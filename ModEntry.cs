using dc;
using dc.en;
using dc.en.inter;
using dc.pr;
using dc.tool;
using dc.libs;
using dc.ui;
using HaxeProxy.Runtime;
using ModCore.Events.Interfaces.Game;
using ModCore.Events.Interfaces.Game.Hero;
using ModCore.Menu;
using ModCore.Mods;
using ModCore.Utilities;
using System.IO;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using DotNetFile = System.IO.File;
using DotNetMath = System.Math;
using DotNetPath = System.IO.Path;
using DotNetType = System.Type;
using Options = dc.ui.Options;

namespace RiftSiege;

// RiftSiege 是一个独立的新 Mod。
// 第一版先实现可测试闭环：
// 1. 每张主地图随机抽取 15-30 的击杀阈值。
// 2. 玩家在普通地图击杀怪物达到阈值后，直接在当前地图启动本地刷怪事件。
// 3. 不生成入口实体或独立地图，避免地图模板和切图逻辑带来的不稳定。
// 4. 事件期间每 0.1 秒刷 1 只随机普通敌人，敌人锁定玩家并尝试进攻。
// 5. 竞技场敌人死亡时，掉落 1 个可拾取的蓝色细胞。
// 6. 同一张地图只触发一次事件，避免重复刷怪。
public sealed class ModEntry(ModInfo info) : ModBase(info),
    IModMenu,
    IOnHeroUpdate,
    IOnHeroInit,
    IOnHeroDispose,
    IOnGameExit
{
    // 每局随机使用同一个 Random，避免同一帧多次 new Random 生成重复随机数。
    private static readonly Random _random = new();

    // 调试日志文件路径，位于 coremod/mods/RiftSiege/moddbg.log。
    private static string? _debugLogPath;

    // 用户配置文件路径，位于 coremod/mods/RiftSiege/config.json。
    private static string? _configPath;

    // 上一次读到的配置文件修改时间，用来避免每帧重复读文件。
    private static DateTime _configLastWriteTimeUtc;

    // 配置热加载计时器。每秒检查一次，避免频繁 IO。
    private static double _configReloadTimer;

    // 总开关。false 时不计数、不触发事件、不刷怪。
    private static bool _enabled = true;

    // 当前正在运行的 pr.Game 实例，用来读取 Boss 细胞数和当前关卡。
    private static Game? _currentGame;

    // 当前主地图的 id。地图切换后会重置击杀计数和本地事件状态。
    private static string? _currentMapId;

    // 本地事件中心点。刷怪优先围绕玩家当前位置，找不到可站立点时回退到这个中心。
    private static CPoint? _arenaCenter;

    // 当前是否处于本地刷怪事件状态。处于事件中时才按计时器刷怪。
    private static bool _inArena;

    // 当前地图的事件触发击杀阈值。每张地图重置时随机为 15-30。
    private static int _entryKillThreshold;

    // 当前地图已累计的普通怪击杀数。达到阈值后启动本地事件。
    private static int _entryKillCount;

    // 本局运行期间已经触发过事件的地图 id。
    // 只要某张主地图成功触发过一次事件，就不会在同一张地图再次触发。
    private static readonly HashSet<string> _mapsWithEntryPortal = [];

    // 记录地图后是否已经写过地图信息日志，避免每帧刷屏。
    private static bool _loggedCurrentMap;

    // 刷怪计时器。事件期间每隔 LocalSpawnIntervalSeconds 秒在玩家附近刷一只敌人。
    private static double _spawnTimer;

    // 本次本地刷怪事件还需要生成多少只敌人。
    private static int _remainingArenaSpawns;

    // 已经由本 Mod 生成、仍需要跟踪死亡奖励的敌人运行时 key。
    private static readonly HashSet<int> _arenaMobKeys = [];

    // 当前还被认为存活的竞技场敌人 key，用于限制场上敌人数量。
    private static readonly HashSet<int> _aliveArenaMobKeys = [];

    // 事件怪对象引用表。
    // 主要用于兜底：如果某些死亡没有走 Hero.onMobDeath，也能在每帧检测 destroyed 后补发细胞掉落。
    private static readonly Dictionary<int, dc.en.Mob> _arenaMobsByKey = [];

    // 当前事件头顶提示。PopText 默认不会按我们的需求自动销毁，所以这里手动计时。
    private static PopText? _eventPopText;

    // 事件头顶提示已经显示的秒数。
    private static double _eventPopTextTimer;

    // 事件头顶提示最终停留的 Y 偏移。
    private static double _eventPopTextTargetY;

    // 本地刷怪间隔：用户要求 0.1 秒出一只。
    private const double LocalSpawnIntervalSeconds = 0.1;

    // 一次事件刷几十只怪。当前恢复为 40 只。
    private const int LocalSpawnTotal = 40;

    // 场上最多跟踪多少只竞技场敌人。超过后暂停刷怪，等玩家清掉再继续。
    private const int MaxAliveArenaMobs = 40;

    // 事件头顶提示显示时长。太长会挡视野，太短又容易错过。
    private const double EventPopTextDurationSeconds = 2.2;

    // 事件头顶提示淡入和上移动画时长。
    private const double EventPopTextIntroSeconds = 0.28;

    // 事件头顶提示从目标位置下方多少像素开始出现。
    private const double EventPopTextIntroYOffset = 28.0;

    // 事件提示使用明亮金色，避免原版默认黑色在暗背景里看不清。
    private const int EventPopTextColor = 0xFFD35A;

    // 配置文件热加载间隔。
    private const double ConfigReloadIntervalSeconds = 1.0;

    // 可以随机刷出的敌人类型。
    // 这些类型都来自已确认存在的原版 Mob 子类，构造签名稳定为 (Level, cx, cy, tierA, tierB)。
    private static readonly string[] _mobTypeNames =
    [
        "dc.en.mob.Zombie",
        "dc.en.mob.Archer",
        "dc.en.mob.Runner",
        "dc.en.mob.Grenader",
        "dc.en.mob.Shield",
        "dc.en.mob.Shielder",
        "dc.en.mob.Defender",
        "dc.en.mob.Hammer",
        "dc.en.mob.Rampager",
        "dc.en.mob.Bomber",
        "dc.en.mob.BatKamikaze",
        "dc.en.mob.FlyZombie",
        "dc.en.mob.Scorpio",
        "dc.en.mob.Lancer",
        "dc.en.mob.PirateChief",
        "dc.en.mob.Merman",
        "dc.en.mob.Demon",
        "dc.en.mob.Golem",
        "dc.en.mob.AxeThrower",
        "dc.en.mob.BoneThrower",
        "dc.en.mob.FatZombie",
        "dc.en.mob.Fugitive",
        "dc.en.mob.Librarian",
        "dc.en.mob.Mage360",
        "dc.en.mob.CastleKnight",
        "dc.en.mob.Duelist",
        "dc.en.mob.Enforcer",
        "dc.en.mob.Blowgunner",
        "dc.en.mob.JavelinSnake",
        "dc.en.mob.Ninja",
        "dc.en.mob.Stomper",
        "dc.en.mob.Spiker",
        "dc.en.mob.Shocker",
        "dc.en.mob.SewerTtcl",
        "dc.en.mob.WormZombie",
    ];

    public override void Initialize()
    {
        // Info.ModRoot 在安装后指向 coremod/mods/RiftSiege。
        // 这里把日志文件固定写到 Mod 安装目录，方便你一边玩一边查看 moddbg.log。
        _debugLogPath = Info.ModRoot?.GetFilePath("moddbg.log");

        // 配置文件也放在 Mod 安装目录，用户可以直接编辑。
        _configPath = Info.ModRoot?.GetFilePath("config.json");

        DebugLog("Initialize");

        // 首次加载时读取配置；如果 config.json 不存在，会自动创建默认启用配置。
        ReloadConfigIfChanged(force: true);

        // 缓存原版 pr.Game 实例，地图加载、细胞数读取都要用它。
        // Hook_Game.init 会在游戏主对象初始化时触发，此时能拿到本局的 Game self。
        Hook_Game.init += Hook_Game_init;

        // Game 销毁时必须释放缓存，否则下一局可能读到上一局的对象。
        Hook_Game.onDispose += Hook_Game_onDispose;

        // 玩家击杀敌人后，原版会调用 Hero.onMobDeath；这里负责计数触发事件，并给事件怪掉落 1 个蓝色细胞。
        Hook_Hero.onMobDeath += Hook_Hero_onMobDeath;

        // 同时写一条 ModCore 自带日志，方便确认 Mod 已加载。
        Logger.Information("RiftSiege initialized.");
    }

    // ModCore 菜单里显示的入口名称。
    public string GetName()
    {
        return "裂缝入侵 / Rift Siege";
    }

    // ModCore 菜单入口下方的小字。
    public string? GetSubText()
    {
        return _enabled
            ? "Enabled / 已启用"
            : "Disabled / 已关闭";
    }

    // 构建 Mod 设置菜单。
    public void BuildMenu(Options options)
    {
        // 设置页面标题。
        options.title.set_text("裂缝入侵 / Rift Siege".AsHaxeString());

        // 创建一个滚动容器；即使现在只有一个按钮，后续加更多设置也不用改结构。
        options.createScroller(1);

        // 当前设置项要加到滚动容器里。
        var flow = options.scrollerFlow;

        // 状态文字每次进入菜单都会刷新。
        var stateText = _enabled
            ? "当前：已启用。点击后关闭事件。 / Current: Enabled. Click to disable."
            : "当前：已关闭。点击后启用事件。 / Current: Disabled. Click to enable.";

        // 用简单按钮做开关：点击后写入 config.json，并立即生效。
        options.addSimpleWidget("启用裂缝入侵 / Enable Rift Siege".AsHaxeString(), stateText.AsHaxeString(), () =>
        {
            SetEnabled(!_enabled, "menu toggle");
            SaveConfig();
        }, Ref<int>.In(5), flow);

        // 给用户一个配置文件位置提示，方便不开菜单时手动改。
        options.addSimpleWidget("配置文件 / Config File".AsHaxeString(), SafeToString(_configPath).AsHaxeString(), () => { }, Ref<int>.In(0), flow);
    }

    // 原版 Game.init 的 Hook：缓存 Game 实例，然后继续执行原版 init。
    private static void Hook_Game_init(Hook_Game.orig_init orig, Game self)
    {
        // 缓存 self，后续 GetBossCells 和 HUD fallback 都会从这里取数据。
        _currentGame = self;
        DebugLog("Captured dc.pr.Game instance.");

        // 必须调用 orig，否则原版游戏初始化会被打断。
        orig(self);
    }

    // 原版 Game.onDispose 的 Hook：如果销毁的是当前缓存的 Game，就清空本 Mod 状态。
    private static void Hook_Game_onDispose(Hook_Game.orig_onDispose orig, Game self)
    {
        // 只清理当前记录的 Game，避免误清理其他生命周期对象。
        if (ReferenceEquals(_currentGame, self))
        {
            // Game 已经结束，缓存对象不能继续使用。
            _currentGame = null;

            // 顺手清空当前地图的事件状态，避免残留到下一局。
            ResetCurrentLevelState("game disposed");
        }

        // 必须放行原版 dispose，让游戏自己释放资源。
        orig(self);
    }

    // 游戏退出回调：清空本局所有已触发地图记录。
    void IOnGameExit.OnGameExit()
    {
        // 清理当前地图状态，比如正在显示的事件文字、刷怪计时器等。
        ResetCurrentLevelState("game exit");

        // 游戏退出后下一次进入应该重新允许每张地图触发事件。
        _mapsWithEntryPortal.Clear();
    }

    // 玩家初始化回调：开局或复活时重置事件记录。
    void IOnHeroInit.OnHeroInit()
    {
        // 复活后视为新的一轮测试，允许地图重新触发事件。
        _mapsWithEntryPortal.Clear();

        // 清理上一具角色遗留的事件状态。
        ResetCurrentLevelState("hero init / respawn");
        DebugLog("Hero initialized: cleared triggered maps so respawn can trigger local arena again.");
    }

    // 玩家销毁回调：死亡或切换生命周期时清理状态。
    void IOnHeroDispose.OnHeroDispose()
    {
        // 玩家死亡后，旧角色身上的状态不能带到新角色。
        _mapsWithEntryPortal.Clear();

        // 清掉当前事件，避免复活后还继续刷旧事件的怪。
        ResetCurrentLevelState("hero dispose / death");
        DebugLog("Hero disposed: cleared triggered maps so next hero can trigger local arena again.");
    }

    // 玩家每帧更新回调：这是本 Mod 的主循环入口。
    void IOnHeroUpdate.OnHeroUpdate(double dt)
    {
        // 每秒热加载一次配置文件，支持游戏运行时改 config.json。
        _configReloadTimer -= dt;
        if (_configReloadTimer <= 0)
        {
            _configReloadTimer = ConfigReloadIntervalSeconds;
            ReloadConfigIfChanged(force: false);
        }

        // 关闭时完全绕过功能；如果关闭前正在事件中，先重置本 Mod 状态。
        if (!_enabled)
        {
            if (_inArena || _entryKillCount > 0 || _arenaMobKeys.Count > 0)
            {
                ResetCurrentLevelState("disabled");
            }

            return;
        }

        // 从 ModCore 拿当前玩家实例；主菜单、加载中等阶段可能为空。
        var hero = ModCore.Modules.Game.Instance.HeroInstance;
        if (hero == null) return;

        // 玩家所在关卡或地图还没准备好时，不能读碰撞和实体列表。
        var level = hero._level;
        if (level?.map == null) return;

        // 每帧检查是否换图；换图时重置击杀阈值和事件状态。
        RefreshLevelStateIfNeeded(hero, level);

        // 事件提示文字需要逐帧更新透明度和 Y 轴位置。
        UpdateEventPopText(dt);

        // 兜底检查事件怪是否已经被销毁但没有触发 Hero.onMobDeath。
        // 有些怪可能被陷阱、环境、特殊状态或非玩家直接伤害杀死，这时 Hero.onMobDeath 不一定会被调用。
        CheckArenaMobFallbackDeaths(hero);

        // 只有事件已触发时才进入刷怪逻辑，平时只做轻量检查。
        if (_inArena)
        {
            UpdateArena(hero, level, dt);
        }
    }

    // 地图变化时清理上一张地图的击杀计数和刷怪状态。
    private static void RefreshLevelStateIfNeeded(Hero hero, Level level)
    {
        // 地图 id 是判断是否换图的主依据。
        var mapId = SafeToString(level.map.id);

        // 地图没变就什么都不做，避免每帧重置状态。
        if (_currentMapId == mapId) return;

        // 地图变化后，上一张地图的计数、刷怪和提示文字都不再有效。
        ResetCurrentLevelState($"level changed: {_currentMapId ?? "null"} -> {mapId}");

        // 记录新地图 id，后续击杀计数会绑定到这张地图。
        _currentMapId = mapId;

        // 每张地图只打印一次基础信息，主要用于确认当前阈值是否随机正确。
        if (!_loggedCurrentMap)
        {
            _loggedCurrentMap = true;
            DebugLog($"Level detected: map={mapId}, size={level.map.wid}x{level.map.hei}, hero=({hero.cx},{hero.cy}), eventKillThreshold={_entryKillThreshold}");
        }
    }

    // 在普通地图怪物死亡位置附近直接启动本地刷怪事件。
    private static void TryStartLocalArenaEventAtMobDeath(Hero hero, dc.en.Mob mob)
    {
        // 事件发生在玩家当前地图；如果地图还没准备好，直接跳过。
        var level = hero._level;
        if (level?.map == null) return;

        // 没有当前地图 id 时无法记录“本地图已触发”，所以跳过。
        if (string.IsNullOrWhiteSpace(_currentMapId)) return;

        // 同一张地图只触发一次，防止刷怪事件在一关内重复出现。
        if (_mapsWithEntryPortal.Contains(_currentMapId))
        {
            DebugLog($"Local arena skipped: map already triggered event, map={_currentMapId}.");
            return;
        }

        // 用最后一只触发阈值的怪物死亡坐标作为事件中心候选。
        var deathCx = mob.cx;
        var deathCy = mob.cy;

        // 怪的死亡格如果能站人并且不覆盖交互物，就直接用死亡点。
        // 否则在死亡点周围找最近的可站立格，保证刷怪中心不会卡进墙里。
        if (!TryFindNearbyWalkablePoint(level, deathCx, deathCy, out var point))
        {
            DebugLog($"Local arena skipped: no walkable point near mob death, mob=({deathCx},{deathCy}).");
            return;
        }

        // 先标记本地图已触发，避免后续逻辑或同帧回调重复启动。
        _mapsWithEntryPortal.Add(_currentMapId);

        // 真正启动刷怪事件。
        StartLocalArenaEvent(hero, point);

        // 给玩家显示“事件出现”的头顶提示。
        ShowLocalizedEventText();

        // 记录完整坐标和击杀进度，方便你看日志判断是否符合预期。
        DebugLog($"Local arena started after kills: map={_currentMapId}, kills={_entryKillCount}/{_entryKillThreshold}, mobDeath=({deathCx},{deathCy}), center=({point.cx},{point.cy}), hero=({hero.cx},{hero.cy})");
    }

    // 初始化一次本地刷怪事件的运行时状态。
    private static void StartLocalArenaEvent(Hero hero, CPoint center)
    {
        // 打开事件开关，OnHeroUpdate 后续每帧会调用 UpdateArena。
        _inArena = true;

        // 保存事件中心；如果玩家附近找不到刷怪点，会回退到这个中心附近。
        _arenaCenter = center;

        // 计时器清零，让事件启动后尽快刷出第一只怪。
        _spawnTimer = 0.0;

        // 本次事件总刷怪数量。
        _remainingArenaSpawns = LocalSpawnTotal;

        // 清空旧的敌人追踪集合，避免上一轮事件的怪影响本轮掉落判断。
        _arenaMobKeys.Clear();
        _aliveArenaMobKeys.Clear();
        _arenaMobsByKey.Clear();

        DebugLog($"Local arena event armed: map={SafeToString(hero._level?.map?.id)}, center=({center.cx},{center.cy}), total={LocalSpawnTotal}, interval={LocalSpawnIntervalSeconds}, bossCells={GetBossCells()}");
    }

    // 竞技场每帧更新：定时刷怪。
    private static void UpdateArena(Hero hero, Level level, double dt)
    {
        // 没有中心点说明事件状态不完整，直接跳过，避免空引用。
        if (_arenaCenter == null) return;

        // 需要生成的怪已经刷完后，关闭事件；已生成怪的死亡奖励仍由 Hook 追踪。
        if (_remainingArenaSpawns <= 0)
        {
            _inArena = false;
            _arenaCenter = null;
            _spawnTimer = 0;
            DebugLog($"Local arena event completed spawning: tracked={_arenaMobKeys.Count}, alive={_aliveArenaMobKeys.Count}");
            return;
        }

        // dt 是上一帧到这一帧的秒数；倒计时到 0 才刷下一只。
        _spawnTimer -= dt;
        if (_spawnTimer > 0) return;

        // 场上怪太多时暂停刷怪，避免瞬间堆满导致卡顿或围死玩家。
        if (_aliveArenaMobKeys.Count >= MaxAliveArenaMobs)
        {
            _spawnTimer = LocalSpawnIntervalSeconds;
            DebugLog($"Arena spawn skipped: alive={_aliveArenaMobKeys.Count}, limit={MaxAliveArenaMobs}");
            return;
        }

        // 优先在玩家附近随机偏移一块区域刷怪，保证事件压迫感。
        var preferredCx = hero.cx + _random.Next(-12, 13);
        var preferredCy = hero.cy + _random.Next(-3, 4);

        // 如果玩家附近找不到合法落点，再回退到事件中心附近。
        var spawned = TrySpawnArenaMobNear(level, hero, preferredCx, preferredCy, "near-hero")
            || TrySpawnArenaMobNear(level, hero, _arenaCenter.cx, _arenaCenter.cy, "event-center");

        // 只有真的刷出来才扣数量；刷失败则下次计时继续尝试。
        if (spawned)
        {
            _remainingArenaSpawns--;
        }

        // 无论成功失败，都等 0.1 秒再试，避免同一帧死循环刷屏。
        _spawnTimer = LocalSpawnIntervalSeconds;
        DebugLog($"Local arena spawn progress: remaining={_remainingArenaSpawns}, alive={_aliveArenaMobKeys.Count}");
    }

    // 在期望坐标附近找一个可站立格再刷怪，避免把怪刷进墙里或刷到玩家看不到的断层。
    private static bool TrySpawnArenaMobNear(Level level, Hero hero, int preferredCx, int preferredCy, string side)
    {
        // 先把期望坐标修正到附近可站立位置。
        if (!TryFindNearbyWalkablePoint(level, preferredCx, preferredCy, out var point))
        {
            DebugLog($"Arena spawn skipped: side={side}, no walkable point near=({preferredCx},{preferredCy})");
            return false;
        }

        // 找到合法点后再真正创建敌人。
        return SpawnArenaMob(level, hero, point.cx, point.cy);
    }

    // 在指定坐标刷一只随机普通敌人，并把它的生命值翻倍。
    private static bool SpawnArenaMob(Level level, Hero hero, int cx, int cy)
    {
        // 随机一个起始下标，然后顺序尝试整个怪物列表。
        // 这样既随机，又能在某个类型构造失败时自动尝试下一个类型。
        var firstIndex = _random.Next(_mobTypeNames.Length);

        for (var attempt = 0; attempt < _mobTypeNames.Length; attempt++)
        {
            // 通过取模绕回数组开头，确保最多尝试所有怪物类型一次。
            var typeName = _mobTypeNames[(firstIndex + attempt) % _mobTypeNames.Length];

            try
            {
                // GameProxy 是 Dead Cells 代理程序集，原版怪物类型都从这里反射获取。
                var mobType = DotNetType.GetType(typeName + ", GameProxy");
                if (mobType == null)
                {
                    DebugLog($"Spawn mob candidate skipped: type not found: {typeName}");
                    continue;
                }

                // 大多数普通怪构造函数是 (Level, cx, cy, tierA, tierB)。
                // tier 取当前 Boss 细胞，尽量贴近“当前难度的血量”，随后再把 maxLife/life 乘 2。
                var bossCells = GetBossCells();

                // 用反射调用怪物构造函数，避免为每种怪物写一套 new 代码。
                var mob = Activator.CreateInstance(mobType, level, cx, cy, bossCells, bossCells) as dc.en.Mob;
                if (mob == null)
                {
                    DebugLog($"Spawn mob candidate skipped: constructor returned null: {typeName}");
                    continue;
                }

                // init 会把怪加入关卡实体系统，并让原版完成属性初始化。
                mob.init();

                // 初始化后原版已经按难度计算完血量，这里再翻倍。
                var originalMaxLife = mob.maxLife;

                // 至少保底 1 点最大生命，避免某些特殊怪初始血量异常导致 0 血。
                var doubledMaxLife = DotNetMath.Max(1, originalMaxLife * 2);
                mob.maxLife = doubledMaxLife;
                mob.life = doubledMaxLife;
                mob.oldLife = doubledMaxLife;

                // 主动给玩家威胁值，促使敌人朝玩家进攻。
                var threat = 9999.0;

                // addThreat 使用 Ref<double>，这里传一个很高的威胁值，让怪优先仇恨玩家。
                mob.addThreat(hero, 9999.0, new Ref<double>(ref threat));

                // NemesisTarget 是更强的锁定目标提示，配合威胁值提升追击稳定性。
                mob.setNemesisTarget(hero);

                // RuntimeHelpers.GetHashCode 获取对象身份哈希，不受怪物自身 Equals 实现影响。
                var key = RuntimeHelpers.GetHashCode(mob);

                // _arenaMobKeys 用于死亡时识别“这是本 Mod 生成的怪，需要掉细胞”。
                _arenaMobKeys.Add(key);

                // _aliveArenaMobKeys 用于限制同屏存活怪数量。
                _aliveArenaMobKeys.Add(key);

                // 保存对象引用，用于 Hero.onMobDeath 漏掉时做 destroyed 兜底检测。
                _arenaMobsByKey[key] = mob;

                DebugLog($"Arena mob spawned: type={typeName}, pos=({cx},{cy}), bossCells={bossCells}, life={originalMaxLife}->{doubledMaxLife}, attempt={attempt + 1}");
                return true;
            }
            catch (Exception ex)
            {
                DebugLog($"Spawn mob candidate failed: type={typeName}, pos=({cx},{cy}), attempt={attempt + 1}, {ex.GetType().Name}: {ex.Message}");
            }
        }

        DebugLog($"Spawn mob failed: no valid candidate at pos=({cx},{cy})");
        return false;
    }

    // 玩家击杀本 Mod 生成的事件敌人时，掉落 1 个可拾取的蓝色细胞。
    private static void Hook_Hero_onMobDeath(Hook_Hero.orig_onMobDeath orig, Hero self, dc.en.Mob mob)
    {
        // 先执行原版死亡逻辑，保证经验、金币、原版掉落等流程不被破坏。
        orig(self, mob);

        // 用对象身份哈希判断死亡的是不是本 Mod 刚才生成并登记过的事件怪。
        var key = RuntimeHelpers.GetHashCode(mob);
        if (!_arenaMobKeys.Remove(key))
        {
            // 不是事件怪，就当作普通击杀，用来累计事件触发阈值。
            CountNormalMobKillForEntry(self, mob);
            return;
        }

        // 是事件怪：从存活集合移除，避免场上数量限制永远不下降。
        _aliveArenaMobKeys.Remove(key);
        _arenaMobsByKey.Remove(key);
        DebugLog($"Arena mob death tracked: mob={SafeToString(mob.type)}, remainingTracked={_arenaMobKeys.Count}, alive={_aliveArenaMobKeys.Count}");

        // 按需求让事件怪掉落一个可拾取的蓝色细胞。
        DropArenaCellReward(self, mob);
    }

    // 兜底死亡检测：处理没有触发 Hero.onMobDeath 的事件怪。
    private static void CheckArenaMobFallbackDeaths(Hero hero)
    {
        // 没有追踪对象时直接返回，避免每帧做无意义遍历。
        if (_arenaMobsByKey.Count == 0) return;

        // 先收集需要处理的 key，避免遍历 Dictionary 时直接修改集合。
        List<int>? destroyedKeys = null;

        foreach (var (key, mob) in _arenaMobsByKey)
        {
            try
            {
                // destroyed 为 true 说明实体已经被游戏销毁。
                // 如果它还留在我们的追踪表里，就代表 Hero.onMobDeath 没有处理到它。
                if (!mob.destroyed) continue;

                destroyedKeys ??= [];
                destroyedKeys.Add(key);
            }
            catch (Exception ex)
            {
                // 读取 destroyed 本身失败时也移除追踪，避免坏引用每帧刷异常。
                destroyedKeys ??= [];
                destroyedKeys.Add(key);
                DebugLog($"Arena mob fallback check failed: key={key}, {ex.GetType().Name}: {ex.Message}");
            }
        }

        // 没有漏网死亡对象就结束。
        if (destroyedKeys == null) return;

        foreach (var key in destroyedKeys)
        {
            // TryGetValue 失败说明它可能刚被其他路径移除，跳过即可。
            if (!_arenaMobsByKey.TryGetValue(key, out var mob)) continue;

            // 从所有追踪集合移除，保证不会重复掉落。
            _arenaMobsByKey.Remove(key);
            _arenaMobKeys.Remove(key);
            _aliveArenaMobKeys.Remove(key);

            DebugLog($"Arena mob fallback death tracked: mob={SafeToString(mob.type)}, remainingTracked={_arenaMobKeys.Count}, alive={_aliveArenaMobKeys.Count}");

            // 即使不是 Hero.onMobDeath 路径，也按事件怪死亡处理细胞掉落。
            DropArenaCellReward(hero, mob);
        }
    }

    // 统计普通地图击杀数，达到本地图随机阈值后触发本地刷怪事件。
    private static void CountNormalMobKillForEntry(Hero hero, dc.en.Mob mob)
    {
        // 正在事件中、地图状态还没准备好、或者本地图已经触发过时，不继续累计。
        if (_inArena || string.IsNullOrWhiteSpace(_currentMapId)) return;
        if (_mapsWithEntryPortal.Contains(_currentMapId)) return;

        // 秘密房和子关卡容易有特殊规则，避免在这些地方启动本地事件。
        if (IsSecretOrSubLevel(hero._level)) return;

        // 只统计玩家当前关卡里的怪，避免特殊回调或召唤物死亡污染计数。
        if (!ReferenceEquals(hero._level, mob._level)) return;

        // 普通有效击杀数 +1。
        _entryKillCount++;
        DebugLog($"Entry kill progress: {_entryKillCount}/{_entryKillThreshold}, mob={SafeToString(mob.type)}, death=({mob.cx},{mob.cy})");

        // 没达到本地图随机阈值时只记录进度，不触发事件。
        if (_entryKillCount < _entryKillThreshold) return;

        // 达到阈值后，在这只怪死亡位置附近启动事件。
        TryStartLocalArenaEventAtMobDeath(hero, mob);
    }

    // 秘密子关卡不应该触发本地事件，避免打断原版特殊房间逻辑。
    private static bool IsSecretOrSubLevel(Level? level)
    {
        try
        {
            // level 为空时没法判断，按“不是特殊关卡”处理，让外层其他空值保护负责拦截。
            if (level == null) return false;

            // 原版秘密房或子关卡不参与事件触发。
            return level.isSecret || level.isSubLevel;
        }
        catch
        {
            // 读取关卡标记失败时保守返回 false，避免误伤正常地图。
            return false;
        }
    }

    // 随机找一个当前地图内相对安全、可站立的格子。
    private static bool TryFindWalkablePoint(Level level, int avoidCx, int avoidCy, int minDistance, out CPoint point)
    {
        // 取出地图对象和尺寸，后续随机坐标必须限制在地图边界内。
        var map = level.map;
        var width = DotNetMath.Max(1, map.wid);
        var height = DotNetMath.Max(1, map.hei);

        // 随机尝试 240 次，既足够覆盖大地图，又不会在坏地图上卡住。
        for (var attempt = 0; attempt < 240; attempt++)
        {
            // 避开地图最边缘，减少刷到墙体、门外或越界区域的概率。
            var cx = _random.Next(3, DotNetMath.Max(4, width - 3));
            var cy = _random.Next(5, DotNetMath.Max(6, height - 5));

            // 如果要求远离某个点，就用曼哈顿距离过滤太近的位置。
            if (DotNetMath.Abs(cx - avoidCx) + DotNetMath.Abs(cy - avoidCy) < minDistance) continue;

            // 必须是可站立格子：身体无碰撞，脚下有地。
            if (!IsWalkable(level, cx, cy)) continue;

            // 不要贴着 NPC、门、宝箱等交互物刷。
            if (IsNearExistingInteractive(level, cx, cy, 4)) continue;

            // 找到合适点后通过 out 参数返回。
            point = new CPoint(cx, cy);
            return true;
        }

        // 找不到时返回避让点本身，bool=false 告诉调用者不要直接使用。
        point = new CPoint(avoidCx, avoidCy);
        return false;
    }

    // 从指定中心点向外扩散查找可站立格子，适合“怪物死亡点附近启动事件”的场景。
    private static bool TryFindNearbyWalkablePoint(Level level, int centerCx, int centerCy, out CPoint point)
    {
        // 从中心向外一圈圈扩散，优先选择离原坐标最近的可站立位置。
        for (var radius = 0; radius <= 8; radius++)
        {
            // dx/dy 遍历当前半径包围盒。
            for (var dx = -radius; dx <= radius; dx++)
            {
                for (var dy = -radius; dy <= radius; dy++)
                {
                    // 只检查当前圈的边缘，避免重复检查内部点。
                    if (DotNetMath.Abs(dx) != radius && DotNetMath.Abs(dy) != radius) continue;

                    // 把相对偏移转换成地图格坐标。
                    var cx = centerCx + dx;
                    var cy = centerCy + dy;

                    // 不可站立就跳过。
                    if (!IsWalkable(level, cx, cy)) continue;

                    // 太靠近交互物也跳过，防止影响原版交互。
                    if (IsNearExistingInteractive(level, cx, cy, 3)) continue;

                    // 找到最近的合法点。
                    point = new CPoint(cx, cy);
                    return true;
                }
            }
        }

        // 8 格范围内都没找到，返回原点并报告失败。
        point = new CPoint(centerCx, centerCy);
        return false;
    }

    // 判定一个格子是否适合站立：
    // 脚下有地面，身体区域没有实体碰撞。
    private static bool IsWalkable(Level level, int cx, int cy)
    {
        try
        {
            // 拿地图用于碰撞检测。
            var map = level.map;

            // 边界附近不安全，避免 checkCollRect 访问越界或刷到地图外。
            if (cx <= 1 || cy <= 1 || cx >= map.wid - 2 || cy >= map.hei - 2) return false;

            // checkCollRect(x, y, w, h, includeOneWay) 为 true 表示区域有碰撞。
            // 身体占用脚上两格；这里要求身体区域没有墙。
            var bodyBlocked = map.checkCollRect(cx, cy - 2, 1, 2, true);

            // 脚下一格必须有碰撞，代表这里有地板可以站。
            var groundBlocked = map.checkCollRect(cx, cy + 1, 1, 1, true);

            // 只有“身体不堵 + 脚下有地”才算可站立。
            return !bodyBlocked && groundBlocked;
        }
        catch
        {
            // 碰撞查询失败就认为不可站立，宁可不刷，也不刷进异常位置。
            return false;
        }
    }

    // 避免刷怪中心贴着已有交互物。这里扫描当前关卡实体列表里的 Interactive。
    private static bool IsNearExistingInteractive(Level level, int cx, int cy, int radius)
    {
        try
        {
            // 原版关卡实体列表里包含怪物、交互物、特效等对象。
            var entities = level.entities;
            if (entities == null) return false;

            // 遍历所有实体，筛选 Interactive 类型。
            for (var i = 0; i < entities.length; i++)
            {
                // 不是交互物就跳过。
                if (entities.getDyn(i) is not Interactive interactive) continue;

                // 交互物在目标点半径内，说明这里不适合作为事件中心或刷怪点。
                if (DotNetMath.Abs(interactive.cx - cx) <= radius && DotNetMath.Abs(interactive.cy - cy) <= radius)
                {
                    return true;
                }
            }
        }
        catch
        {
            // 扫描失败时保守认为“不安全”，避免盖住已有交互物。
            return true;
        }

        return false;
    }

    // 读取当前 Boss 细胞数。优先读 pr.Game.user.bossRuneActivated。
    private static int GetBossCells()
    {
        try
        {
            // bossRuneActivated 就是当前 Boss 细胞难度；Clamp 防止异常值越界。
            return DotNetMath.Clamp(_currentGame?.user?.bossRuneActivated ?? 0, 0, 5);
        }
        catch
        {
            // 读取失败时按 0 细胞处理，保证 Mod 不会因为难度读取失败闪退。
            return 0;
        }
    }

    // 设置启用状态，并在关闭时清理当前事件状态。
    private static void SetEnabled(bool enabled, string reason)
    {
        // 状态没变时只写一条轻量日志。
        if (_enabled == enabled)
        {
            DebugLog($"Enabled unchanged: enabled={_enabled}, reason={reason}");
            return;
        }

        // 更新内存状态。
        _enabled = enabled;
        DebugLog($"Enabled changed: enabled={_enabled}, reason={reason}");

        // 关闭功能时，立刻停止本 Mod 的计数和刷怪。
        if (!_enabled)
        {
            ResetCurrentLevelState($"disabled by {reason}");
        }
    }

    // 读取 config.json；文件变化后自动应用。
    private static void ReloadConfigIfChanged(bool force)
    {
        try
        {
            if (string.IsNullOrWhiteSpace(_configPath))
            {
                return;
            }

            // 没有配置文件时创建默认配置，避免用户不知道该怎么写。
            if (!DotNetFile.Exists(_configPath))
            {
                SaveConfig();
                _configLastWriteTimeUtc = DotNetFile.GetLastWriteTimeUtc(_configPath);
                DebugLog("Config not found; created default config.");
                return;
            }

            // 文件没变化且不是强制加载时，不重复解析。
            var lastWriteTimeUtc = DotNetFile.GetLastWriteTimeUtc(_configPath);
            if (!force && lastWriteTimeUtc == _configLastWriteTimeUtc) return;

            // 读取并反序列化配置。
            var json = DotNetFile.ReadAllText(_configPath);
            var config = JsonSerializer.Deserialize<RiftSiegeConfig>(json);
            if (config == null)
            {
                DebugLog("Config reload skipped: deserialized config is null.");
                return;
            }

            // 应用启用状态。
            SetEnabled(config.Enabled, "config reload");
            _configLastWriteTimeUtc = lastWriteTimeUtc;
            DebugLog($"Config loaded: Enabled={_enabled}");
        }
        catch (Exception ex)
        {
            // 配置读取失败不影响游戏，继续使用当前内存里的状态。
            DebugLog($"Config reload failed: {ex.GetType().Name}: {ex.Message}");
        }
    }

    // 保存当前配置到 config.json。
    private static void SaveConfig()
    {
        try
        {
            if (string.IsNullOrWhiteSpace(_configPath))
            {
                return;
            }

            // 确保配置目录存在。
            Directory.CreateDirectory(DotNetPath.GetDirectoryName(_configPath)!);

            // 只暴露一个参数：Enabled，后续要加更多设置可以继续扩展这个类。
            var config = new RiftSiegeConfig
            {
                Enabled = _enabled,
            };

            var json = JsonSerializer.Serialize(config, new JsonSerializerOptions
            {
                WriteIndented = true,
            });

            DotNetFile.WriteAllText(_configPath, json);
            _configLastWriteTimeUtc = DotNetFile.GetLastWriteTimeUtc(_configPath);
            DebugLog($"Config saved: Enabled={_enabled}");
        }
        catch (Exception ex)
        {
            // 保存失败只写日志，避免菜单点击导致游戏崩溃。
            DebugLog($"Config save failed: {ex.GetType().Name}: {ex.Message}");
        }
    }

    // 重置“当前地图级别”的运行状态；换图、死亡、退出都会调用。
    private static void ResetCurrentLevelState(string reason)
    {
        // 关闭事件刷怪开关。
        _inArena = false;

        // 清空当前地图 id，下一帧 RefreshLevelStateIfNeeded 会重新记录。
        _currentMapId = null;

        // 为下一张地图重新随机一个 15-30 的触发阈值。
        _entryKillThreshold = _random.Next(15, 31);

        // 清空本地图击杀计数。
        _entryKillCount = 0;

        // 允许下一张地图重新打印一次基础日志。
        _loggedCurrentMap = false;

        // 清空事件中心。
        _arenaCenter = null;

        // 清空刷怪计时器和剩余刷怪数量。
        _spawnTimer = 0;
        _remainingArenaSpawns = 0;

        // 清空事件怪追踪；换图后旧怪不再由本事件管理。
        _arenaMobKeys.Clear();
        _aliveArenaMobKeys.Clear();
        _arenaMobsByKey.Clear();

        // 清掉还挂在玩家头顶的事件文字。
        ClearEventPopText();

        DebugLog($"Level state reset: reason={reason}");
    }

    // 安全转字符串：日志里经常打印 Haxe/代理对象，ToString 可能抛异常。
    private static string SafeToString(object? value)
    {
        try
        {
            // 正常情况下直接调用 ToString，null 统一打印为 "null"。
            return value?.ToString() ?? "null";
        }
        catch
        {
            // 某些代理对象 ToString 失败时，仍然保证日志写入不影响游戏。
            return "unknown";
        }
    }

    // 根据游戏语言返回事件提示文本。
    private static string GetLocalizedEventText()
    {
        // 默认先给空字符串，读取失败时会走英文 fallback。
        var language = string.Empty;

        try
        {
            // Lang.Class.LANG 是原版当前语言标识。
            language = SafeToString(Lang.Class.LANG);
        }
        catch
        {
            // 读取语言失败时走英文，避免本地化探测影响游戏运行。
        }

        // 统一小写后做宽松匹配，兼容 zh、schinese、tchinese、cn 等命名。
        var lower = language.ToLowerInvariant();

        // 中文环境显示中文，否则显示英文。
        return lower.Contains("zh")
            || lower.Contains("chinese")
            || lower.Contains("schinese")
            || lower.Contains("tchinese")
            || lower.Contains("cn")
            ? "裂隙围攻事件出现"
            : "Rift Siege event appeared";
    }

    // 显示事件出现提示：优先玩家头顶 PopText，失败后尝试 HUD 方法。
    private static void ShowLocalizedEventText()
    {
        // 先拿本地化后的文本。
        var text = GetLocalizedEventText();
        DebugLog($"Event text requested: {text}");

        // 优先显示在玩家头顶，因为这是你明确要求的表现方式。
        var hero = ModCore.Modules.Game.Instance.HeroInstance;
        if (hero != null && TryShowHeroPopText(hero, text))
        {
            return;
        }

        try
        {
            // 如果玩家对象不可用或 PopText 创建失败，尝试走 HUD 兜底。
            var hud = _currentGame?.hud;
            if (hud == null)
            {
                DebugLog("Event text display skipped: hud=null");
                return;
            }

            // 由于代理 API 没有稳定文档，这里用反射试几个常见 HUD 文本方法名。
            if (TryInvokeTextMethod(hud, text,
                    "announce",
                    "notify",
                    "message",
                    "showMessage",
                    "showNotification",
                    "showInfo",
                    "showText",
                    "print",
                    "addText"))
            {
                return;
            }

            DebugLog($"Event text display method not found: hudType={hud.GetType().FullName}");
        }
        catch (Exception ex)
        {
            // 提示文字失败不应该影响刷怪事件本身。
            DebugLog($"Event text display failed: {ex.GetType().Name}: {ex.Message}");
        }
    }

    // 在玩家头顶创建 PopText，并把它交给 UpdateEventPopText 做动画和销毁。
    private static bool TryShowHeroPopText(Hero hero, string text)
    {
        try
        {
            // 先销毁旧提示，避免多个事件文字叠在一起。
            ClearEventPopText();

            // PopText 是原版的浮动文字进程。第一个参数绑定实体，所以这里绑定 Hero，
            // 文字会从玩家头顶附近弹出，而不是固定在屏幕 HUD 上。
            var popText = new PopText(hero, text.AsHaxeString(), EventPopTextColor, 0, true);

            // init 后 PopText 内部文本对象和初始坐标才会准备好。
            popText.init();

            // 原版 startIGY 偏低，这里上移到玩家头顶附近作为最终位置。
            _eventPopTextTargetY = popText.startIGY - 92;

            // 初始位置在最终位置下方，后续 UpdateEventPopText 会向上移动到目标点。
            popText.startIGY = _eventPopTextTargetY + EventPopTextIntroYOffset;

            // X 轴暂不偏移，保留这行是为了说明可调位置在这里。
            popText.startIGX += 0;

            try
            {
                // 设置明亮金色，提高暗色地图上的可读性。
                popText.text.textColor = EventPopTextColor;

                // 初始透明度为 0，做淡入动画。
                popText.text.alpha = 0.0;

                // 稍微放大，确保战斗中能看清。
                popText.text.customScale = 1.25;

                // 限制最大宽度，避免长文本横向过宽。
                popText.text.maxWidth = 420.0;
            }
            catch (Exception styleEx)
            {
                // 样式设置失败时仍然保留 PopText，最多只是表现差一点。
                DebugLog($"Hero PopText style failed: {styleEx.GetType().Name}: {styleEx.Message}");
            }

            // 保存 PopText 引用，后续每帧更新动画。
            _eventPopText = popText;

            // 从 0 秒开始计时。
            _eventPopTextTimer = 0.0;
            DebugLog($"Event text displayed above hero through PopText: hero=({hero.cx},{hero.cy}), text={text}");
            return true;
        }
        catch (Exception ex)
        {
            // 创建失败时返回 false，让 ShowLocalizedEventText 尝试 HUD fallback。
            DebugLog($"Hero PopText display failed: {ex.GetType().Name}: {ex.Message}");
            return false;
        }
    }

    // 每帧更新事件提示文字的位置、透明度和生命周期。
    private static void UpdateEventPopText(double dt)
    {
        // 没有正在显示的提示文字就不用做任何事。
        if (_eventPopText == null) return;

        // 累计显示时间，所有动画都基于这个计时器计算。
        _eventPopTextTimer += dt;

        try
        {
            // 如果 PopText 已经被原版或其他流程销毁，就清空引用。
            if (_eventPopText.destroyed)
            {
                _eventPopText = null;
                _eventPopTextTimer = 0;
                return;
            }

            // alpha 分三段：
            // 1. 前 0.22 秒从 0 淡入到 1。
            // 2. 中间保持完全可见。
            // 3. 最后 0.45 秒从 1 淡出到 0。
            var alpha = _eventPopTextTimer < 0.22
                ? _eventPopTextTimer / 0.22
                : _eventPopTextTimer > EventPopTextDurationSeconds - 0.45
                    ? DotNetMath.Max(0.0, (EventPopTextDurationSeconds - _eventPopTextTimer) / 0.45)
                    : 1.0;

            // introProgress 表示从下往上移动的进度，限制在 0-1。
            var introProgress = DotNetMath.Clamp(_eventPopTextTimer / EventPopTextIntroSeconds, 0.0, 1.0);

            // 三次缓动：开始快、结束慢，看起来比线性移动更自然。
            var easedProgress = 1.0 - DotNetMath.Pow(1.0 - introProgress, 3.0);

            // 应用透明度。
            _eventPopText.text.alpha = alpha;

            // 从“目标位置下方 EventPopTextIntroYOffset”移动到目标位置。
            _eventPopText.startIGY = _eventPopTextTargetY + EventPopTextIntroYOffset * (1.0 - easedProgress);

            // 显示时间结束后主动销毁，避免文字一直留在人物身上。
            if (_eventPopTextTimer >= EventPopTextDurationSeconds)
            {
                ClearEventPopText();
            }
        }
        catch (Exception ex)
        {
            // 动画更新失败时清理文字，避免坏对象每帧继续报错。
            DebugLog($"Event PopText update failed: {ex.GetType().Name}: {ex.Message}");
            ClearEventPopText();
        }
    }

    // 销毁当前事件提示文字，并重置相关计时字段。
    private static void ClearEventPopText()
    {
        // 没有提示文字时直接返回。
        if (_eventPopText == null) return;

        try
        {
            // 只有未销毁的 PopText 才需要调用 destroy。
            if (!_eventPopText.destroyed)
            {
                _eventPopText.destroy();
            }
        }
        catch (Exception ex)
        {
            // 销毁失败只写日志，不影响游戏逻辑。
            DebugLog($"Event PopText destroy failed: {ex.GetType().Name}: {ex.Message}");
        }

        // 清空引用和动画状态。
        _eventPopText = null;
        _eventPopTextTimer = 0;
        _eventPopTextTargetY = 0;
    }

    // 给事件怪死亡位置创建细胞掉落。
    private static void DropArenaCellReward(Hero hero, dc.en.Mob mob)
    {
        // 优先使用怪物自己的关卡；如果为空，再退回玩家当前关卡。
        var level = mob._level ?? hero._level;

        // 掉落坐标使用怪物死亡时所在格子。
        var dropCx = mob.cx;
        var dropCy = mob.cy;

        // 首选原版 Loot.create + GenericCell，因为它生成的是正常可拾取蓝色细胞。
        if (level != null && TryCreateGenericCellLoot(level, mob, dropCx, dropCy))
        {
            DebugLog($"Arena cell created through Loot.create: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy})");
            return;
        }

        // 兜底方案：尝试 DeltaCell。之前测试过主要以 GenericCell 为准，这里只是防止完全不掉落。
        if (level != null && TryDropDeltaCell(level, mob, dropCx, dropCy))
        {
            DebugLog($"Arena cell dropped as DeltaCell: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy})");
            return;
        }

        // 按你的要求，不直接给细胞；如果物理掉落失败，就只写日志。
        DebugLog($"Arena cell physical drop failed: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy}). No direct cell grant by design.");
    }

    // 通过原版 Loot 工厂创建蓝色细胞掉落。
    private static bool TryCreateGenericCellLoot(Level level, dc.en.Mob mob, int cx, int cy)
    {
        // 这里只保留 GenericCell，避免之前同时尝试多种类型导致蓝色+黄色重复掉落。
        foreach (var lootType in new LootType[] { new LootType.GenericCell() })
        {
            try
            {
                // 调用原版 Loot.Class.create，让游戏自己创建对应 Loot 实体。
                var loot = Loot.Class.create.Invoke(lootType, level, cx, cy);
                if (loot == null)
                {
                    DebugLog($"Loot.create returned null: type={lootType}, pos=({cx},{cy})");
                    continue;
                }

                // init 初始化实体基础状态。
                loot.init();

                // initGfx 初始化显示对象，否则可能逻辑存在但看不见。
                loot.initGfx();

                // onDropAsLoot 让它按“掉落物”流程进入可拾取状态。
                loot.onDropAsLoot();

                // 给一点横向速度，让掉落表现更像原版爆出来。
                loot.dx = mob.dx + (_random.NextDouble() * 0.7 - 0.35);

                // 给一点向上速度，避免直接贴地。
                loot.dy = -0.45;

                // 确保可见。
                loot.visible = true;

                // 关闭 floating，避免它像某些特殊物品一样悬浮不落地。
                loot.floating = false;

                // 增大磁吸距离，方便玩家靠近时自动吸取。
                loot.magnetDist = DotNetMath.Max(loot.magnetDist, 10.0);

                // 增大拾取距离，减少“看见但捡不到”的情况。
                loot.pickDist = DotNetMath.Max(loot.pickDist, 1.5);

                // 延长存在时间，避免战斗中还没捡就消失。
                loot.lifeTimer = DotNetMath.Max(loot.lifeTimer, 12.0);

                // 成功创建后打印完整状态，方便查“掉了但看不见/捡不到”这类问题。
                DebugLog($"Loot.create candidate succeeded: type={lootType}, pos=({loot.cx},{loot.cy}), visible={loot.visible}, destroyed={loot.destroyed}, pickDist={loot.pickDist}, magnetDist={loot.magnetDist}");
                return true;
            }
            catch (Exception ex)
            {
                // Loot.create 某些版本可能签名或内部逻辑不同，失败就记录并尝试下一个类型。
                DebugLog($"Loot.create candidate failed: type={lootType}, pos=({cx},{cy}), {ex.GetType().Name}: {ex.Message}");
            }
        }

        // 所有候选 LootType 都失败。
        return false;
    }

    // 兜底创建 DeltaCell；当前主要用于 GenericCell 失败时保底。
    private static bool TryDropDeltaCell(Level level, dc.en.Mob mob, int cx, int cy)
    {
        try
        {
            // DeltaCell 是原版细胞实体之一，构造参数为坐标和来源怪物。
            var cell = new DeltaCell(cx, cy, mob);

            // 赋予一点随机横向速度。
            cell.dx = _random.Next(-2, 3);

            // 赋予向上速度，让它从死亡点弹出。
            cell.dy = -4;
            return true;
        }
        catch (Exception ex)
        {
            // 创建失败返回 false，让上层知道物理掉落彻底失败。
            DebugLog($"DeltaCell drop failed: pos=({cx},{cy}), {ex.GetType().Name}: {ex.Message}");
            return false;
        }
    }

    // 反射调用目标对象上的文本显示方法；用于 HUD fallback。
    private static bool TryInvokeTextMethod(object target, string text, params string[] methodNames)
    {
        // 获取目标对象实际类型，后面要扫描它的实例方法。
        var targetType = target.GetType();

        // 依次尝试候选方法名。
        foreach (var methodName in methodNames)
        {
            // 大小写不敏感地找 public 实例方法。
            var methods = targetType
                .GetMethods(BindingFlags.Public | BindingFlags.Instance)
                .Where(method => string.Equals(method.Name, methodName, StringComparison.OrdinalIgnoreCase));

            // 同名方法可能有重载，所以需要逐个尝试参数构造。
            foreach (var method in methods)
            {
                // 当前方法参数不适配时跳过。
                if (!TryBuildTextMethodArgs(method, text, out var args)) continue;

                try
                {
                    // 参数适配成功后尝试调用。
                    method.Invoke(target, args);
                    DebugLog($"Event text displayed through {targetType.FullName}.{method.Name}");
                    return true;
                }
                catch (TargetInvocationException ex)
                {
                    // 反射调用内部抛错时，真实异常在 InnerException 里。
                    DebugLog($"Event text method failed: {method.Name}, inner={ex.InnerException?.GetType().Name}: {ex.InnerException?.Message}");
                }
                catch (Exception ex)
                {
                    // 参数类型等其他反射错误走这里。
                    DebugLog($"Event text method failed: {method.Name}, {ex.GetType().Name}: {ex.Message}");
                }
            }
        }

        // 所有候选方法都不可用。
        return false;
    }

    // 根据反射方法签名构造一组“尽量安全”的文本调用参数。
    private static bool TryBuildTextMethodArgs(MethodInfo method, string text, out object?[] args)
    {
        // 读取方法参数列表。
        var parameters = method.GetParameters();

        // 预分配参数数组，长度必须和方法签名一致。
        args = new object?[parameters.Length];

        // 没有文本参数的方法无法显示文字；参数太多的重载不猜，避免误调用。
        if (parameters.Length == 0 || parameters.Length > 4) return false;

        // 必须至少填入一个字符串或 Haxe 字符串参数，才认为这个方法可用。
        var hasTextParameter = false;
        for (var i = 0; i < parameters.Length; i++)
        {
            // 当前参数类型。
            var parameterType = parameters[i].ParameterType;

            // .NET string 参数直接传 C# 字符串。
            if (parameterType == typeof(string))
            {
                args[i] = text;
                hasTextParameter = true;
                continue;
            }

            // Haxe 字符串参数需要调用 AsHaxeString 转换。
            if (parameterType.FullName == "dc.String")
            {
                args[i] = text.AsHaxeString();
                hasTextParameter = true;
                continue;
            }

            // int 参数通常是样式、持续时间、优先级等，默认传 0。
            if (parameterType == typeof(int))
            {
                args[i] = 0;
                continue;
            }

            // double 参数通常是持续时间或坐标，默认给 3 秒。
            if (parameterType == typeof(double))
            {
                args[i] = 3.0;
                continue;
            }

            // float 版本同理。
            if (parameterType == typeof(float))
            {
                args[i] = 3.0f;
                continue;
            }

            // bool 参数通常是开关，默认 false，避免打开未知行为。
            if (parameterType == typeof(bool))
            {
                args[i] = false;
                continue;
            }

            // 引用类型参数可以传 null，很多可选对象参数能接受 null。
            if (!parameterType.IsValueType)
            {
                args[i] = null;
                continue;
            }

            // 其他值类型不知道该填什么，放弃这个重载。
            return false;
        }

        // 只有确实填过文本参数，才允许调用。
        return hasTextParameter;
    }

    // 写调试日志；所有异常都吞掉，避免日志系统影响游戏。
    internal static void DebugLog(string message)
    {
        try
        {
            // 日志路径没初始化时直接跳过，比如 Mod 还没完全初始化。
            if (string.IsNullOrWhiteSpace(_debugLogPath)) return;

            // 确保日志目录存在。
            Directory.CreateDirectory(DotNetPath.GetDirectoryName(_debugLogPath)!);

            // 追加一行带时间戳的日志，便于你按游戏行为对照。
            DotNetFile.AppendAllText(_debugLogPath, $"[{DateTime.Now:HH:mm:ss}] {message}{Environment.NewLine}");
        }
        catch
        {
            // 调试日志不能影响游戏运行。
        }
    }
}

// RiftSiege 的用户配置文件结构。
internal sealed class RiftSiegeConfig
{
    // 总开关：true 启用事件，false 完全关闭事件。
    public bool Enabled { get; set; } = true;
}
