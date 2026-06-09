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
using ModCore.Mods;
using ModCore.Utilities;
using System.IO;
using System.Reflection;
using System.Runtime.CompilerServices;
using DotNetFile = System.IO.File;
using DotNetMath = System.Math;
using DotNetPath = System.IO.Path;
using DotNetType = System.Type;

namespace ArenaTeleporter;

// ArenaTeleporter 是一个独立的新 Mod。
// 第一版先实现可测试闭环：
// 1. 每张主地图随机抽取 15-30 的击杀阈值。
// 2. 玩家在普通地图击杀怪物达到阈值后，直接在当前地图启动本地刷怪事件。
// 3. 不生成传送门或独立地图，避免地图模板和切图逻辑带来的不稳定。
// 4. 事件期间每 0.1 秒刷 1 只随机普通敌人，敌人锁定玩家并尝试进攻。
// 5. 竞技场敌人死亡时，掉落 1 个可拾取的蓝色细胞。
// 6. 同一张地图只触发一次事件，避免重复刷怪。
public sealed class ModEntry(ModInfo info) : ModBase(info),
    IOnHeroUpdate,
    IOnHeroInit,
    IOnHeroDispose,
    IOnGameExit
{
    // 每局随机使用同一个 Random，避免同一帧多次 new Random 生成重复随机数。
    private static readonly Random _random = new();

    // 调试日志文件路径，位于 coremod/mods/ArenaTeleporter/moddbg.log。
    private static string? _debugLogPath;

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
        // Info.ModRoot 在安装后指向 coremod/mods/ArenaTeleporter。
        _debugLogPath = Info.ModRoot?.GetFilePath("moddbg.log");
        DebugLog("Initialize");

        // 缓存原版 pr.Game 实例，地图加载、细胞数读取都要用它。
        Hook_Game.init += Hook_Game_init;
        Hook_Game.onDispose += Hook_Game_onDispose;

        // 玩家击杀敌人后，原版会调用 Hero.onMobDeath；这里负责计数触发事件，并给事件怪掉落 1 个蓝色细胞。
        Hook_Hero.onMobDeath += Hook_Hero_onMobDeath;

        Logger.Information("ArenaTeleporter initialized.");
    }

    private static void Hook_Game_init(Hook_Game.orig_init orig, Game self)
    {
        _currentGame = self;
        DebugLog("Captured dc.pr.Game instance.");
        orig(self);
    }

    private static void Hook_Game_onDispose(Hook_Game.orig_onDispose orig, Game self)
    {
        if (ReferenceEquals(_currentGame, self))
        {
            _currentGame = null;
            ResetCurrentLevelState("game disposed");
        }

        orig(self);
    }

    void IOnGameExit.OnGameExit()
    {
        ResetCurrentLevelState("game exit");
        _mapsWithEntryPortal.Clear();
    }

    void IOnHeroInit.OnHeroInit()
    {
        _mapsWithEntryPortal.Clear();
        ResetCurrentLevelState("hero init / respawn");
        DebugLog("Hero initialized: cleared triggered maps so respawn can trigger local arena again.");
    }

    void IOnHeroDispose.OnHeroDispose()
    {
        _mapsWithEntryPortal.Clear();
        ResetCurrentLevelState("hero dispose / death");
        DebugLog("Hero disposed: cleared triggered maps so next hero can trigger local arena again.");
    }

    void IOnHeroUpdate.OnHeroUpdate(double dt)
    {
        var hero = ModCore.Modules.Game.Instance.HeroInstance;
        if (hero == null) return;

        var level = hero._level;
        if (level?.map == null) return;

        RefreshLevelStateIfNeeded(hero, level);
        UpdateEventPopText(dt);

        if (_inArena)
        {
            UpdateArena(hero, level, dt);
        }
    }

    // 地图变化时清理上一张地图的击杀计数和刷怪状态。
    private static void RefreshLevelStateIfNeeded(Hero hero, Level level)
    {
        var mapId = SafeToString(level.map.id);
        if (_currentMapId == mapId) return;

        ResetCurrentLevelState($"level changed: {_currentMapId ?? "null"} -> {mapId}");
        _currentMapId = mapId;

        if (!_loggedCurrentMap)
        {
            _loggedCurrentMap = true;
            DebugLog($"Level detected: map={mapId}, size={level.map.wid}x{level.map.hei}, hero=({hero.cx},{hero.cy}), eventKillThreshold={_entryKillThreshold}");
        }
    }

    // 在普通地图怪物死亡位置附近直接启动本地刷怪事件。
    private static void TryStartLocalArenaEventAtMobDeath(Hero hero, dc.en.Mob mob)
    {
        var level = hero._level;
        if (level?.map == null) return;
        if (string.IsNullOrWhiteSpace(_currentMapId)) return;
        if (_mapsWithEntryPortal.Contains(_currentMapId))
        {
            DebugLog($"Local arena skipped: map already triggered event, map={_currentMapId}.");
            return;
        }

        var deathCx = mob.cx;
        var deathCy = mob.cy;

        // 怪的死亡格如果能站人并且不覆盖交互物，就直接用死亡点。
        // 否则在死亡点周围找最近的可站立格，保证刷怪中心不会卡进墙里。
        if (!TryFindNearbyWalkablePoint(level, deathCx, deathCy, out var point))
        {
            DebugLog($"Local arena skipped: no walkable point near mob death, mob=({deathCx},{deathCy}).");
            return;
        }

        _mapsWithEntryPortal.Add(_currentMapId);
        StartLocalArenaEvent(hero, point);
        ShowLocalizedEventText();
        DebugLog($"Local arena started after kills: map={_currentMapId}, kills={_entryKillCount}/{_entryKillThreshold}, mobDeath=({deathCx},{deathCy}), center=({point.cx},{point.cy}), hero=({hero.cx},{hero.cy})");
    }

    private static void StartLocalArenaEvent(Hero hero, CPoint center)
    {
        _inArena = true;
        _arenaCenter = center;
        _spawnTimer = 0.0;
        _remainingArenaSpawns = LocalSpawnTotal;
        _arenaMobKeys.Clear();
        _aliveArenaMobKeys.Clear();

        DebugLog($"Local arena event armed: map={SafeToString(hero._level?.map?.id)}, center=({center.cx},{center.cy}), total={LocalSpawnTotal}, interval={LocalSpawnIntervalSeconds}, bossCells={GetBossCells()}");
    }

    // 竞技场每帧更新：定时刷怪。
    private static void UpdateArena(Hero hero, Level level, double dt)
    {
        if (_arenaCenter == null) return;
        if (_remainingArenaSpawns <= 0)
        {
            _inArena = false;
            _arenaCenter = null;
            _spawnTimer = 0;
            DebugLog($"Local arena event completed spawning: tracked={_arenaMobKeys.Count}, alive={_aliveArenaMobKeys.Count}");
            return;
        }

        _spawnTimer -= dt;
        if (_spawnTimer > 0) return;

        if (_aliveArenaMobKeys.Count >= MaxAliveArenaMobs)
        {
            _spawnTimer = LocalSpawnIntervalSeconds;
            DebugLog($"Arena spawn skipped: alive={_aliveArenaMobKeys.Count}, limit={MaxAliveArenaMobs}");
            return;
        }

        var preferredCx = hero.cx + _random.Next(-12, 13);
        var preferredCy = hero.cy + _random.Next(-3, 4);

        var spawned = TrySpawnArenaMobNear(level, hero, preferredCx, preferredCy, "near-hero")
            || TrySpawnArenaMobNear(level, hero, _arenaCenter.cx, _arenaCenter.cy, "event-center");

        if (spawned)
        {
            _remainingArenaSpawns--;
        }

        _spawnTimer = LocalSpawnIntervalSeconds;
        DebugLog($"Local arena spawn progress: remaining={_remainingArenaSpawns}, alive={_aliveArenaMobKeys.Count}");
    }

    // 在期望坐标附近找一个可站立格再刷怪，避免把怪刷进墙里或刷到玩家看不到的断层。
    private static bool TrySpawnArenaMobNear(Level level, Hero hero, int preferredCx, int preferredCy, string side)
    {
        if (!TryFindNearbyWalkablePoint(level, preferredCx, preferredCy, out var point))
        {
            DebugLog($"Arena spawn skipped: side={side}, no walkable point near=({preferredCx},{preferredCy})");
            return false;
        }

        return SpawnArenaMob(level, hero, point.cx, point.cy);
    }

    // 在指定坐标刷一只随机普通敌人，并把它的生命值翻倍。
    private static bool SpawnArenaMob(Level level, Hero hero, int cx, int cy)
    {
        var firstIndex = _random.Next(_mobTypeNames.Length);

        for (var attempt = 0; attempt < _mobTypeNames.Length; attempt++)
        {
            var typeName = _mobTypeNames[(firstIndex + attempt) % _mobTypeNames.Length];

            try
            {
                var mobType = DotNetType.GetType(typeName + ", GameProxy");
                if (mobType == null)
                {
                    DebugLog($"Spawn mob candidate skipped: type not found: {typeName}");
                    continue;
                }

                // 大多数普通怪构造函数是 (Level, cx, cy, tierA, tierB)。
                // tier 取当前 Boss 细胞，尽量贴近“当前难度的血量”，随后再把 maxLife/life 乘 2。
                var bossCells = GetBossCells();
                var mob = Activator.CreateInstance(mobType, level, cx, cy, bossCells, bossCells) as dc.en.Mob;
                if (mob == null)
                {
                    DebugLog($"Spawn mob candidate skipped: constructor returned null: {typeName}");
                    continue;
                }

                mob.init();

                // 初始化后原版已经按难度计算完血量，这里再翻倍。
                var originalMaxLife = mob.maxLife;
                var doubledMaxLife = DotNetMath.Max(1, originalMaxLife * 2);
                mob.maxLife = doubledMaxLife;
                mob.life = doubledMaxLife;
                mob.oldLife = doubledMaxLife;

                // 主动给玩家威胁值，促使敌人朝玩家进攻。
                var threat = 9999.0;
                mob.addThreat(hero, 9999.0, new Ref<double>(ref threat));
                mob.setNemesisTarget(hero);

                var key = RuntimeHelpers.GetHashCode(mob);
                _arenaMobKeys.Add(key);
                _aliveArenaMobKeys.Add(key);

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
        orig(self, mob);

        var key = RuntimeHelpers.GetHashCode(mob);
        if (!_arenaMobKeys.Remove(key))
        {
            CountNormalMobKillForEntry(self, mob);
            return;
        }

        _aliveArenaMobKeys.Remove(key);
        DebugLog($"Arena mob death tracked: mob={SafeToString(mob.type)}, remainingTracked={_arenaMobKeys.Count}, alive={_aliveArenaMobKeys.Count}");
        DropArenaCellReward(self, mob);
    }

    // 统计普通地图击杀数，达到本地图随机阈值后触发本地刷怪事件。
    private static void CountNormalMobKillForEntry(Hero hero, dc.en.Mob mob)
    {
        // 正在事件中、地图状态还没准备好、或者本地图已经触发过时，不继续累计。
        if (_inArena || string.IsNullOrWhiteSpace(_currentMapId)) return;
        if (_mapsWithEntryPortal.Contains(_currentMapId)) return;
        if (IsSecretOrSubLevel(hero._level)) return;

        // 只统计玩家当前关卡里的怪，避免特殊回调或召唤物死亡污染计数。
        if (!ReferenceEquals(hero._level, mob._level)) return;

        _entryKillCount++;
        DebugLog($"Entry kill progress: {_entryKillCount}/{_entryKillThreshold}, mob={SafeToString(mob.type)}, death=({mob.cx},{mob.cy})");

        if (_entryKillCount < _entryKillThreshold) return;

        TryStartLocalArenaEventAtMobDeath(hero, mob);
    }

    // 秘密子关卡不应该触发本地事件，避免打断原版特殊房间逻辑。
    private static bool IsSecretOrSubLevel(Level? level)
    {
        try
        {
            if (level == null) return false;
            return level.isSecret || level.isSubLevel;
        }
        catch
        {
            return false;
        }
    }

    // 随机找一个当前地图内相对安全、可站立的格子。
    private static bool TryFindWalkablePoint(Level level, int avoidCx, int avoidCy, int minDistance, out CPoint point)
    {
        var map = level.map;
        var width = DotNetMath.Max(1, map.wid);
        var height = DotNetMath.Max(1, map.hei);

        for (var attempt = 0; attempt < 240; attempt++)
        {
            var cx = _random.Next(3, DotNetMath.Max(4, width - 3));
            var cy = _random.Next(5, DotNetMath.Max(6, height - 5));

            if (DotNetMath.Abs(cx - avoidCx) + DotNetMath.Abs(cy - avoidCy) < minDistance) continue;
            if (!IsWalkable(level, cx, cy)) continue;
            if (IsNearExistingInteractive(level, cx, cy, 4)) continue;

            point = new CPoint(cx, cy);
            return true;
        }

        point = new CPoint(avoidCx, avoidCy);
        return false;
    }

    // 从指定中心点向外扩散查找可站立格子，适合“怪物死亡点附近启动事件”的场景。
    private static bool TryFindNearbyWalkablePoint(Level level, int centerCx, int centerCy, out CPoint point)
    {
        for (var radius = 0; radius <= 8; radius++)
        {
            for (var dx = -radius; dx <= radius; dx++)
            {
                for (var dy = -radius; dy <= radius; dy++)
                {
                    if (DotNetMath.Abs(dx) != radius && DotNetMath.Abs(dy) != radius) continue;

                    var cx = centerCx + dx;
                    var cy = centerCy + dy;
                    if (!IsWalkable(level, cx, cy)) continue;
                    if (IsNearExistingInteractive(level, cx, cy, 3)) continue;

                    point = new CPoint(cx, cy);
                    return true;
                }
            }
        }

        point = new CPoint(centerCx, centerCy);
        return false;
    }

    // 判定一个格子是否适合站立：
    // 脚下有地面，身体区域没有实体碰撞。
    private static bool IsWalkable(Level level, int cx, int cy)
    {
        try
        {
            var map = level.map;
            if (cx <= 1 || cy <= 1 || cx >= map.wid - 2 || cy >= map.hei - 2) return false;

            // checkCollRect(x, y, w, h, includeOneWay) 为 true 表示区域有碰撞。
            var bodyBlocked = map.checkCollRect(cx, cy - 2, 1, 2, true);
            var groundBlocked = map.checkCollRect(cx, cy + 1, 1, 1, true);
            return !bodyBlocked && groundBlocked;
        }
        catch
        {
            return false;
        }
    }

    // 避免刷怪中心贴着已有交互物。这里扫描当前关卡实体列表里的 Interactive。
    private static bool IsNearExistingInteractive(Level level, int cx, int cy, int radius)
    {
        try
        {
            var entities = level.entities;
            if (entities == null) return false;

            for (var i = 0; i < entities.length; i++)
            {
                if (entities.getDyn(i) is not Interactive interactive) continue;

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
            return DotNetMath.Clamp(_currentGame?.user?.bossRuneActivated ?? 0, 0, 5);
        }
        catch
        {
            return 0;
        }
    }

    private static void ResetCurrentLevelState(string reason)
    {
        _inArena = false;
        _currentMapId = null;
        _entryKillThreshold = _random.Next(15, 31);
        _entryKillCount = 0;
        _loggedCurrentMap = false;
        _arenaCenter = null;
        _spawnTimer = 0;
        _remainingArenaSpawns = 0;
        _arenaMobKeys.Clear();
        _aliveArenaMobKeys.Clear();
        ClearEventPopText();

        DebugLog($"Level state reset: reason={reason}");
    }

    private static string SafeToString(object? value)
    {
        try
        {
            return value?.ToString() ?? "null";
        }
        catch
        {
            return "unknown";
        }
    }

    private static string GetLocalizedEventText()
    {
        var language = string.Empty;

        try
        {
            language = SafeToString(Lang.Class.LANG);
        }
        catch
        {
            // 读取语言失败时走英文，避免本地化探测影响游戏运行。
        }

        var lower = language.ToLowerInvariant();
        return lower.Contains("zh")
            || lower.Contains("chinese")
            || lower.Contains("schinese")
            || lower.Contains("tchinese")
            || lower.Contains("cn")
            ? "裂隙围攻事件出现"
            : "Rift Siege event appeared";
    }

    private static void ShowLocalizedEventText()
    {
        var text = GetLocalizedEventText();
        DebugLog($"Event text requested: {text}");

        var hero = ModCore.Modules.Game.Instance.HeroInstance;
        if (hero != null && TryShowHeroPopText(hero, text))
        {
            return;
        }

        try
        {
            var hud = _currentGame?.hud;
            if (hud == null)
            {
                DebugLog("Event text display skipped: hud=null");
                return;
            }

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
            DebugLog($"Event text display failed: {ex.GetType().Name}: {ex.Message}");
        }
    }

    private static bool TryShowHeroPopText(Hero hero, string text)
    {
        try
        {
            ClearEventPopText();

            // PopText 是原版的浮动文字进程。第一个参数绑定实体，所以这里绑定 Hero，
            // 文字会从玩家头顶附近弹出，而不是固定在屏幕 HUD 上。
            var popText = new PopText(hero, text.AsHaxeString(), EventPopTextColor, 0, true);
            popText.init();
            _eventPopTextTargetY = popText.startIGY - 92;
            popText.startIGY = _eventPopTextTargetY + EventPopTextIntroYOffset;
            popText.startIGX += 0;

            try
            {
                popText.text.textColor = EventPopTextColor;
                popText.text.alpha = 0.0;
                popText.text.customScale = 1.25;
                popText.text.maxWidth = 420.0;
            }
            catch (Exception styleEx)
            {
                DebugLog($"Hero PopText style failed: {styleEx.GetType().Name}: {styleEx.Message}");
            }

            _eventPopText = popText;
            _eventPopTextTimer = 0.0;
            DebugLog($"Event text displayed above hero through PopText: hero=({hero.cx},{hero.cy}), text={text}");
            return true;
        }
        catch (Exception ex)
        {
            DebugLog($"Hero PopText display failed: {ex.GetType().Name}: {ex.Message}");
            return false;
        }
    }

    private static void UpdateEventPopText(double dt)
    {
        if (_eventPopText == null) return;

        _eventPopTextTimer += dt;

        try
        {
            if (_eventPopText.destroyed)
            {
                _eventPopText = null;
                _eventPopTextTimer = 0;
                return;
            }

            var alpha = _eventPopTextTimer < 0.22
                ? _eventPopTextTimer / 0.22
                : _eventPopTextTimer > EventPopTextDurationSeconds - 0.45
                    ? DotNetMath.Max(0.0, (EventPopTextDurationSeconds - _eventPopTextTimer) / 0.45)
                    : 1.0;

            var introProgress = DotNetMath.Clamp(_eventPopTextTimer / EventPopTextIntroSeconds, 0.0, 1.0);
            var easedProgress = 1.0 - DotNetMath.Pow(1.0 - introProgress, 3.0);
            _eventPopText.text.alpha = alpha;
            _eventPopText.startIGY = _eventPopTextTargetY + EventPopTextIntroYOffset * (1.0 - easedProgress);

            if (_eventPopTextTimer >= EventPopTextDurationSeconds)
            {
                ClearEventPopText();
            }
        }
        catch (Exception ex)
        {
            DebugLog($"Event PopText update failed: {ex.GetType().Name}: {ex.Message}");
            ClearEventPopText();
        }
    }

    private static void ClearEventPopText()
    {
        if (_eventPopText == null) return;

        try
        {
            if (!_eventPopText.destroyed)
            {
                _eventPopText.destroy();
            }
        }
        catch (Exception ex)
        {
            DebugLog($"Event PopText destroy failed: {ex.GetType().Name}: {ex.Message}");
        }

        _eventPopText = null;
        _eventPopTextTimer = 0;
        _eventPopTextTargetY = 0;
    }

    private static void DropArenaCellReward(Hero hero, dc.en.Mob mob)
    {
        var level = mob._level ?? hero._level;
        var dropCx = mob.cx;
        var dropCy = mob.cy;

        if (level != null && TryCreateGenericCellLoot(level, mob, dropCx, dropCy))
        {
            DebugLog($"Arena cell created through Loot.create: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy})");
            return;
        }

        if (level != null && TryDropDeltaCell(level, mob, dropCx, dropCy))
        {
            DebugLog($"Arena cell dropped as DeltaCell: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy})");
            return;
        }

        DebugLog($"Arena cell physical drop failed: mob={SafeToString(mob.type)}, pos=({dropCx},{dropCy}). No direct cell grant by design.");
    }

    private static bool TryCreateGenericCellLoot(Level level, dc.en.Mob mob, int cx, int cy)
    {
        foreach (var lootType in new LootType[] { new LootType.GenericCell() })
        {
            try
            {
                var loot = Loot.Class.create.Invoke(lootType, level, cx, cy);
                if (loot == null)
                {
                    DebugLog($"Loot.create returned null: type={lootType}, pos=({cx},{cy})");
                    continue;
                }

                loot.init();
                loot.initGfx();
                loot.onDropAsLoot();
                loot.dx = mob.dx + (_random.NextDouble() * 0.7 - 0.35);
                loot.dy = -0.45;
                loot.visible = true;
                loot.floating = false;
                loot.magnetDist = DotNetMath.Max(loot.magnetDist, 10.0);
                loot.pickDist = DotNetMath.Max(loot.pickDist, 1.5);
                loot.lifeTimer = DotNetMath.Max(loot.lifeTimer, 12.0);
                DebugLog($"Loot.create candidate succeeded: type={lootType}, pos=({loot.cx},{loot.cy}), visible={loot.visible}, destroyed={loot.destroyed}, pickDist={loot.pickDist}, magnetDist={loot.magnetDist}");
                return true;
            }
            catch (Exception ex)
            {
                DebugLog($"Loot.create candidate failed: type={lootType}, pos=({cx},{cy}), {ex.GetType().Name}: {ex.Message}");
            }
        }

        return false;
    }

    private static bool TryDropDeltaCell(Level level, dc.en.Mob mob, int cx, int cy)
    {
        try
        {
            var cell = new DeltaCell(cx, cy, mob);
            cell.dx = _random.Next(-2, 3);
            cell.dy = -4;
            return true;
        }
        catch (Exception ex)
        {
            DebugLog($"DeltaCell drop failed: pos=({cx},{cy}), {ex.GetType().Name}: {ex.Message}");
            return false;
        }
    }

    private static bool TryInvokeTextMethod(object target, string text, params string[] methodNames)
    {
        var targetType = target.GetType();

        foreach (var methodName in methodNames)
        {
            var methods = targetType
                .GetMethods(BindingFlags.Public | BindingFlags.Instance)
                .Where(method => string.Equals(method.Name, methodName, StringComparison.OrdinalIgnoreCase));

            foreach (var method in methods)
            {
                if (!TryBuildTextMethodArgs(method, text, out var args)) continue;

                try
                {
                    method.Invoke(target, args);
                    DebugLog($"Event text displayed through {targetType.FullName}.{method.Name}");
                    return true;
                }
                catch (TargetInvocationException ex)
                {
                    DebugLog($"Event text method failed: {method.Name}, inner={ex.InnerException?.GetType().Name}: {ex.InnerException?.Message}");
                }
                catch (Exception ex)
                {
                    DebugLog($"Event text method failed: {method.Name}, {ex.GetType().Name}: {ex.Message}");
                }
            }
        }

        return false;
    }

    private static bool TryBuildTextMethodArgs(MethodInfo method, string text, out object?[] args)
    {
        var parameters = method.GetParameters();
        args = new object?[parameters.Length];

        if (parameters.Length == 0 || parameters.Length > 4) return false;

        var hasTextParameter = false;
        for (var i = 0; i < parameters.Length; i++)
        {
            var parameterType = parameters[i].ParameterType;

            if (parameterType == typeof(string))
            {
                args[i] = text;
                hasTextParameter = true;
                continue;
            }

            if (parameterType.FullName == "dc.String")
            {
                args[i] = text.AsHaxeString();
                hasTextParameter = true;
                continue;
            }

            if (parameterType == typeof(int))
            {
                args[i] = 0;
                continue;
            }

            if (parameterType == typeof(double))
            {
                args[i] = 3.0;
                continue;
            }

            if (parameterType == typeof(float))
            {
                args[i] = 3.0f;
                continue;
            }

            if (parameterType == typeof(bool))
            {
                args[i] = false;
                continue;
            }

            if (!parameterType.IsValueType)
            {
                args[i] = null;
                continue;
            }

            return false;
        }

        return hasTextParameter;
    }

    internal static void DebugLog(string message)
    {
        try
        {
            if (string.IsNullOrWhiteSpace(_debugLogPath)) return;

            Directory.CreateDirectory(DotNetPath.GetDirectoryName(_debugLogPath)!);
            DotNetFile.AppendAllText(_debugLogPath, $"[{DateTime.Now:HH:mm:ss}] {message}{Environment.NewLine}");
        }
        catch
        {
            // 调试日志不能影响游戏运行。
        }
    }
}
