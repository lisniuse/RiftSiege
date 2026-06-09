# RiftSiege

Dead Cells Core Modding MDK mod. This mod currently implements a local arena-style encounter on the current map.

## Steam Workshop

https://steamcommunity.com/sharedfiles/filedetails/?id=3741466048

## Current Behavior

- Each normal map rolls a random kill threshold between 15 and 30.
- After the player kills enough normal enemies, a rift siege event starts near the last enemy death position.
- The event spawns 40 random enemies near the player, one every 0.1 seconds.
- Spawned enemies use the current boss-cell difficulty and have doubled health.
- Each spawned event enemy drops one collectible blue cell on death.
- Each map can trigger the event only once per run.

## Settings

The mod can be enabled or disabled without deleting it.

In game, open the Core Modding menu and enter `Rift Siege` or `裂缝入侵`, then choose one radio-style option:

```text
● Enabled
○ Disabled
```

The menu text follows the current game language. Chinese game language shows Chinese text; other languages use English.

You can also edit the generated config file in the installed mod directory:

```json
{
  "Enabled": true
}
```

Set `Enabled` to `false` to disable the event. The config is checked every second while the game is running.

## Build

From the Dead Cells install/workspace root:

```powershell
$env:DCCM_MDK_ROOT = (Resolve-Path .\dev\core\mdk\bin).Path
$env:DCCM_ROOT = (Resolve-Path .\coremod).Path + "\"
dotnet build .\dev\RiftSiege\RiftSiege.csproj -v:minimal
```

The project is configured with `AutoInstallMod=true`, so a successful build installs the mod into the local Core Modding mod directory.

## License

MIT
