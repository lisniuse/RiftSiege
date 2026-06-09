# RiftSiege

Dead Cells Core Modding MDK mod. This mod currently implements a local arena-style encounter on the current map.

## Current Behavior

- Each normal map rolls a random kill threshold between 15 and 30.
- After the player kills enough normal enemies, a rift siege event starts near the last enemy death position.
- The event spawns 40 random enemies near the player, one every 0.1 seconds.
- Spawned enemies use the current boss-cell difficulty and have doubled health.
- Each spawned event enemy drops one collectible blue cell on death.
- Each map can trigger the event only once per run.

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
