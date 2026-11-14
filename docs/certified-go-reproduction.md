# Certified Go proof and replay

The [GO1–GO8 map](certified-go-map.json) identifies the original producers, independent consumers, and the retained execution inputs. The [selection](../checks/certified-go-selection.json) fixes the original proof epoch at `e60a86058abcb74b7f2225f2383c182be8343785`.

Run from the repository root with the pinned toolchain. The public Lake targets build the original proof modules and each original IO runner separately.

```sh
make bootstrap
lake -d Lean build CertifiedGo
lake -d Lean build +H0mework.Papers.CertifiedGo.Re60a8605
python3 tools/paper_proofs.py certified-go entry
python3 tools/paper_proofs.py certified-go build --output .local/go-build
python3 tools/paper_proofs.py certified-go roots --output .local/go-roots
python3 tools/paper_proofs.py certified-go trust --output .local/go-trust
python3 tools/paper_proofs.py certified-go types --output .local/go-types
python3 tools/paper_proofs.py certified-go source --output .local/go-source --exact
```

The exact view restores the original Lean directory names and gzip inputs. The [input custody record](../evidence/certified-go/input-custody.json) binds their preserved bytes. From a checkout with the public modules already built, run the 73-row control and W31 as follows.

```sh
repo=$PWD
r=e60a86058abcb74b7f2225f2383c182be8343785
from=H0mework/Versions/Re60a8605/ReleaseMaterials/SaturationMonoid/ProcessGame/Regression/CriticalKomi
graph=scratch/GoCriticalKomi/EarlierSourceSearch/.cache/retained-w31-y2oi1paf/strategy_dag.json.gz
restored="$repo/.local/go-source/$r/Lean"
assembly=H0mework/Versions/Re60a8605/ReleaseMaterials/Scratch/GoCriticalKomi/EarlierSourceSearch/ElevenAssembly.lean
run_go() {
  lake -d "$repo/Lean" env bash -c 'cd "$1"; shift; exec lean "$@"' _ "$restored" \
    --trust=0 -DwarningAsError=true --run "$@"
}
run_go "$repo/Lean/$from/RunRegionalProgram19.lean" --dag
run_go "$repo/Lean/$from/RunRegionalDAG19.lean" "$restored/$graph" --w31
run_go "$repo/Lean/$assembly" "$restored/$graph"
```

The original W31 receipt records 1,700,986 nodes and 2,007,462 edges, and the actual first response B(2,4). The original H11 batch retained 348 of 351 immediate replies. W02, W31, and W32 retain their independent receipts. The source map links those historical computations separately from the local public proof build and trust audits.

The public Lean checks passed for all 48 selected roots and 97 complete declaration types. Both source views recovered 1,434 files. The [complete H11 replay](../evidence/certified-go/acceptance/original-source-h11-replay.json) validates the original graph, assembles the 351 White replies in one process and produces the certificate at the actual ten-ply predecessor through Black's B(2,1).

The [CI comparison](../evidence/cache-preservation/observation-go.json) lists the existing shard keys and their status after this intake.
