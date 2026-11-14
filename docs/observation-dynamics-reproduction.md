# Autonomous Observation Dynamics proof and source reproduction

The [per-claim map](observation-dynamics-map.json) connects the paper's claims to their fixed Lean sources, public owners, direct consumers and receipts. The [selection](../checks/observation-dynamics-selection.json) keeps each historical source in its own Lean environment. O25 refers to the independent molecular electronic structure paper.

Run from the repository root with the pinned Lean toolchain and manifest.

```sh
make bootstrap
lake -d Lean build ObservationDynamicsRelease
python3 tools/paper_proofs.py observation-dynamics entry
python3 tools/paper_proofs.py observation-dynamics build --output .local/observation-build
python3 tools/paper_proofs.py observation-dynamics roots --output .local/observation-roots
python3 tools/paper_proofs.py observation-dynamics trust --output .local/observation-trust
python3 tools/paper_proofs.py observation-dynamics types --output .local/observation-types
make check-map check-obs
```

```sh
python3 tools/paper_proofs.py observation-dynamics source --output .local/observation-source
```

The public view restores each fixed source path and the selected publication views of receipts. To recover original receipt bytes, supply the exact originals named by the recorded SHA-256 using `--exact --private-originals PATH`. The public collection includes the FlyCNS Lean algorithms, controls, and historical receipts. The original data-heavy FlyCNS runs use the full research inputs documented by those receipts. The manuscript's editable archive includes `verification/recheck.py` for independent exact arithmetic checks.

Corollary 2.5 is proved by `prefix_has_update_iff_kernel_eq` in `H0mework.ReleaseProofs.Observation.PrefixDeterminacy`. At the live receiver seam, `delta_pair_query` gives the query's actual next pair, and the original and stock programs establish the equality needed to read that pair from the next receipt. The claim map identifies both public owners and the exact historical sources.

The [CI comparison](../evidence/cache-preservation/observation-go.json) records the unchanged shard keys. The [certification custody record](../evidence/observation-dynamics/certification-custody.json) identifies the retained historical inputs and distinguishes them from this edition's kernel runs.
