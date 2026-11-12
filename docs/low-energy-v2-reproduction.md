# Low-energy series, second-edition evidence

| Paper | Inherited results | Second-edition proof packages |
|---|---|---|
| Low-energy electromagnetic emergence | L1–L28 | L26–L29, including the high-frequency Born deficit |
| Ordered traces and polarization curvature | Q1–Q6 | Q7, including the finite-window limit, explicit polynomial evaluation, photon feed, and cutoff-independent infrared return |

The [second-edition map](low-energy-v2-map.json) binds the written results to exact declarations, complete checked types, public owners, direct consumers and original resources. The [first-edition map](low-energy-release-map.json) retains the inherited claims and their original acceptance. The second-edition entry checks separate fresh receipts for those 16 inherited packages and the ten added or expanded scopes.

## Verify and build

Use the pinned Lean toolchain and mathlib manifest in `Lean/`. Install the existing dependency cache with `make bootstrap` if needed. Run from the repository root and choose a fresh output directory for every execution.

```sh
make check-map
python3 tools/low_energy_v2.py entry
for check in build trust types; do
  LEAN_NUM_THREADS=2 python3 tools/low_energy_v2.py "$check" --output ".local/low-energy-v2-$check"
  LEAN_NUM_THREADS=2 python3 tools/low_energy_v2.py "$check" --inherited --output ".local/low-energy-v2-v1-$check"
done
```

Use `--paper low-energy-phenomenology` or `--paper low-energy-loop-response` to execute one paper’s packages. Each package imports its actual source environment. The Q7 matrix, event feed and cutoff audits have separate entries. The original event receipt also preserves the failed combined-import trial. The finite prepared-photon pair retains its finite Green legs. The cutoff equality applies to the full-Y static matrix, physical five-leg window and infrared return.

The new proofs retain the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. Original execution receipts keep their own source epochs and verdicts. The new Born theorem concerns sufficiently large positive real frequency on each fixed nonreal causal line. L29 gives a combined feedback and null coefficient in the finite return branch, with exact order when that coefficient is nonzero.

## Recover the original layout

```sh
python3 tools/low_energy_v2.py source --output .local/low-energy-v2-public
```

This reconstructs the [fixed selection](../checks/low-energy-v2-selection.json) by original path and epoch. Each changed source path, import, audit owner name and receipt has an export-map entry. For byte-for-byte receipt recovery, place the original private bodies in a directory under their recorded SHA-256 names and run the same command with `--exact --private-originals DIR` and a fresh output. The public view keeps scientific values, declarations and verdicts, using repository-relative runtime labels.

## CI and fixed numerical evidence

The [cache report](../evidence/low-energy-v2/acceptance/cache-preservation.json) compares the complete Linux plans. The 107 prior shard keys have matching complete archives. The 19 new owners form `s11-06` and use those upstream artifacts. The new selection takes its own complete acceptance after the formal workflow succeeds. Bell and quantum-carrier configurations and fixed input identities still match their previous successful receipts, with `full_replay` set to false.
