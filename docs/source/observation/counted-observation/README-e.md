# Counted observation controls

Run `python3 Verification/no-island/counted-observation/verify.py --build` from the repository root.
Omit `--build` when owned and direct consumer modules are current. Logs and inventories stay in a temporary directory.
For an isolated audit, pass both `--source-root` and `--library` for the corresponding source and compiled trees.

- `Gate.lean`: all owned declarations, complete type/value dependency closure including opaque bodies, standard three axioms, constructor/readout value provenance, and original source-frontier direction. Posterior and next constructors must consume the existing restore/advance/nextModel and cannot consume the source answer. Counted merge constructors cannot consume a Frame, recovery, or source answer. Type fingerprints accompany the declaration and dependency inventories; they are not a substitute for kernel checking.
- `Controls.lean`: original `current_consumed` exposes the counted-source law at both normal and next.
- `Reachability.lean`: actual `runtimeAt 3`, complete inventory and exact source samples pay the initial budgets and consume arbitrary-step simulation, complete posterior recovery, autonomous next/Model, and actual coarse posterior/next Model in the original next Field.
- `Execution.lean`: executable source updates versus the original Frame; independent H/mass/clock, absent and duplicate keys, retained arrays, and opposite/same-direction residuals.
- `RecoveryControls.lean`: residual inventory cannot increase; fresh cells and nonzero old residuals have the precise distinct effects certified by the new equation.
- `RecoveryExecution.lean`: four actual receipts and 66 real coordinates; two positive recoveries and two cancellations, with source innovation retained even while total error increases.
- `PosteriorExecution.lean`: five actual prefixes, fine/coarse and absent keys, all 280 posterior coefficients, a noise coordinate that later enters the actor inventory, retained raw observations and the excluded half-margin boundary.
- `AdvanceExecution.lean`: five prefixes, 50 counts and 360 complete posterior coefficients; original next, updated-table restore and the original generator agree. Ten wrong-receipt controls distinguish the actual successor; future noise and original table fields remain intact.
- `MergeExecution.lean`: unequal fine-cell counts, five prefixes, 3,120 H coordinates and 260 posterior coefficients; merge then step, step then merge and the original Frame agree. Four unequal-weight controls reject unweighted averaging; mass/clock, absent and zero rows, and noise remain intact.

The executable noise fixture tests update semantics. Budget reachability is certified separately by `Reachability.lean`.
