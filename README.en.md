<p align="center"><img src="docs/assets/banner.svg" alt="H0mework · An unfinished map: the 0 marks the point from which the map grows" width="100%"></p>

[简体中文](README.md) · English

This repository contains the proofs and evidence behind a family of research papers.

The papers begin with a common source: how a process retains its history, how fields and particles arise together, how classical and quantum descriptions correspond, why debt persists after the books balance, and what observation pays for compression. The arguments are developed in the papers; their Lean 4 proofs, reproduction programs and frozen results are available here for independent checking.

## Published papers

| Paper | Zenodo version | Lean proofs and reproduction |
| --- | --- | --- |
| **The State Is Not the History, the Source Is: Identity, Responsibility, and Minimal Revision in Processes** | [v2](https://doi.org/10.5281/zenodo.23297175) | [Claim map](docs/second-edition-map.json) · [Reproduction](docs/edition-reproduction.md) |
| **We Found No Magic in This Mighty Universe: Common-Source Generation and Classical–Quantum Correspondence in a Spin×SU(7) Theory** | [v2](https://doi.org/10.5281/zenodo.23297179) | [Claim map](docs/second-edition-map.json) · [Reproduction](docs/edition-reproduction.md) |
| **The Current Takes the Stand: From Coupled Propagation to Actual Electrons, Coulomb Response, and Born Dressing** (Low-energy 1) | [v1](https://doi.org/10.5281/zenodo.23299174) | [Claim map](docs/low-energy-release-map.json) · [Reproduction](docs/edition-reproduction.md) |
| **Two Minuses, One Plus, and a Bare Trace Under Oath: Ordered Closed Traces and Whole-Ball Response Curvature** (Low-energy 2) | [v1](https://doi.org/10.5281/zenodo.23299177) | [Claim map](docs/low-energy-release-map.json) · [Reproduction](docs/edition-reproduction.md) |
| **Book-Balancing Magic Has Nowhere to Hide: Source-Native Accounting and Actual Continuation** | [v1](https://doi.org/10.5281/zenodo.23437454) | [Claim map](docs/whole-ledger-map.json) · [Reproduction](docs/whole-ledger-reproduction.md) |
| **1 Bit Is All You Need: The Weakest Superpower: No Unaccounted Differences** | [v1](https://doi.org/10.5281/zenodo.23437456) | [Claim map](docs/one-bit-map.json) · [Reproduction](docs/one-bit-reproduction.md) |

The main texts, necessary proof supplements and editable sources are available from each Zenodo record. The first versions of the process-core and physics papers retain their original DOIs ([process core](https://doi.org/10.5281/zenodo.23210084), [physics](https://doi.org/10.5281/zenodo.23210292)) and [first-release package](papers/first-release/README.md). The [2026-10-09 low-energy snapshot](papers/low-energy-first-release/2026-10-09/README.md) retains its original file and source identities.

The published second editions and the two low-energy papers cite source commit `b9d66048`. Subsequent public-source repairs and their `643721f1` binding are described in the [source index](docs/source-materials.md#四篇论文的源码绑定); actual material acceptance is recorded in the [edition status](docs/second-edition-readiness.md). Whole-ledger accounting and One Bit cite [`4301fa8c`](https://github.com/Sapientropic/H0mework/tree/4301fa8c5bb19bb1e8c3824d7c69be406264ed12) and [`6bff9d40`](https://github.com/Sapientropic/H0mework/tree/6bff9d4046b3f89004678244482b1c403837150c), respectively. Their accepted material scopes are recorded in the [whole-ledger](docs/whole-ledger-readiness.md) and [One Bit](docs/one-bit-readiness.md) acceptance cards.

## Other research threads

| Thread | Subject | Lean entry |
| --- | --- | --- |
| Low-energy phenomenology | Low-energy expansions, propagation, matter exchange and all-time Kubo response | [LowEnergyPhenomenology](Lean/H0mework/Papers/LowEnergyPhenomenology.lean) |
| Low-energy loop response | Closed traces, complete words of prepared states, bosonic effective kernels and analytic remainders | [LowEnergyLoopResponse](Lean/H0mework/Papers/LowEnergyLoopResponse.lean) |
| Constrained local quantum theory | Constraints from the original action, quantum constraints and common-family time evolution | [ConstrainedLocalQuantumK17](Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean) |
| Native flow | Native Navier–Stokes evolution and consumers of its history | [NativeFlow](Lean/H0mework/Papers/NativeFlow.lean) |
| Whole-ledger accounting | Whole-ledger structures, debt settlement and unforgeable settlement | [WholeLedgerAccountingY1](Lean/H0mework/Papers/WholeLedgerAccountingY1.lean) |
| Observation dynamics | Counted observation, versioned proofs and the exact cost of compression | [ObservationDynamics](Lean/H0mework/Papers/ObservationDynamics.lean) |

## Quick start

The entry checks require Git, make and Python 3 with `venv`. Run from the repository root:

```bash
make check-first-release-entry  # Export integrity, Fock/Born identities and exact controls
```

To build the Lean proofs, install elan/Lake, fetch the pinned dependency cache and build the release entries:

```bash
make bootstrap
make build-first-release
```

Run `make check-first-release-full` for the complete acceptance suite. The [reproduction guide](docs/first-release-reproduction.md) describes its scope, dependencies and commands; the [acceptance record](docs/first-release-readiness.md) links the actual results. The toolchain and dependencies are pinned in [lean-toolchain](Lean/lean-toolchain) and [lake-manifest.json](Lean/lake-manifest.json). Commands for the earlier paper editions are in the [original reproduction guide](docs/reproduction.md).

## From papers to proofs

- [Evidence map](docs/evidence-map.md): proof modules, reproduction programs and recorded results for the paper claims, including independent checks of Bell data.
- [Source materials](docs/source-materials.md): mechanism descriptions, verification reports, research history and third-party sources.
- [CI and incremental builds](docs/ci.md): job splitting, proof storage and reuse of unchanged compiled modules.
- Earlier paper editions are bound to the [`papers-2026-09`](https://github.com/Sapientropic/H0mework/tree/papers-2026-09) tag. The first two-paper release follows the fixed versions in the [claim-to-source map](docs/first-release-map.json).

`Lean/` contains proofs, `scripts/` contains reproduction programs, and `evidence/` contains frozen results. The [export map](tools/export-map.json) records file origins and hashes. `papers/first-release/` contains the two first-release papers, supplements, editable sources and distribution packages.

## License

Original code and evidence are distributed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The first-release papers use CC BY 4.0, as recorded in their [publication metadata](papers/first-release/source/papers/source-process-core/zenodo-metadata.md#licenses). Third-party excerpts retain their original copyright and license; see the [third-party source index](docs/source-materials.md#第三方材料).
