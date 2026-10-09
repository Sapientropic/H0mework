<p align="center"><img src="docs/assets/banner.svg" alt="H0mework · An unfinished map: the 0 marks the point from which the map grows" width="100%"></p>

[简体中文](README.md) · English

This repository contains the proofs and evidence behind a family of research papers.

The papers begin with a common source: how a process retains its history, how fields and particles arise together, how classical and quantum descriptions correspond, why debt persists after settlement, and what observation pays for compression. The arguments are developed in the papers; their Lean 4 proofs, reproduction programs and frozen results are available here for independent checking.

## Published papers

| Paper | Zenodo | English editions | Proofs |
| --- | --- | --- | --- |
| **The State Is Not the History, the Source Is: Identity, Responsibility, and Minimal Revision in Processes** | [DOI](https://doi.org/10.5281/zenodo.23210084) | [Paper](papers/first-release/pdf/source-process-core-en.pdf) · [Supplement](papers/first-release/pdf/source-process-core-supplement-en.pdf) | [Reproduction guide](docs/first-release-reproduction.md) |
| **We Found No Magic in This Mighty Universe: Common-Source Generation and Classical–Quantum Correspondence in a Spin×SU(7) Theory** | [DOI](https://doi.org/10.5281/zenodo.23210292) | [Paper](papers/first-release/pdf/physics-common-source-en.pdf) · [Supplement](papers/first-release/pdf/physics-common-source-supplement-en.pdf) | [Claim-to-source map](docs/first-release-map.json) |

Chinese editions, editable manuscripts, figure sources and English arXiv source packages are listed in the [paper package](papers/first-release/README.md).

The second editions of the process-core and common-source physics papers, and the low-energy selections L1–L28 and Q1–Q6, have separate [claim maps](docs/second-edition-map.json), a [low-energy map](docs/low-energy-release-map.json), and [reproduction commands](docs/edition-reproduction.md). Actual material acceptance and local delivery are recorded in the [edition readiness card](docs/second-edition-readiness.md).

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
- Earlier paper editions are bound to the [`papers-2026-09`](https://github.com/Sapientropic/H0mework/tree/papers-2026-09) tag. The current two-paper release follows the fixed versions in the [claim-to-source map](docs/first-release-map.json).

`Lean/` contains proofs, `scripts/` contains reproduction programs, and `evidence/` contains frozen results. The [export map](tools/export-map.json) records file origins and hashes. `papers/first-release/` contains the two published papers, supplements, editable sources and distribution packages.

## License

Original code and evidence are distributed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The first-release papers use CC BY 4.0, as recorded in their [publication metadata](papers/first-release/source/papers/source-process-core/zenodo-metadata.md#licenses). Third-party excerpts retain their original copyright and license; see the [third-party source index](docs/source-materials.md#第三方材料).
