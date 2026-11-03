<p align="center"><img src="docs/assets/banner.svg" alt="H0mework · An unfinished map: the 0 marks the point from which the map grows" width="100%"></p>

<p align="center">
  <a href="https://github.com/Sapientropic/H0mework/actions/workflows/ci.yml"><img alt="CI" src="https://img.shields.io/github/actions/workflow/status/Sapientropic/H0mework/ci.yml?branch=main&style=flat-square&label=CI"></a>
  <a href="https://h0mework.wiki/en/"><img alt="Site h0mework.wiki" src="https://img.shields.io/badge/site-h0mework.wiki-b3372c?style=flat-square"></a>
  <a href="#papers"><img alt="9 papers on Zenodo" src="https://img.shields.io/badge/Zenodo-9%20papers-3c679f?style=flat-square"></a>
  <a href="LICENSE"><img alt="Apache-2.0" src="https://img.shields.io/badge/license-Apache--2.0-3a332b?style=flat-square"></a>
</p>

<p align="center"><a href="README.md">简体中文</a> · English</p>

Lean 4 proofs, reproduction programs and frozen evidence behind a family of research papers. The papers tell the story to people; this repository hands every sentence stated as a theorem to the machine and checks it again from scratch.

**You don't have to trust the authors. You can check.** To read the papers first, visit [h0mework.wiki](https://h0mework.wiki/en/).

## Machine-checked

<!-- BEGIN CI STATUS -->
<a href="https://github.com/Sapientropic/H0mework/actions/runs/41500430850"><img src="docs/assets/ci-wall.en.svg" alt="Lean full selection: 53,198 modules across 11 stages and 65 shards, all checked" width="100%"></a>

- **53,198 Lean modules belong to one kernel-checked selection.** The current 11 stages and 65 shards use `--trust=0` throughout; [the latest main run](https://github.com/Sapientropic/H0mework/actions/runs/41500430850) passes at `4bdfd360`.
<!-- END CI STATUS -->

- **Cited declarations are audited again per edition.** Their full dependency closures use only Lean's three standard axioms, with `unsafe = 0` and `partial = 0`; each paper's acceptance and reproduction links are grouped below.
- **New content is rebuilt; unchanged content reuses its acceptance.** See [CI and incremental builds](docs/ci.md) for sharding, continuation and memory scheduling.

## Papers

<!-- BEGIN PAPERS -->
**[Browse all papers on the site, with abstracts and claim-level proofs →](https://h0mework.wiki/en/papers/)**

Latest: [The Structural Theorem of Capitalism](https://h0mework.wiki/en/papers/capital-formation/) · [An Economic Constitution of Possibility](https://h0mework.wiki/en/papers/economic-constitution/)

<details>
<summary><strong>Preface</strong> · 1 paper</summary>

- [1 Bit Is All You Need](https://h0mework.wiki/en/papers/one-bit/) · [v1](https://doi.org/10.5281/zenodo.23437456) · [Map](docs/one-bit-map.json) · [Reproduce](docs/one-bit-reproduction.md)

</details>

<details>
<summary><strong>Core methods</strong> · 2 papers</summary>

- [The State Is Not the History, the Source Is](https://h0mework.wiki/en/papers/source-process-core/) · [v2](https://doi.org/10.5281/zenodo.23297175) · [Map](docs/second-edition-map.json) · [Reproduce](docs/edition-reproduction.md)
- [Book-Balancing Magic Has Nowhere to Hide](https://h0mework.wiki/en/papers/whole-ledger-accounting/) · [v1](https://doi.org/10.5281/zenodo.23437454) · [Map](docs/whole-ledger-map.json) · [Reproduce](docs/whole-ledger-reproduction.md)

</details>

<details>
<summary><strong>Physics</strong> · 1 paper</summary>

- [We Found No Magic in This Mighty Universe](https://h0mework.wiki/en/papers/physics-common-source/) · [v2](https://doi.org/10.5281/zenodo.23297179) · [Map](docs/second-edition-map.json) · [Reproduce](docs/edition-reproduction.md)

</details>

<details>
<summary><strong>Low-energy series</strong> · 2 papers</summary>

- [The Current Takes the Stand](https://h0mework.wiki/en/papers/low-energy-phenomenology/) · [v1](https://doi.org/10.5281/zenodo.23299174) · [Map](docs/low-energy-release-map.json) · [Reproduce](docs/edition-reproduction.md)
- [Two Minuses, One Plus, and a Bare Trace Under Oath](https://h0mework.wiki/en/papers/low-energy-loop-response/) · [v1](https://doi.org/10.5281/zenodo.23299177) · [Map](docs/low-energy-release-map.json) · [Reproduce](docs/edition-reproduction.md)

</details>

<details>
<summary><strong>Mind & society</strong> · 3 papers</summary>

- [The Canonical Society Theorem](https://h0mework.wiki/en/papers/generated-society/) · [v2](https://doi.org/10.5281/zenodo.23917896) · [Map](docs/generated-society-map.json) · [Reproduce](docs/generated-society-reproduction.md)
- [An Economic Constitution of Possibility](https://h0mework.wiki/en/papers/economic-constitution/) · [v2](https://doi.org/10.5281/zenodo.23917902) · [Map](docs/economic-constitution-map.json) · [Reproduce](docs/economic-constitution-reproduction.md)
- [The Structural Theorem of Capitalism](https://h0mework.wiki/en/papers/capital-formation/) · [v1](https://doi.org/10.5281/zenodo.23927949) · [Map](docs/capital-formation-map.json) · [Reproduce](docs/capital-formation-reproduction.md)

</details>
<!-- END PAPERS -->

Main texts, proof supplements and editable sources are available from each Zenodo record. The site opens each claim, Lean declaration and original receipt; the theme groups above keep the maps and reproduction guides together.

<details>
<summary>Earlier editions and source bindings</summary>

- The first versions of the process-core and physics papers retain their original DOIs ([process core](https://doi.org/10.5281/zenodo.23210084), [physics](https://doi.org/10.5281/zenodo.23210292)) and [first-release package](papers/first-release/README.md). The [2026-10-09 low-energy snapshot](papers/low-energy-first-release/2026-10-09/README.md) retains its original file and source identities.
- The second editions and the two low-energy papers cite source commit `b9d66048`. Later public-source repairs and their `643721f1` binding are described in the [source index](docs/source-materials.md#四篇论文的源码绑定); material acceptance is recorded in the [edition status](docs/second-edition-readiness.md).
- Whole-ledger accounting and One Bit cite [`4301fa8c`](https://github.com/Sapientropic/H0mework/tree/4301fa8c5bb19bb1e8c3824d7c69be406264ed12) and [`6bff9d40`](https://github.com/Sapientropic/H0mework/tree/6bff9d4046b3f89004678244482b1c403837150c); their accepted scopes are in the [whole-ledger](docs/whole-ledger-readiness.md) and [One Bit](docs/one-bit-readiness.md) acceptance records.
- The earlier eight papers are bound to the [`papers-2026-09`](https://github.com/Sapientropic/H0mework/tree/papers-2026-09) tag, with commands in the [original reproduction guide](docs/reproduction.md). The first two-paper release follows the fixed versions in the [claim-to-source map](docs/first-release-map.json).

</details>

## Check it yourself

From the repository root, with Git, make and Python 3 (with `venv`); building Lean also needs elan.

```bash
make check-first-release-entry                # Entry checks: export integrity, Fock/Born identities, exact controls
make bootstrap && make build-first-release    # Fetch the pinned dependency cache and build the Lean proofs
make check-first-release-full                 # Complete acceptance suite
```

The [reproduction guide](docs/first-release-reproduction.md) describes scope and dependencies; the [acceptance record](docs/first-release-readiness.md) links the actual results. The toolchain is pinned in [`lean-toolchain`](Lean/lean-toolchain) and [`lake-manifest.json`](Lean/lake-manifest.json).

## Research threads

| Thread | Subject | Lean entry |
| --- | --- | --- |
| Low-energy phenomenology | Low-energy expansions, propagation, matter exchange and all-time Kubo response | [LowEnergyPhenomenology](Lean/H0mework/Papers/LowEnergyPhenomenology.lean) |
| Low-energy loop response | Closed traces, complete words of prepared states, bosonic effective kernels and analytic remainders | [LowEnergyLoopResponse](Lean/H0mework/Papers/LowEnergyLoopResponse.lean) |
| Constrained local quantum theory | Constraints from the original action, quantum constraints and common-family time evolution | [ConstrainedLocalQuantumK17](Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean) |
| Native flow | Native Navier–Stokes evolution and consumers of its history | [NativeFlow](Lean/H0mework/Papers/NativeFlow.lean) |
| Whole-ledger accounting | Whole-ledger structures, debt settlement and unforgeable settlement | [WholeLedgerAccountingY1](Lean/H0mework/Papers/WholeLedgerAccountingY1.lean) |
| Canonical society | Generated actors, nonempty root-law completion, actionable exit and same-occurrence regeneration | [GeneratedSocietyMInfinity](Lean/H0mework/Papers/GeneratedSocietyMInfinity.lean) · [Selection and acceptance](docs/generated-society-readiness.md) |
| Economic constitution of possibility | Capital, public production, public functions and planning interfaces adopted by the institutional argument | [EconomicConstitutionSourceDF](Lean/H0mework/Papers/EconomicConstitutionSourceDF.lean) · [Selection and acceptance](docs/economic-constitution-readiness.md) |
| Structural theorem of capitalism | Full structural characterization, public replay of arbitrary executions, continuing innovation, joint settlement and actual history | [EconomicConstitutionSourceDF](Lean/H0mework/Papers/EconomicConstitutionSourceDF.lean) · [Paper mapping and acceptance](docs/capital-formation-readiness.md) |
| Observation dynamics | Counted observation, versioned proofs and the exact cost of compression | [ObservationDynamics](Lean/H0mework/Papers/ObservationDynamics.lean) |

## Repository map

| Directory | Contents |
| --- | --- |
| [`Lean/`](Lean) | Proofs |
| [`scripts/`](scripts) | Reproduction programs |
| [`evidence/`](evidence) | Frozen results and acceptance receipts |
| [`papers/`](papers) | Main texts, supplements and packages of published papers |
| [`site/`](site) | Source of [h0mework.wiki](https://h0mework.wiki/en/) |

- [Evidence map](docs/evidence-map.md): the module, program and receipt behind each paper claim, including independent checks of Bell data.
- [Source materials](docs/source-materials.md): mechanism descriptions, verification reports, research history and third-party sources.
- [`tools/export-map.json`](tools/export-map.json): origin and hash of every file.

## License

Original code and evidence are distributed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). Each paper's license is the one on its Zenodo record; the first-release papers use CC BY 4.0, see their [publication metadata](papers/first-release/source/papers/source-process-core/zenodo-metadata.md#licenses). Third-party excerpts retain their original copyright and license; see the [third-party source index](docs/source-materials.md#第三方材料).
