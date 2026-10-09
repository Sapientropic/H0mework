# CourtyCourt · Case 2 — editable release materials

**Jian Gao · v1**

*Two Minuses, One Plus, and a Bare Trace Under Oath: Ordered Closed Traces and Whole-Ball Response Curvature*

《两负一正，裸迹宣誓：有序闭迹与整球响应曲率》

**Complete local manuscripts and materials; public upload awaits the new Q6 evidence acceptance.**

The English and Chinese editions each contain 15 main sections, Appendices A–E and 190 numbered equations. Four original figures have Chinese and English SVG/PNG versions. The full Q1–Q6 written derivations are in the manuscripts; the proofs of Q5 and Q6 are in Sections 12 and 13, so no separate supplement is required.

This editable archive contains the manuscripts, figure sources and generators, shared publication layout, final claim selection, source/target bindings, evidence handoff and local acceptance summary. The two reading PDFs accompany it as separate files. Zenodo form fields are in `papers/low-energy-loop-response/zenodo-metadata.md`; the author supplies this paper's actual DOI and publication date when the record is released.

本地完整交付中英文正文、Q1–Q6书面证明、双语四图、两份阅读PDF及可编辑材料。新增承重证明已进入正文第12／13节。21枚新增根的H0公开迁入与完整验收仍待绑定，整套公开上传据此保持待办。

## Scope and fixed evidence

Q1/Q2 concern finite ordered Dirac words and whole-word preparation readback. Q3/Q4 concern matter feedback counted once and the complete five-term spatial response. Under Q4's specified external source, preparation, double-Laplace clocks and equal-radius two-ball window, the sharp window retains its nonanalytic linear term; raw and connected quadratic coefficient tensors have inertia (negative, positive, zero) = (2, 1, 0), with all mixed-entry bounds included. Mean retains its separate interval crossing zero on the second axis.

Q5 identifies the original action's Fourier Hessian with the 289-field matrix and constructs the complete Schur kernel in four complex momenta from five origin directions and a 45 + 21 + 32 dimensional coordinate complement. Its actual denominator-cleared field return retains contact, active and all nine null directions. Q6 retains the original Noether contact and ordered five-factor word, the real-field half-axis operator, the actual created-unit/background observer, the source-generated nonlinear finite window, the complete 289 × 289 tensor and the unaveraged mother-Euler window pencil. The nonlinear window and the linearized half-axis keep their own conditions; this response has no inherited Q4 inertia statement.

The final contracts and written-proof locations are in `papers/low-energy-loop-response/release-selection.json`. Public source/target identities and declared receipt transformations are in `papers/low-energy-loop-response/data/public-source-bindings.json` and `data/PUBLIC-EVIDENCE.md` within the same paper directory.

| Selected scope | Fixed identity and acceptance |
| --- | --- |
| Q1–Q4 | Homework T=`85cb5386ca132818f74d90470d87a252e4a27ea7`; consumed Case 1 L1–L17 retain S=`30218c1aea92640eae09b1d9204a09b01a2d0e47`. The accepted [Case 2 entry at ba591b43](https://github.com/Sapientropic/H0mework/blob/ba591b43e13a59ac676919aa153569615f8d4cb2/Lean/H0mework/Papers/LowEnergyLoopResponse.lean) covers this original scope. |
| Q5 and Q6 foundations | Original producer epochs are individually recorded. Reuse the accepted same-byte roots at [234817b3](https://github.com/Sapientropic/H0mework/tree/234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a), `docs/first-release-map.json` phys.P27/P29/P33. The fixed [51867c59 observation and root-supplement receipt](https://github.com/Sapientropic/H0mework/blob/51867c59042460646e57d5ead4c405cbca05c240/evidence/first-release/acceptance/proof-root-supplement-20261007/receipt.json) retain their own later identity. |
| Q6 new roots and actual consumers | The bounded source snapshot is Homework `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`, with each root's original epoch and certification preserved. The 21 new roots require the actual public import/resource closure, declared receipt derivations and passing acceptance. The executable handoff is `papers/low-energy-loop-response/h0-evidence-request.md`. |

A new fixed H0 commit, a real registered paper entry and its passing acceptance receipt must be bound in the selection and source map before this edition is marked ready for public upload. The old Case 2 entry and `make check-case2` keep their Q1–Q4 scope.

The original 791-file research archive remains intact in the writing workspace. That archive, its private manifest, original runtime receipts/logs and caches are excluded from this editable public package. Published receipt derivations retain the original digest, public digest and declared transformation. Original full-chain certifications, local independent replays and publication checks have separate execution identities.

## Build the reading editions

Extract the archive and run from the directory containing `papers/` and `shared/`:

```sh
python3 papers/low-energy-loop-response/scripts/build_pdf.py
```

The outputs are:

- `papers/low-energy-loop-response/build/low-energy-loop-response.pdf`
- `papers/low-energy-loop-response/build/low-energy-loop-response-en.pdf`

Use `--lang zh` or `--lang en` to build one edition. This paper's thin entry registers the English running heads and continuous Appendices B–E, preserves the fourth plate's readable size, and calls the shared builder.

The layout uses Python 3, Pandoc 3.12, XeLaTeX, Latin Modern, `xeCJK`, `unicode-math`, `adjustbox`, `seqsplit`, `fvextra`, and Noto Serif/Sans CJK SC. Vector figure printing uses Google Chrome at its standard macOS application location. The package includes the vector PDFs used in the reading editions; editable SVGs and the manuscript sources are also supplied.

Figure regeneration uses the included house style and Chrome/Poppler. The fourth figure also uses Python `fontTools` for the house-font width checks:

```sh
python3 papers/low-energy-loop-response/figures/make_figures.py --lang zh
python3 papers/low-energy-loop-response/figures/make_figures.py --lang en
python3 papers/low-energy-loop-response/figures/make_full_return.py
```

The first generator draws Figures 1–3; the second draws Figure 4 in both languages. Both support `--svg-only`. `python3 papers/low-energy-loop-response/scripts/refresh_release.py --metadata-only` calls the shared metadata writer for the two manuscripts and PDFs. Its `--code-only` mode refreshes this paper's code-availability sections while preserving the split public scope.

## Reproduce the accepted public proof scope

For the original Q1–Q4 selection:

```sh
git clone https://github.com/Sapientropic/H0mework.git
cd H0mework
git checkout ba591b43e13a59ac676919aa153569615f8d4cb2
make bootstrap
make build
make check-case2
make check-map
```

For Q5 and the accepted Q6 foundations, follow the reproduction guide and actually registered checks at the fixed 234817b3/51867c59 identities listed above. The file-level map gives the exact versioned roots and receipts. Commands for the additional 21 roots are supplied only after their public selection is registered and accepted.

The full writing workspace uses Python 3.12 with SymPy 1.14.0 in `papers/low-energy-loop-response/build/release-venv/`; fresh focused outputs go to `papers/low-energy-loop-response/build/release-checks/` through `--output-dir`. Its designated release-summary entry is `validation/verify-release.py` within the paper directory. The archive's `papers/low-energy-loop-response/validation/release-checks.json` records the executed local acceptance; the private replay archive and workspace logs are not included. These local publication checks do not constitute a new certification of the 289-field production chain.

## References and rights

Case 0, Jian Gao, *We Found No Magic in This Mighty Universe: Common-Source Generation and Classical–Quantum Correspondence in a Spin×SU(7) Theory*, v1, is published at [10.5281/zenodo.23210292](https://doi.org/10.5281/zenodo.23210292). Case 1, Jian Gao, *The Current Takes the Stand: From Coupled Propagation to Actual Electrons, Coulomb Response, and Born Dressing*, v1, is cited through its fixed public proof entry until its actual DOI is available.

Manuscripts and original figures: [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Public proof software: Apache-2.0, with attribution and third-party notices in the fixed H0mework repository. Internal prompts and unrelated manuscripts are excluded.
