# Editable first-release materials

This package accompanies *The Current Takes the Stand: From Coupled Propagation to Actual Electrons, Coulomb Response, and Born Dressing* by Jian Gao. It contains the complete Chinese and English texts of §§1–14 and Appendices A–G, nine figure sources in each language, their fixed data, and the shared reading-layout dependencies. The claim scope is **L1–L28**.

The two reading PDFs are separate Zenodo upload files. The bilingual text and written proofs are complete; at the fixed public observation the added L18–L28 proof selection still awaits an authorized export and acceptance commit. This local package is ready for author review. Publication readiness requires that final binding. This source package preserves the directory layout used by the build commands below; run them from its root. The paper text and figures are licensed under CC BY 4.0. The formal proof selection has its own Apache-2.0 license and third-party notices in the public code repository.

## Build the reading editions

The existing pipeline uses Python 3, Pandoc 3, XeLaTeX with xeCJK, TeX Live's Latin Modern fonts, and Noto Serif/Sans CJK SC in the user's or system's `Library/Fonts` directory. Google Chrome is used when an SVG has no supplied PDF. Supplied vector figures are used directly.

```sh
python3 papers/low-energy-phenomenology/scripts/build_pdf.py
```

This thin entry imports the included common builder, registers both running heads, and writes the Chinese and English PDFs under the paper's `build/` directory. `--language zh` and `--language en` select one edition. It uses the common typography and figure-caption filter.

## Reproduce the figures

The figure scripts use `shared/figure-style/house_style.py`. Main-figure mathematical labels are vector MathText/STIX glyphs with editable TeX metadata; other labels remain SVG text. The current canvases, source parameters, signed growth variable and original time are retained in both languages. The main dashed curves are actual segmented paths.

```sh
uv run --with matplotlib==3.11.2 --with pymupdf==1.28.2 --with pillow==12.3.0 python papers/low-energy-phenomenology/figures/src/draw_main_figures.py --language en
python3 papers/low-energy-phenomenology/figures/src/draw_figures.py --language en --receipt papers/low-energy-phenomenology/figures/data/exact-readout.json --output papers/low-energy-phenomenology/figures
```

Use `--language zh` for the Chinese labels. The additional action/clock, Newton and Born plates are generated with `draw_release_figures.py --language both` using the same dependencies; their fixed source identity is 71e. Main-figure SVGs are printed to one-page vector PDFs with headless Google Chrome and rasterized with Poppler. The appendix script generates SVG; the reading builder uses the supplied vector PDFs or prints the SVG when a PDF is absent. Fonts can be installed locally; this package includes no font binaries.

## Data and proof identity

`figures/data/source-exports.json` binds the eight exact output files to their original Git paths and SHA-256 digests. `main-parameters.json` supplies the rational phase coefficients and finite-control parameters; the CSV files are plotting samples of these formulas. The figures contain theoretical readouts, with no empirical fitting.

The inherited L1–L17 mathematical source is Homework **S = `30218c1aea92640eae09b1d9204a09b01a2d0e47`**. The exported view is **base = `8e29b8e1e58f9846fdddedaaeab9fc8724cdcb87`**, the immediate successor of S. The selected source paths are byte-identical across this step. Public import and resource rewrites, and receipt publication transforms, are recorded by the code repository rather than silently identified with the private originals.

The inherited L1–L17 public proof binding is [H0mework commit ba591b43e13a59ac676919aa153569615f8d4cb2](https://github.com/Sapientropic/H0mework/tree/ba591b43e13a59ac676919aa153569615f8d4cb2). Its entry is `H0mework.Papers.LowEnergyPhenomenology`; `public-proof-index.json` maps all 28 release claims to their written proofs and fixed production/consumer paths, distinguishing actual inherited exports from pending additions. L18–L23 retain e05558097256e86b537c019c8ca63cd449d6b2d2, L24–L25 retain c62f3d25c42d4bf2b77ac009b49fc71cfd752f46, and L26–L28 retain 71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9. The pinned Lean toolchain is `v4.33.0`, with mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

In a checkout of that public commit:

```sh
make bootstrap && make build
make check
make check-map
python3 tools/source_view.py --output restored --at base --path Verification/physics/low-energy-phenomenology/stabilizer-derivation.md
```

`make check` is the repository's finite scientific-check target. The historical Lean and complete 289/1078-row matrix certifications retain their original execution identity; this manuscript release does not claim a fresh full rebuild. The paper's Appendix E and the public index locate those original records.

## Metadata

The included `zenodo-metadata.md` supplies bilingual titles, abstracts, keywords, author identity and fixed software links. Its generation entry explicitly includes both PDFs:

```sh
python3 papers/low-energy-phenomenology/scripts/prepare_zenodo.py
```

This command runs after building both editions. The paper cites the published physics predecessor [10.5281/zenodo.23210292](https://doi.org/10.5281/zenodo.23210292). This package reserves no new DOI and assigns no publication date; those fields are completed by the author at actual publication.

## Local exact checks

```sh
uv run --with sympy==1.14.0 python papers/low-energy-phenomenology/validation/verify_new_math.py
python3 papers/low-energy-phenomenology/validation/verify_release.py
```

The first command checks algebra used in the new written proofs and critical counterexamples. The second checks the complete bilingual formula/label alignment and supplied vector plates after building both PDFs. Neither represents a new full Lean or large-matrix certification.
