import type { APIRoute } from "astro";
import { ORDERED, paperOf, statsOf } from "../lib/papers";

export const GET: APIRoute = () => {
  const lines = [
    "# H0mework",
    "",
    `> Machine-checked Lean 4 proofs (--trust=0), reproduction programs, and frozen evidence behind a family of ${ORDERED.length} research papers by Jian Gao (ORCID: 0009-0009-5002-1655).`,
    "",
    "- Website (English): https://h0mework.wiki/en/",
    "- Website (Chinese): https://h0mework.wiki/",
    "- Verification Index: https://h0mework.wiki/en/check/",
    "- GitHub Repository: https://github.com/Sapientropic/H0mework",
    "- BibTeX of all papers: https://h0mework.wiki/papers.bib",
    "",
    "## Agent Audit Protocol (How AI Agents Can Verify Claims)",
    "",
    "- Every theorem claim on h0mework.wiki maps to concrete Lean 4 declarations in `Lean/` verified under `lean --trust=0` with zero `sorry` and zero custom `axiom` declarations.",
    "- Agents without local shell access can inspect each paper's JSON claim map (`Source Map` URL below) and follow the pinned GitHub links directly to the `.lean` source files and declaration lines.",
    "- Agents with shell access can clone `https://github.com/Sapientropic/H0mework` and run each paper's `Audit command` listed below.",
    "",
    "## Repository-Wide Positive & Negative Control Discipline (All 10 Papers)",
    "",
    "Every theoretical paper and verification runner in `Sapientropic/H0mework` enforces a strict, repository-wide **Paired Positive + Negative Control Discipline** (anti-vacuity counterexamples, necessary-and-sufficient `iff` gates, single-condition-drop failure models, compile-time `fail_if_success` guards, and retained empirical negative controls):",
    "",
    "- **Harness & Receipt Enforcement (`tools/`, `checks/`, `evidence/`)**:",
    "  - Every release requires `lean --trust=0` (zero `sorry`, zero custom axioms), full `Expr` DAG declaration-type SHA-256 verification (`declaration-types.json.gz`), downstream `direct_consumers` in the actual import closure, and executed negative controls.",
    "  - In `tools/first_release_replay.py` (`effective_negative_controls`) and `evidence/first-release/acceptance/scientific-20261005/receipt.json`, the verification harness explicitly fails if negative controls are absent or do not fire (47 executed negative controls across 4 suites, plus `actual_Born_uniform_counterexamples`).",
    "- **Paper 1 (`one-bit`)**: `checks/one-bit-control-map.json` and `docs/one-bit-reproduction.md` separately verify unequal raw values, identical lawful projections, and distinct actual occurrences across 17 control declarations and 6 admission producers, plus compile-time negative controls on illegal API applications (`OB1`, `OB11`).",
    "- **Paper 2 (`source-process-core`)**: Proves positive finite-settlement and minimal-revision theorems (`C2`, `C13`, `C28`) alongside ghost-register negative controls (`C5`, `C8`, `C35–C44`) where identical instantaneous states with distinct source histories diverge under lawful continuation.",
    "- **Paper 3 (`whole-ledger-accounting`)**: Pairs whole-ledger conservation (`Δ = 0` on every page) with explicit negative-control theorems proving that deleting inconvenient events (`WA2`), lending receipts to identical-looking sources (`WA3`), equating identical surface reports (`WA6`), or moving entries without settlement (`WA7`, `WA35`) cannot close the ledger residual.",
    "- **Papers 4–6 (`physics-common-source`, `low-energy-phenomenology`, `low-energy-loop-response`)**:",
    "  - **Formal Vacuity No-Go Boundary**: `Lean/H0mework/Versions/Re60a8605/ReleaseMaterials/SaturationMonoid/PhysicsCore/ConstitutiveHardGateVacuityBoundary.lean` (`constitutiveHardGateVacuityBoundary`) proves that an untyped schema can be inhabited by `Unit`, motivating the strict dual-axis and exact-admission hard gates.",
    "  - **Exact Coframe Admission vs. Mismatched-Coframe Rejection + Nonseparability (`Δ_mix = 9 ≠ 0`)**: `Lean/H0mework/Physics/Coframe/NonseparableSourceCoframeRegression.lean` proves positive admission (`sourceNonseparableConfiguration_exactAdmission`), nonseparability (`gravityGaugeMixedDifference_eq_nine`, `nonseparableMasterAction_not_additively_separable`), and the formal negative control (`mismatchedCoframeConfiguration_rejected`: a `timeModeProbe` coframe of the exact same Lean carrier type is formally rejected).",
    "  - **Bijective Standard Model Subalgebra Selection (`iff`)**: `Lean/H0mework/Physics/Lie/SU7MotherLieAlgebra.lean` (`selectedBySourceBreaking_iff_p286LieBlockImage`, `selected_entry_zero_of_breakingLevel_ne`) proves over 7x7 skew-adjoint traceless complex matrices that commutation with the `3+2+1+1` spectral order parameter plus 3 operational block-trace equations holds **if and only if** the matrix lies in `su(3) ⊕ su(2) ⊕ u(1)` (forcing all off-block entries to zero).",
    "  - **Einstein–Cartan–Torsion 4-Leg Equivalence (`iff`) & Pure Symmetric Plebanski Refutation (`5/8 ≠ 0`)**: `Lean/H0mework/Physics/DualVariation/IIPlusTorsionSpinCriticalLocus.lean` and `Lean/H0mework/Versions/Re60a8605/ReleaseMaterials/SaturationMonoid/PhysicsCore/StageNinePlebanskiExistingGravityMultiplierCompatibility.lean` prove 4-leg stationarity is equivalent to simplicity `B = II+(e)` + Einstein–Cartan balance + torsion–spin, while pure symmetric quadratic multipliers fail across the `Spin+(1,3)` orbit with pair-exchange defect `5/8 ≠ 0`. In `P39`, the 3-fermion charged state has strictly positive spectrum while the neutral channel is identically zero.",
    "  - **Empirical Positive vs. Negative Controls (§10.2)**: With zero tunable parameters, uncalibrated ideal nominal locks trigger immediate rejection (`P24` naive NIST 2015 nominal replay retained as negative outcome; Storz et al. 100k superconducting trials rejected at `log E = 46803.62` where the nominal table gives `S = 0`; Munich zero-error ideal lock rejected at trial 3,974 with `E ≈ 494.85 > 40`), whereas open-instrument recycling/loss fibres (`P31`, `P32`, `P35`, `P40`) pass all 20,403 Munich prefixes (`1.301828e-21` primal/adjoint agreement across the 120 ns gate) and yield `CH_N5 > 1.3790e-6` across the NIST 2015 joint 95% domain.",
    "- **Paper 7 (`generated-society`)**: Proves `K = 1` on complete and single-service sources while paired negative-control counterexamples (`G3`, `G4`, `G25`: link-only, path-only, capture, and readout-only without source refinement) yield `K = 0` and unrecoverable repairs.",
    "- **Paper 8 (`economic-constitution`)**: `docs/economic-constitution-reproduction.md` verifies 11 consumer programs (201 instances including 109 planning contracts/negative controls and compile-time `fail_if_success` mutation negative controls) and proves that past contribution tallies open no permanent rule gate (`ECN3`, `R2`, `R5`).",
    "- **Paper 9 (`capital-formation`)**: `docs/capital-formation-reproduction.md` and `papers/capital-formation/2026-11-04/source-excerpts/` pair the 5-condition positive structural theorem with 5 explicit formal counterexample models (including archive/zero-issuance counterexamples) proving that dropping any single condition forces collapse into capture or rent extraction (`R1–R18`).",
    "- **Paper 10 (`enforceable-peace`)**: `docs/enforceable-peace-reproduction.md` (`PE1–PE33`) pairs sustainable terminal settlement with formal negative controls across all 5 boundaries (judgment-proof liability erasure, unilateral zero-cost receipts, filibuster exit stalls, stealth capture without prepaid verification, and `< 3f+1` Byzantine quorum failure), verified against signed 4-machine journals (`python3 tools/enforceable_peace.py replay`).",
    "",
    "## Published Papers",
    "",
  ];
  for (const entry of ORDERED) {
    const en = paperOf(entry.slug, "en");
    const zh = paperOf(entry.slug, "zh");
    const stats = statsOf(entry.slug);
    lines.push(
      `### ${en.title} (${zh.title})`,
      `- Page (EN): https://h0mework.wiki/en/papers/${entry.slug}/`,
      `- Page (ZH): https://h0mework.wiki/papers/${entry.slug}/`,
      `- PDF (EN): https://h0mework.wiki${en.citation.pdfPath}`,
      `- PDF (ZH): https://h0mework.wiki${zh.citation.pdfPath}`,
      `- Zenodo DOI: https://doi.org/${en.current.doi}`,
      `- Published: ${en.current.date} (v${en.current.number})`,
      `- Formalization scope: ${stats.claims} claims, ${stats.modules} Lean modules, ${stats.declarations} declarations`,
      ...(en.current.sourceMap ? [`- Source Map (JSON): ${en.current.sourceMap}`] : []),
      `- Reproduction Guide: ${en.current.guide}`,
      `- Audit command: \`${en.current.check}\``,
      `- Keywords: ${en.citation.keywords.join(", ")}`,
      `- Abstract: ${en.citation.abstract}`,
      "",
    );
  }
  return new Response(lines.join("\n"), {
    headers: { "Content-Type": "text/plain; charset=utf-8" },
  });
};
