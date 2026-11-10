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
    "## Formal & Empirical Positive/Negative Controls (Anti-Vacuity & Physical Falsifiability)",
    "",
    "To prevent vacuous type inhabitation (`Unit` shells, zero-field shortcuts, or post-hoc parameter fitting), the repository pairs positive existence/derivation theorems with explicit formal negative controls (`¬ ...` / `iff` uniqueness / no-go theorems) and empirical positive/negative controls on public datasets:",
    "",
    "1. **Explicit Formal Vacuity No-Go Boundary**: `Lean/H0mework/Versions/Re60a8605/ReleaseMaterials/SaturationMonoid/PhysicsCore/ConstitutiveHardGateVacuityBoundary.lean` (`constitutiveHardGateVacuityBoundary`) proves that an untyped constitutive schema can be inhabited by `Unit`, motivating the strict dual-axis and exact-admission hard gates.",
    "2. **Exact Coframe Admission vs. Mismatched-Coframe Rejection + Nonseparability (`Δ_mix = 9 ≠ 0`)**: `Lean/H0mework/Physics/Coframe/NonseparableSourceCoframeRegression.lean` proves both the positive admission (`sourceNonseparableConfiguration_exactAdmission`), the nonseparability theorem (`gravityGaugeMixedDifference_eq_nine`, `nonseparableMasterAction_not_additively_separable` proving the action cannot split as `gravityOnly + gaugeOnly`), and the formal negative control (`mismatchedCoframeConfiguration_rejected`: a `timeModeProbe` coframe of the exact same Lean carrier type is formally rejected).",
    "3. **Bijective Standard Model Subalgebra Selection (`iff`)**: `Lean/H0mework/Physics/Lie/SU7MotherLieAlgebra.lean` (`selectedBySourceBreaking_iff_p286LieBlockImage`, `selected_entry_zero_of_breakingLevel_ne`) proves over 7x7 skew-adjoint traceless complex matrices that commutation with the source-generated `3+2+1+1` spectral order parameter plus 3 operational block-trace equations holds **if and only if** the matrix lies in `su(3) ⊕ su(2) ⊕ u(1)` (forcing all off-block entries to zero).",
    "4. **Einstein–Cartan–Torsion 4-Leg Critical Equivalence (`iff`) & Pure Symmetric Plebanski Refutation (`5/8 ≠ 0`)**: `Lean/H0mework/Physics/DualVariation/IIPlusTorsionSpinCriticalLocus.lean` (`diracDualFormNative_fourLegCriticalLocus_iff_reducedCoframeStationary_and_torsionSpin`) and `Lean/H0mework/Versions/Re60a8605/ReleaseMaterials/SaturationMonoid/PhysicsCore/StageNinePlebanskiExistingGravityMultiplierCompatibility.lean` prove 4-leg stationarity is equivalent to simplicity `B = II+(e)` + Einstein–Cartan balance + torsion–spin, while pure symmetric quadratic multipliers fail across the `Spin+(1,3)` orbit with pair-exchange defect `(4,3) - (3,4) = 5/16 - (-5/16) = 5/8 ≠ 0`.",
    "5. **Empirical Positive vs. Negative Controls on Public Loophole-Free Bell Archives (§10.2)**:",
    "   - **Negative Controls (Uncalibrated Nominal Locks Must Alarm)**: With zero tunable parameters, feeding an uncalibrated ideal nominal angle table on Storz et al. (100,000 superconducting trials) is decisively rejected (`log E = 46803.62`, `p_any ≈ 2.78e-20327`; the nominal table evaluates to `S = 0` under the experimenters' own CHSH sign convention); forcing a zero-error ideal detector onto the 20,403 Munich entangled-atom trials fails at April trial 3,974 (`E ≈ 494.85 > 40`); and in the naive two-mode NIST 2015 nominal replay (claim `P24`, `proved: false`), all 5 nominal parameters fall outside the predeclared band.",
    "   - **Positive Controls (Open-Instrument Readout & Recycling Closure)**: Incorporating genuine open losses, spontaneous recycling, and 12-state ionization detector fibres (`P31`, `P32`, `P35`, `P40`, `Physics.Bell.ReadoutDetectorFiber`, `Munich.ReadoutDomain.RegisteredDuhamelTail`) keeps all 20,403 Munich prefixes below threshold 40 (April peak `1`, June peak `1.3387`), matches 30 forward curves to 6 adjoint flows across the 120 ns gate within `1.301828e-21`, and yields strictly positive Clauser–Horne gain `CH_N5 > 1.3790e-6` across the NIST 2015 joint 95% domain.",
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
