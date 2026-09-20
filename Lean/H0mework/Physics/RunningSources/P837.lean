import H0mework.Physics.AlphaSpectrum.P836

/-!
# Proposition 837: spectrum alpha convergence is SU(7) confinement

P836 made the exact `alpha_s` side spectrum-resolved, but its bridge object
still carried the shared fixed-point convergence field:

`SpectrumResolvedAlphaConvergentCarrier`.

This file removes that field as an external-looking input.  P834 already
proved that the SU(7) residual-split confinement law produces the data-level
fixed-point producer.  Therefore confinement itself supplies the remaining
carrier convergence needed by P836.

The main result is the tight equivalence:

`SpectrumResolvedAlphaConvergentCarrier ↔ SU7ConfinementResidualSplitLaw`

and, through P835:

`SpectrumResolvedAlphaConvergentCarrier ↔ SU7RepresentationAllowedSectorLaw`.

Thus the current throat is not "alpha exactness plus an unexplained fixed
point"; it is:

`spectrum-resolved alpha exactness + SU(7) confinement/representation law`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Confinement supplies the spectrum-resolved alpha carrier -/

/-- THEOREM 1: the residual-split SU(7) confinement law supplies the remaining
fixed-point convergence field of the spectrum-resolved alpha carrier. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SpectrumResolvedAlphaConvergentCarrier where
  exact_from_spectrum :=
    spectrumResolvedAlphaExactInverseResidualNail
  fixed_point_convergence :=
    ⟨fixedPointProducer_of_confinementResidualSplitLaw L⟩

/-- THEOREM 2: the representation allowed-sector law also supplies the
spectrum-resolved alpha carrier, because it already produces the fixed-point
producer by P835. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    SpectrumResolvedAlphaConvergentCarrier where
  exact_from_spectrum :=
    spectrumResolvedAlphaExactInverseResidualNail
  fixed_point_convergence :=
    ⟨fixedPointProducer_of_su7RepresentationAllowedSectorLaw L⟩

/-- THEOREM 3: spectrum-resolved alpha convergence induces residual-split
SU(7) confinement. -/
theorem confinementResidualSplitLaw_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
      C)

/-- THEOREM 4: spectrum-resolved alpha convergence is exactly SU(7)
residual-split confinement. -/
theorem spectrumResolvedAlphaConvergentCarrier_iff_confinementResidualSplitLaw :
    SpectrumResolvedAlphaConvergentCarrier ↔
      SU7ConfinementResidualSplitLaw := by
  constructor
  · exact confinementResidualSplitLaw_of_spectrumResolvedAlphaConvergentCarrier
  · exact spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw

/-- THEOREM 5: spectrum-resolved alpha convergence is exactly the SU(7)
representation allowed-sector law. -/
theorem spectrumResolvedAlphaConvergentCarrier_iff_su7RepresentationAllowedSectorLaw :
    SpectrumResolvedAlphaConvergentCarrier ↔
      SU7RepresentationAllowedSectorLaw := by
  constructor
  · exact su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
  · exact spectrumResolvedAlphaConvergentCarrier_of_su7RepresentationAllowedSectorLaw

/-! ## Direct readouts from confinement through the spectrum alpha bridge -/

/-- THEOREM 6: residual-split confinement produces the P819 alpha convergent
carrier nail through the spectrum-resolved alpha bridge. -/
theorem alphaStrongConvergentCarrierNail_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    GrandUnification.AlphaStrongConvergentCarrierNail :=
  alphaStrongConvergentCarrierNail_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)

/-- THEOREM 7: residual-split confinement produces the representation law
through the spectrum-resolved alpha bridge. -/
theorem su7RepresentationAllowedSectorLaw_of_confinementResidualSplitLaw_via_spectrumAlpha
    (L : SU7ConfinementResidualSplitLaw) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)

/-- THEOREM 8: residual-split confinement produces the trace-zero prime-edge
normal form through the spectrum-resolved alpha bridge. -/
noncomputable def traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha
    (L : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)
    n hn

/-- THEOREM 9: the spectrum-alpha route from confinement still has trace zero
on every even fiber. -/
theorem traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha_trace_zero
    (L : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha
          L n hn).leftPrime
        (traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha
          L n hn).rightPrime) :=
  (traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha
    L n hn).trace_zero

/-- THEOREM 10: residual-split confinement produces the unit bracket through
the spectrum-resolved alpha bridge. -/
theorem unitBracketProducer_of_confinementResidualSplitLaw_via_spectrumAlpha
    (L : SU7ConfinementResidualSplitLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)

/-- THEOREM 11: residual-split confinement produces the fixed-point producer
through the spectrum-resolved alpha bridge. -/
noncomputable def fixedPointProducer_of_confinementResidualSplitLaw_via_spectrumAlpha
    (L : SU7ConfinementResidualSplitLaw) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)

/-- THEOREM 12: residual-split confinement produces the data-level color-loop
witness through the spectrum-resolved alpha bridge. -/
noncomputable def colorLoopWitness_of_confinementResidualSplitLaw_via_spectrumAlpha
    (L : SU7ConfinementResidualSplitLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitness_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw L)

/-! ## Certificate -/

/-- P837 certificate: the fixed-point convergence field in P836 has been
identified with SU(7) residual-split confinement and the representation
allowed-sector law. -/
structure SpectrumAlphaConfinementEquivalenceCertificate where
  spectrum_alpha_iff_confinement :
    SpectrumResolvedAlphaConvergentCarrier ↔
      SU7ConfinementResidualSplitLaw
  spectrum_alpha_iff_representation_law :
    SpectrumResolvedAlphaConvergentCarrier ↔
      SU7RepresentationAllowedSectorLaw
  confinement_to_spectrum_alpha :
    SU7ConfinementResidualSplitLaw ->
      SpectrumResolvedAlphaConvergentCarrier
  representation_law_to_spectrum_alpha :
    SU7RepresentationAllowedSectorLaw ->
      SpectrumResolvedAlphaConvergentCarrier
  spectrum_alpha_to_confinement :
    SpectrumResolvedAlphaConvergentCarrier ->
      SU7ConfinementResidualSplitLaw
  confinement_to_alpha_nail :
    SU7ConfinementResidualSplitLaw ->
      GrandUnification.AlphaStrongConvergentCarrierNail
  confinement_to_representation_law :
    SU7ConfinementResidualSplitLaw ->
      SU7RepresentationAllowedSectorLaw
  confinement_to_trace_zero_normal_form :
    ∀ (_L : SU7ConfinementResidualSplitLaw)
      (n : ℕ) (_hn : 2 ≤ n),
      TraceZeroPrimeEdgeLoop n
  confinement_to_unit_bracket :
    SU7ConfinementResidualSplitLaw ->
      ColorLoopTraceUnitBracketProducer
  confinement_to_fixed_point :
    SU7ConfinementResidualSplitLaw ->
      EvenGoldbachDynamicalFixedPointProducer
  confinement_to_witness :
    SU7ConfinementResidualSplitLaw ->
      ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 13: canonical P837 certificate. -/
def spectrumAlphaConfinementEquivalenceCertificate :
    SpectrumAlphaConfinementEquivalenceCertificate where
  spectrum_alpha_iff_confinement :=
    spectrumResolvedAlphaConvergentCarrier_iff_confinementResidualSplitLaw
  spectrum_alpha_iff_representation_law :=
    spectrumResolvedAlphaConvergentCarrier_iff_su7RepresentationAllowedSectorLaw
  confinement_to_spectrum_alpha :=
    spectrumResolvedAlphaConvergentCarrier_of_confinementResidualSplitLaw
  representation_law_to_spectrum_alpha :=
    spectrumResolvedAlphaConvergentCarrier_of_su7RepresentationAllowedSectorLaw
  spectrum_alpha_to_confinement :=
    confinementResidualSplitLaw_of_spectrumResolvedAlphaConvergentCarrier
  confinement_to_alpha_nail :=
    alphaStrongConvergentCarrierNail_of_confinementResidualSplitLaw
  confinement_to_representation_law :=
    su7RepresentationAllowedSectorLaw_of_confinementResidualSplitLaw_via_spectrumAlpha
  confinement_to_trace_zero_normal_form :=
    traceZeroPrimeEdgeLoopOfConfinementResidualSplitLaw_via_spectrumAlpha
  confinement_to_unit_bracket :=
    unitBracketProducer_of_confinementResidualSplitLaw_via_spectrumAlpha
  confinement_to_fixed_point :=
    fixedPointProducer_of_confinementResidualSplitLaw_via_spectrumAlpha
  confinement_to_witness :=
    colorLoopWitness_of_confinementResidualSplitLaw_via_spectrumAlpha


end StandardModelConstraint
end SaturationMonoid
