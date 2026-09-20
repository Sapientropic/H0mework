import H0mework.Physics.RunningSources.P829
import H0mework.Physics.RepresentationSources.P835

/-!
# Proposition 836: spectrum-resolved alpha producer induces the representation law

P835 names the target object:

`SU7RepresentationAllowedSectorLaw`.

Its input is an `AlphaStrongConvergentCarrierNail`: exact `alpha_s` plus
same-carrier fixed-point convergence.

This file pushes the exact `alpha_s` side one layer lower.  The exact inverse
residual is read from the coordinatewise structural four-source vector of
P823/P829:

* SU(7)-breaking source: `89/10000`;
* threshold source: generated balanced trace `7 - 7`;
* RG source: generated loop/counterterm coordinates cancel;
* Higgs-extra source: generated incidence slots `6 - 6`.

The theorem below says that this spectrum-resolved alpha producer is the exact
alpha nail used by the representation allowed-sector bridge.  Once the shared
carrier convergence field is present, the allowed-sector law follows without a
new equivalence shell.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation
open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Spectrum-resolved exact alpha nail -/

/-- The exact inverse `alpha_s` nail read from the coordinatewise structural
four-source vector, not from the already-compressed independent vector. -/
def SpectrumResolvedAlphaExactInverseResidualNail : Prop :=
  inverseCorrectionFromAlphaGap
      (alphaStrongTwoLoopSMOutput ℚ)
      (∑ s : AlphaStrongResidualSource,
        alphaStrongCoordinatewiseStructuralFourSourceVector
          canonicalStructuralCarrierSmoothPhysicsSourceData s) =
    -((89000 : ℚ) / 128511)

/-- THEOREM 1: the spectrum-resolved coordinatewise producer gives the exact
inverse residual. -/
theorem spectrumResolvedAlphaExactInverseResidualNail :
    SpectrumResolvedAlphaExactInverseResidualNail :=
  alphaStrongCoordinatewiseStructuralProducer_outputs_residual

/-- THEOREM 2: the spectrum-resolved exact nail transports to the canonical
P819 alpha nail.  The transport is by the two proved generator equalities:

`coordinatewise structural vector = SU7 primitive vector = independent vector`.
-/
theorem spectrumResolvedAlphaExactInverseResidualNail_to_canonical
    (h : SpectrumResolvedAlphaExactInverseResidualNail) :
    GrandUnification.AlphaStrongExactInverseResidualNail := by
  unfold SpectrumResolvedAlphaExactInverseResidualNail at h
  unfold GrandUnification.AlphaStrongExactInverseResidualNail
  rw [← su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent,
    ← alphaStrongCoordinatewiseStructuralFourSourceVector_eq_primitive]
  exact h

/-- THEOREM 3: the canonical exact alpha nail can be read directly through the
spectrum-resolved producer. -/
theorem canonicalAlphaExactNail_from_spectrumResolvedProducer :
    GrandUnification.AlphaStrongExactInverseResidualNail :=
  spectrumResolvedAlphaExactInverseResidualNail_to_canonical
    spectrumResolvedAlphaExactInverseResidualNail

/-! ## Spectrum-resolved convergent alpha carrier -/

/-- Spectrum-resolved alpha convergence carrier.  The exact residual is
produced by the coordinatewise structural alpha sources; the remaining field is
the shared residual-carrier convergence needed by P819/P835. -/
structure SpectrumResolvedAlphaConvergentCarrier : Prop where
  exact_from_spectrum : SpectrumResolvedAlphaExactInverseResidualNail
  fixed_point_convergence :
    Nonempty AffineRelaxation.EvenGoldbachDynamicalFixedPointProducer

/-- THEOREM 4: the spectrum-resolved alpha carrier is an
`AlphaStrongConvergentCarrierNail`. -/
theorem alphaStrongConvergentCarrierNail_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    GrandUnification.AlphaStrongConvergentCarrierNail where
  exact_inverse_residual :=
    spectrumResolvedAlphaExactInverseResidualNail_to_canonical
      C.exact_from_spectrum
  fixed_point_convergence := C.fixed_point_convergence

/-- THEOREM 5: spectrum-resolved alpha convergence induces the SU(7)
representation allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_alphaStrongConvergentCarrierNail
    (alphaStrongConvergentCarrierNail_of_spectrumResolvedAlphaConvergentCarrier
      C)

/-- THEOREM 6: spectrum-resolved alpha convergence produces the trace-zero
prime-edge normal form on every even fiber. -/
noncomputable def traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier)
    (n : ℕ) (hn : 2 ≤ n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopOfRepresentationLaw
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
      C)
    n hn

/-- THEOREM 7: the normal form extracted from spectrum-resolved alpha
convergence has trace zero. -/
theorem traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier_trace_zero
    (C : SpectrumResolvedAlphaConvergentCarrier)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
          C n hn).leftPrime
        (traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
          C n hn).rightPrime) :=
  (traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
    C n hn).trace_zero

/-- THEOREM 8: spectrum-resolved alpha convergence produces the unit-bracket
producer. -/
theorem unitBracketProducer_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
      C)

/-- THEOREM 9: spectrum-resolved alpha convergence produces the dynamical
fixed-point producer. -/
noncomputable def fixedPointProducer_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    AffineRelaxation.EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
      C)

/-- THEOREM 10: spectrum-resolved alpha convergence produces the data-level
color-loop unit-bracket/fixed-point witness. -/
noncomputable def colorLoopWitness_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitness_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
      C)

/-! ## Certificate -/

/-- P836 certificate: the low-level spectrum/counterterm alpha producer has
been connected to the representation allowed-sector law. -/
structure SpectrumResolvedAlphaToRepresentationLawCertificate where
  spectrum_exact :
    SpectrumResolvedAlphaExactInverseResidualNail
  spectrum_exact_to_canonical :
    SpectrumResolvedAlphaExactInverseResidualNail ->
      GrandUnification.AlphaStrongExactInverseResidualNail
  convergent_carrier_to_alpha_nail :
    SpectrumResolvedAlphaConvergentCarrier ->
      GrandUnification.AlphaStrongConvergentCarrierNail
  convergent_carrier_to_representation_law :
    SpectrumResolvedAlphaConvergentCarrier ->
      SU7RepresentationAllowedSectorLaw
  convergent_carrier_to_trace_zero_normal_form :
    ∀ (_C : SpectrumResolvedAlphaConvergentCarrier)
      (n : ℕ) (_hn : 2 ≤ n),
      TraceZeroPrimeEdgeLoop n
  convergent_carrier_to_unit_bracket :
    SpectrumResolvedAlphaConvergentCarrier ->
      ColorLoopTraceUnitBracketProducer
  convergent_carrier_to_fixed_point :
    SpectrumResolvedAlphaConvergentCarrier ->
      AffineRelaxation.EvenGoldbachDynamicalFixedPointProducer
  convergent_carrier_to_witness :
    SpectrumResolvedAlphaConvergentCarrier ->
      ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 11: canonical P836 certificate. -/
def spectrumResolvedAlphaToRepresentationLawCertificate :
    SpectrumResolvedAlphaToRepresentationLawCertificate where
  spectrum_exact :=
    spectrumResolvedAlphaExactInverseResidualNail
  spectrum_exact_to_canonical :=
    spectrumResolvedAlphaExactInverseResidualNail_to_canonical
  convergent_carrier_to_alpha_nail :=
    alphaStrongConvergentCarrierNail_of_spectrumResolvedAlphaConvergentCarrier
  convergent_carrier_to_representation_law :=
    su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier
  convergent_carrier_to_trace_zero_normal_form :=
    traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
  convergent_carrier_to_unit_bracket :=
    unitBracketProducer_of_spectrumResolvedAlphaConvergentCarrier
  convergent_carrier_to_fixed_point :=
    fixedPointProducer_of_spectrumResolvedAlphaConvergentCarrier
  convergent_carrier_to_witness :=
    colorLoopWitness_of_spectrumResolvedAlphaConvergentCarrier

end StandardModelConstraint
end SaturationMonoid
