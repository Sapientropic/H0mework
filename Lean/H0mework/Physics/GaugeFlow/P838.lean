import H0mework.Physics.RunningSources.P837

/-!
# Proposition 838: primitive SU(7) gauge dynamics normal form

P837 identified the P836 convergence field with SU(7) residual-split
confinement and the representation allowed-sector law.

This file exposes the primitive gauge-dynamics object underneath that
confinement law.  It has two coordinates:

* local normal form: the SU(7) color-adjoint filter is exactly trace zero;
* global dynamics: permanent color holonomy is forbidden.

The first coordinate is the P818 representation/filter theorem.  The second is
the gauge-dynamical prohibition.  Together they generate:

`confinement -> spectrum alpha convergence -> representation law
 -> no-gap -> unit bracket -> fixed point`.

This makes the remaining producer primitive explicit: prove the global
no-permanent-color-holonomy field from still-lower SU(7) gauge dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Primitive gauge dynamics normal form -/

/-- Primitive SU(7) gauge dynamics normal-form law.

The local coordinate says "allowed = trace-zero".  The global coordinate says
that the gauge dynamics admits no permanent color holonomy. -/
structure SU7PrimitiveGaugeDynamicsNormalFormLaw : Prop where
  filter_iff_trace_zero :
    ∀ M : ColorLoopField,
      SU7ColorAdjointRepresentationFilter M ↔
        ColorLoopTraceExact M
  no_permanent_color_holonomy :
    ¬ PermanentPrimeEdgeColorHolonomy

/-- THEOREM 1: any primitive gauge dynamics law forbids every residual-split
permanent holonomy readout. -/
theorem primitiveGaugeDynamics_forbids_residualSplitPermanent
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      ¬ ColorLoopResidualSplitPermanentHolonomy sigma := by
  intro sigma hsigma
  exact
    (noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
      sigma hsigma).mpr G.no_permanent_color_holonomy

/-- THEOREM 2: primitive SU(7) gauge dynamics induces the residual-split
confinement law. -/
theorem confinementResidualSplitLaw_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7ConfinementResidualSplitLaw where
  forbids_residual_split_permanent :=
    primitiveGaugeDynamics_forbids_residualSplitPermanent G

/-- THEOREM 3: residual-split confinement induces the primitive gauge dynamics
normal-form law.  The local filter normal form is the SU(7) representation
theorem; the global field is read from confinement as no permanent color
holonomy. -/
theorem primitiveGaugeDynamics_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7PrimitiveGaugeDynamicsNormalFormLaw where
  filter_iff_trace_zero :=
    su7ColorAdjointRepresentationFilter_iff_traceExact
  no_permanent_color_holonomy :=
    noPermanentColorHolonomy_of_confinementResidualSplitLaw L

/-- THEOREM 4: primitive gauge dynamics is exactly residual-split
confinement. -/
theorem primitiveGaugeDynamics_iff_confinementResidualSplitLaw :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7ConfinementResidualSplitLaw := by
  constructor
  · exact confinementResidualSplitLaw_of_primitiveGaugeDynamics
  · exact primitiveGaugeDynamics_of_confinementResidualSplitLaw

/-- THEOREM 5: primitive gauge dynamics is exactly spectrum-resolved alpha
convergence. -/
theorem primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SpectrumResolvedAlphaConvergentCarrier := by
  exact
    primitiveGaugeDynamics_iff_confinementResidualSplitLaw.trans
      spectrumResolvedAlphaConvergentCarrier_iff_confinementResidualSplitLaw.symm

/-- THEOREM 6: primitive gauge dynamics is exactly the SU(7) representation
allowed-sector law. -/
theorem primitiveGaugeDynamics_iff_su7RepresentationAllowedSectorLaw :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7RepresentationAllowedSectorLaw := by
  exact
    primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier.trans
      spectrumResolvedAlphaConvergentCarrier_iff_su7RepresentationAllowedSectorLaw

/-! ## Direct readouts from primitive gauge dynamics -/

/-- THEOREM 7: primitive gauge dynamics produces the spectrum-resolved alpha
convergent carrier. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SpectrumResolvedAlphaConvergentCarrier :=
  primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier.mp G

/-- THEOREM 8: primitive gauge dynamics produces the P819 alpha convergent
carrier nail. -/
theorem alphaStrongConvergentCarrierNail_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    GrandUnification.AlphaStrongConvergentCarrierNail :=
  alphaStrongConvergentCarrierNail_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics G)

/-- THEOREM 9: primitive gauge dynamics produces the representation
allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7RepresentationAllowedSectorLaw :=
  primitiveGaugeDynamics_iff_su7RepresentationAllowedSectorLaw.mp G

/-- THEOREM 10: primitive gauge dynamics produces no-gap. -/
theorem primeEdgeTraceSpectrumNoGap_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    PrimeEdgeTraceSpectrumNoGap :=
  primeEdgeTraceSpectrumNoGap_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_primitiveGaugeDynamics G)

/-- THEOREM 11: primitive gauge dynamics produces the trace-zero normal form
on every even fiber. -/
noncomputable def traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopOfSpectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics G)
    n hn

/-- THEOREM 12: the primitive-gauge normal form has trace zero. -/
theorem traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics_trace_zero
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics G n hn).leftPrime
        (traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics G n hn).rightPrime) :=
  (traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics G n hn).trace_zero

/-- THEOREM 13: primitive gauge dynamics produces the unit bracket. -/
theorem unitBracketProducer_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics G)

/-- THEOREM 14: primitive gauge dynamics produces the fixed-point producer. -/
noncomputable def fixedPointProducer_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics G)

/-- THEOREM 15: primitive gauge dynamics produces the data-level color-loop
unit-bracket/fixed-point witness. -/
noncomputable def colorLoopWitness_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitness_of_spectrumResolvedAlphaConvergentCarrier
    (spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics G)

/-! ## Certificate -/

/-- P838 certificate: primitive gauge dynamics normal form is the same target
as confinement, spectrum-resolved alpha convergence, and representation law,
and it produces no-gap / unit bracket / fixed point. -/
structure PrimitiveGaugeDynamicsNormalFormCertificate where
  primitive_iff_confinement :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7ConfinementResidualSplitLaw
  primitive_iff_spectrum_alpha :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SpectrumResolvedAlphaConvergentCarrier
  primitive_iff_representation_law :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7RepresentationAllowedSectorLaw
  primitive_forbids_residual_split_permanent :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      ∀ sigma : ℝ, sigma ≠ 0 ->
        ¬ ColorLoopResidualSplitPermanentHolonomy sigma
  primitive_to_alpha_nail :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      GrandUnification.AlphaStrongConvergentCarrierNail
  primitive_to_no_gap :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      PrimeEdgeTraceSpectrumNoGap
  primitive_to_trace_zero_normal_form :
    ∀ (_G : SU7PrimitiveGaugeDynamicsNormalFormLaw)
      (n : ℕ) (_hn : 2 ≤ n),
      TraceZeroPrimeEdgeLoop n
  primitive_to_unit_bracket :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      ColorLoopTraceUnitBracketProducer
  primitive_to_fixed_point :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      EvenGoldbachDynamicalFixedPointProducer
  primitive_to_witness :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 16: canonical P838 primitive gauge dynamics certificate. -/
def primitiveGaugeDynamicsNormalFormCertificate :
    PrimitiveGaugeDynamicsNormalFormCertificate where
  primitive_iff_confinement :=
    primitiveGaugeDynamics_iff_confinementResidualSplitLaw
  primitive_iff_spectrum_alpha :=
    primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier
  primitive_iff_representation_law :=
    primitiveGaugeDynamics_iff_su7RepresentationAllowedSectorLaw
  primitive_forbids_residual_split_permanent :=
    primitiveGaugeDynamics_forbids_residualSplitPermanent
  primitive_to_alpha_nail :=
    alphaStrongConvergentCarrierNail_of_primitiveGaugeDynamics
  primitive_to_no_gap :=
    primeEdgeTraceSpectrumNoGap_of_primitiveGaugeDynamics
  primitive_to_trace_zero_normal_form :=
    traceZeroPrimeEdgeLoopOfPrimitiveGaugeDynamics
  primitive_to_unit_bracket :=
    unitBracketProducer_of_primitiveGaugeDynamics
  primitive_to_fixed_point :=
    fixedPointProducer_of_primitiveGaugeDynamics
  primitive_to_witness :=
    colorLoopWitness_of_primitiveGaugeDynamics


end StandardModelConstraint
end SaturationMonoid
