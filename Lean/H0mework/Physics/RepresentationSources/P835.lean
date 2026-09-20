import H0mework.Physics.BranchSources.P834

/-!
# Proposition 835: representation allowed-sector law

P832 proved the fiber normal form:

`SU7AllowedPrimeEdgeLoop n ≃ TraceZeroPrimeEdgeLoop n`.

P833 made the global allowed sector a data object.

P834 named confinement as a residual-split no-holonomy law.

This file names the representation-theoretic producer that sits below those
readouts.  A SU(7) representation allowed-sector law says:

* the color-adjoint filter is the trace-zero fiber of the color-loop
  observable;
* every even fiber has a prime-edge representative passing that filter.

Lean then extracts the whole target:

`representation law -> allowed sector -> confinement residual-split law
 -> no-gap -> unit bracket -> fixed point`.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## Representation law for the allowed sector -/

/-- SU(7) representation allowed-sector law.  This is the global
representation/filter object: the color-adjoint filter is the trace-zero
normal-form condition, and every even prime-edge fiber has an allowed
representative. -/
structure SU7RepresentationAllowedSectorLaw : Prop where
  filter_iff_trace_zero :
    ∀ M : ColorLoopField,
      SU7ColorAdjointRepresentationFilter M ↔
        ColorLoopTraceExact M
  allowed_representative :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ p q : AffineRelaxation.PrimeExponent,
        SU7ColorAdjointRepresentationFilter
          (primeEdgeColorLoopMatrix n p q)

/-- THEOREM 1: the proposition-level SU(7 filtered producer induces the
representation allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_filteredProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7RepresentationAllowedSectorLaw where
  filter_iff_trace_zero :=
    su7ColorAdjointRepresentationFilter_iff_traceExact
  allowed_representative := P

/-- THEOREM 2: the representation allowed-sector law extracts the
proposition-level SU(7 filtered producer. -/
theorem su7FilteredProducer_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    SU7FilteredPrimeEdgeLoopProducer :=
  L.allowed_representative

/-- THEOREM 3: the representation allowed-sector law is exactly the
SU(7-filtered prime-edge producer. -/
theorem su7RepresentationAllowedSectorLaw_iff_filteredProducer :
    SU7RepresentationAllowedSectorLaw ↔
      SU7FilteredPrimeEdgeLoopProducer := by
  constructor
  · exact su7FilteredProducer_of_su7RepresentationAllowedSectorLaw
  · exact su7RepresentationAllowedSectorLaw_of_filteredProducer

/-! ## Data-level normal form extracted from the representation law -/

/-- THEOREM 4: the representation law produces the global allowed-sector data
object. -/
noncomputable def su7AllowedPrimeEdgeSectorOfRepresentationLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    SU7AllowedPrimeEdgeSector :=
  su7AllowedPrimeEdgeSectorOfFilteredProducer
    (su7FilteredProducer_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 5: the representation law produces the fiberwise trace-zero normal
form. -/
noncomputable def traceZeroPrimeEdgeLoopOfRepresentationLaw
    (L : SU7RepresentationAllowedSectorLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    TraceZeroPrimeEdgeLoop n :=
  (su7AllowedPrimeEdgeSectorNormalForm
    (su7AllowedPrimeEdgeSectorOfRepresentationLaw L)).loop n hn

/-- THEOREM 6: the representation-law normal form has trace zero on every
even fiber. -/
theorem traceZeroPrimeEdgeLoopOfRepresentationLaw_trace_zero
    (L : SU7RepresentationAllowedSectorLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (traceZeroPrimeEdgeLoopOfRepresentationLaw L n hn).leftPrime
        (traceZeroPrimeEdgeLoopOfRepresentationLaw L n hn).rightPrime) :=
  (traceZeroPrimeEdgeLoopOfRepresentationLaw L n hn).trace_zero

/-- THEOREM 7: the representation-law allowed sector still carries the
SU(7 color-adjoint filter before normal-form readout. -/
theorem su7AllowedPrimeEdgeSectorOfRepresentationLaw_allowed
    (L : SU7RepresentationAllowedSectorLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7ColorAdjointRepresentationFilter
      (primeEdgeColorLoopMatrix n
        ((su7AllowedPrimeEdgeSectorOfRepresentationLaw L).loop n hn).leftPrime
        ((su7AllowedPrimeEdgeSectorOfRepresentationLaw L).loop n hn).rightPrime) :=
  ((su7AllowedPrimeEdgeSectorOfRepresentationLaw L).loop n hn).allowed

/-- THEOREM 8: nonempty allowed-sector data is exactly the representation law.
-/
theorem su7RepresentationAllowedSectorLaw_iff_allowedSector :
    SU7RepresentationAllowedSectorLaw ↔
      Nonempty SU7AllowedPrimeEdgeSector := by
  exact
    su7RepresentationAllowedSectorLaw_iff_filteredProducer.trans
      nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.symm

/-- THEOREM 9: allowed-sector data induces the representation law. -/
theorem su7RepresentationAllowedSectorLaw_of_allowedSector
    (S : SU7AllowedPrimeEdgeSector) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_iff_allowedSector.mpr ⟨S⟩

/-! ## Confinement and witness readouts -/

/-- THEOREM 10: the representation allowed-sector law induces the P834
residual-split confinement law. -/
theorem confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_su7FilteredProducer
    (su7FilteredProducer_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 11: the P834 confinement residual-split law induces the
representation allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_filteredProducer
    (su7FilteredProducer_of_confinementResidualSplitLaw L)

/-- THEOREM 12: representation law and residual-split confinement law are the
same producer target. -/
theorem su7RepresentationAllowedSectorLaw_iff_confinementResidualSplitLaw :
    SU7RepresentationAllowedSectorLaw ↔
      SU7ConfinementResidualSplitLaw := by
  constructor
  · exact confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw
  · exact su7RepresentationAllowedSectorLaw_of_confinementResidualSplitLaw

/-- THEOREM 13: the representation law produces no-gap. -/
theorem primeEdgeTraceSpectrumNoGap_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    PrimeEdgeTraceSpectrumNoGap :=
  primeEdgeTraceSpectrumNoGap_of_confinementResidualSplitLaw
    (confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 14: the representation law produces the unit-bracket producer. -/
theorem unitBracketProducer_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_confinementResidualSplitLaw
    (confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 15: the representation law produces the fixed-point producer. -/
noncomputable def fixedPointProducer_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_confinementResidualSplitLaw
    (confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 16: the representation law produces the data-level color-loop
unit-bracket/fixed-point witness. -/
noncomputable def colorLoopWitness_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfConfinementResidualSplitLaw
    (confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw L)

/-- THEOREM 17: the alpha-convergent carrier nail induces the representation
allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_alphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_filteredProducer
    (su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail H)

/-! ## Certificate -/

/-- P835 certificate: the allowed-sector algebra has been pushed down to the
representation/filter law object.  The law produces allowed-sector data,
trace-zero normal forms, residual-split confinement, no-gap, unit bracket, and
fixed point. -/
structure SU7RepresentationAllowedSectorLawCertificate where
  law_iff_filtered :
    SU7RepresentationAllowedSectorLaw ↔
      SU7FilteredPrimeEdgeLoopProducer
  law_iff_allowed_sector :
    SU7RepresentationAllowedSectorLaw ↔
      Nonempty SU7AllowedPrimeEdgeSector
  law_iff_confinement :
    SU7RepresentationAllowedSectorLaw ↔
      SU7ConfinementResidualSplitLaw
  law_to_allowed_sector :
    SU7RepresentationAllowedSectorLaw -> SU7AllowedPrimeEdgeSector
  law_to_trace_zero_normal_form :
    ∀ (_L : SU7RepresentationAllowedSectorLaw)
      (n : ℕ) (_hn : 2 ≤ n),
      TraceZeroPrimeEdgeLoop n
  law_to_confinement :
    SU7RepresentationAllowedSectorLaw -> SU7ConfinementResidualSplitLaw
  law_to_no_gap :
    SU7RepresentationAllowedSectorLaw -> PrimeEdgeTraceSpectrumNoGap
  law_to_unit_bracket :
    SU7RepresentationAllowedSectorLaw -> ColorLoopTraceUnitBracketProducer
  law_to_fixed_point :
    SU7RepresentationAllowedSectorLaw -> EvenGoldbachDynamicalFixedPointProducer
  law_to_witness :
    SU7RepresentationAllowedSectorLaw -> ColorLoopUnitBracketFixedPointWitness
  alpha_nail_to_law :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      SU7RepresentationAllowedSectorLaw

/-- THEOREM 18: canonical representation allowed-sector law certificate. -/
def su7RepresentationAllowedSectorLawCertificate :
    SU7RepresentationAllowedSectorLawCertificate where
  law_iff_filtered :=
    su7RepresentationAllowedSectorLaw_iff_filteredProducer
  law_iff_allowed_sector :=
    su7RepresentationAllowedSectorLaw_iff_allowedSector
  law_iff_confinement :=
    su7RepresentationAllowedSectorLaw_iff_confinementResidualSplitLaw
  law_to_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfRepresentationLaw
  law_to_trace_zero_normal_form :=
    traceZeroPrimeEdgeLoopOfRepresentationLaw
  law_to_confinement :=
    confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw
  law_to_no_gap :=
    primeEdgeTraceSpectrumNoGap_of_su7RepresentationAllowedSectorLaw
  law_to_unit_bracket :=
    unitBracketProducer_of_su7RepresentationAllowedSectorLaw
  law_to_fixed_point :=
    fixedPointProducer_of_su7RepresentationAllowedSectorLaw
  law_to_witness :=
    colorLoopWitness_of_su7RepresentationAllowedSectorLaw
  alpha_nail_to_law :=
    su7RepresentationAllowedSectorLaw_of_alphaStrongConvergentCarrierNail

end StandardModelConstraint
end SaturationMonoid
