import H0mework.Physics.GaugeFlow.P832

/-!
# Proposition 833: SU(7) allowed-sector producer

P832 proved the canonical normal form:

`SU7AllowedPrimeEdgeLoop n ≃ TraceZeroPrimeEdgeLoop n`.

This file pushes the producer target down to that object.  A
`SU7FilteredPrimeEdgeLoopProducer` no longer merely proves a proposition or
feeds a selector shell: it produces a global `SU7AllowedPrimeEdgeSector`.
The selector, trace-zero normal form, unit bracket, and fixed-point witness are
readouts of that allowed-sector data.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## Producing the allowed sector itself -/

/-- Build the global SU(7) allowed sector from the proposition-level filtered
producer.  This is the data-level form of the producer: each even fiber gets a
concrete allowed prime-edge loop before any selector/witness readout. -/
noncomputable def su7AllowedPrimeEdgeSectorOfFilteredProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7AllowedPrimeEdgeSector where
  loop := by
    intro n hn
    let p : AffineRelaxation.PrimeExponent := Classical.choose (P n hn)
    let q : AffineRelaxation.PrimeExponent :=
      Classical.choose (Classical.choose_spec (P n hn))
    exact
      { leftPrime := p
        rightPrime := q
        allowed := Classical.choose_spec (Classical.choose_spec (P n hn)) }

/-- THEOREM 1: the allowed sector constructed from a filtered producer carries
the SU(7) filter on every selected fiber. -/
theorem su7AllowedPrimeEdgeSectorOfFilteredProducer_allowed
    (P : SU7FilteredPrimeEdgeLoopProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7ColorAdjointRepresentationFilter
      (primeEdgeColorLoopMatrix n
        ((su7AllowedPrimeEdgeSectorOfFilteredProducer P).loop n hn).leftPrime
        ((su7AllowedPrimeEdgeSectorOfFilteredProducer P).loop n hn).rightPrime) :=
  ((su7AllowedPrimeEdgeSectorOfFilteredProducer P).loop n hn).allowed

/-- THEOREM 2: normalizing the produced allowed sector lands in trace-zero
fiber on every even input. -/
theorem su7AllowedPrimeEdgeSectorOfFilteredProducer_normalForm_trace_zero
    (P : SU7FilteredPrimeEdgeLoopProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfFilteredProducer P)).loop n hn).leftPrime
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfFilteredProducer P)).loop n hn).rightPrime) :=
  ((su7AllowedPrimeEdgeSectorNormalForm
    (su7AllowedPrimeEdgeSectorOfFilteredProducer P)).loop n hn).trace_zero

/-- THEOREM 3: the filtered producer is exactly nonempty allowed-sector data. -/
theorem nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      SU7FilteredPrimeEdgeLoopProducer := by
  constructor
  · rintro ⟨S⟩
    intro n hn
    exact
      ⟨(S.loop n hn).leftPrime,
        (S.loop n hn).rightPrime,
        (S.loop n hn).allowed⟩
  · intro P
    exact ⟨su7AllowedPrimeEdgeSectorOfFilteredProducer P⟩

/-- THEOREM 4: the allowed-sector object is exactly the selector object, but
the allowed sector is lower-level: it contains the loop and filter before the
selector is read. -/
theorem nonemptyAllowedPrimeEdgeSector_iff_confinementSelector :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      Nonempty SU7ConfinementPrimeEdgeSelector := by
  exact
    nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.trans
      nonemptyConfinementSelector_iff_su7FilteredProducer.symm

/-- THEOREM 5: the allowed-sector object is exactly the alpha convergence
nail. -/
theorem nonemptyAllowedPrimeEdgeSector_iff_alphaStrongConvergentCarrierNail :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      GrandUnification.AlphaStrongConvergentCarrierNail := by
  exact
    nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.trans
      alphaStrongConvergentCarrierNail_iff_su7FilteredProducer.symm

/-- THEOREM 6: the allowed-sector object is exactly the color-loop
unit-bracket producer. -/
theorem nonemptyAllowedPrimeEdgeSector_iff_unitBracketProducer :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      ColorLoopTraceUnitBracketProducer := by
  exact
    nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.trans
      su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer

/-- THEOREM 7: the allowed-sector object is exactly the fixed-point witness
producer. -/
theorem nonemptyAllowedPrimeEdgeSector_iff_fixedPointProducer :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  exact
    nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.trans
      su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer

/-! ## Producing allowed sectors from convergence/no-holonomy inputs -/

/-- THEOREM 8: no permanent color holonomy produces the allowed sector data. -/
noncomputable def su7AllowedPrimeEdgeSectorOfNoPermanentHolonomy
    (hno : ¬ PermanentPrimeEdgeColorHolonomy) :
    SU7AllowedPrimeEdgeSector :=
  su7AllowedPrimeEdgeSectorOfFilteredProducer
    ((noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mp hno)

/-- THEOREM 9: an alpha-convergent carrier nail produces the allowed sector
data, not merely a propositional witness. -/
noncomputable def su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    SU7AllowedPrimeEdgeSector :=
  su7AllowedPrimeEdgeSectorOfFilteredProducer
    (su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail H)

/-- THEOREM 10: if the exact alpha residual requires carrier convergence, then
it produces the allowed sector data. -/
noncomputable def su7AllowedPrimeEdgeSectorOfAlphaRequiresConvergence
    (hreq : GrandUnification.AlphaStrongExactResidualRequiresCarrierConvergence) :
    SU7AllowedPrimeEdgeSector :=
  su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail
    (GrandUnification.alphaStrongConvergentCarrierNail_of_requiresConvergence
      hreq)

/-- THEOREM 11: the alpha-generated allowed sector normalizes to trace-zero
on every even fiber. -/
theorem su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail_trace_zero
    (H : GrandUnification.AlphaStrongConvergentCarrierNail)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H)).loop
            n hn).leftPrime
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H)).loop
            n hn).rightPrime) :=
  ((su7AllowedPrimeEdgeSectorNormalForm
    (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H)).loop
      n hn).trace_zero

/-- THEOREM 12: reading the selector from the alpha-generated allowed sector
uses the same prime-edge endpoints as the allowed-sector normal form. -/
theorem confinementSelectorOfAlphaAllowedSector_pick_eq
    (H : GrandUnification.AlphaStrongConvergentCarrierNail)
    (n : ℕ) (hn : 2 ≤ n) :
    (confinementSelectorOfAllowedPrimeEdgeSector
      (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H)).pick
        n hn =
      (((su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H).loop
          n hn).leftPrime,
        ((su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H).loop
          n hn).rightPrime) :=
  confinementSelectorOfAllowedPrimeEdgeSector_pick_eq
    (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H) n hn

/-- THEOREM 13: the alpha-generated allowed sector directly extracts the
unit-bracket/fixed-point witness object. -/
noncomputable def colorLoopWitnessOfAlphaAllowedSector
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfAllowedPrimeEdgeSector
    (su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail H)

/-! ## Certificate -/

/-- P833 certificate: the producer target is the allowed-sector normal-form
object itself.  Filtered producers, no-holonomy, and alpha convergence all
produce `SU7AllowedPrimeEdgeSector`; selector/witness data are readouts. -/
structure SU7AllowedSectorProducerCertificate where
  allowed_sector_iff_filtered :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      SU7FilteredPrimeEdgeLoopProducer
  allowed_sector_iff_selector :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      Nonempty SU7ConfinementPrimeEdgeSelector
  allowed_sector_iff_alpha_nail :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      GrandUnification.AlphaStrongConvergentCarrierNail
  allowed_sector_iff_unit_bracket :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      ColorLoopTraceUnitBracketProducer
  allowed_sector_iff_fixed_point :
    Nonempty SU7AllowedPrimeEdgeSector ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  filtered_producer_to_allowed_sector :
    SU7FilteredPrimeEdgeLoopProducer -> SU7AllowedPrimeEdgeSector
  no_holonomy_to_allowed_sector :
    (¬ PermanentPrimeEdgeColorHolonomy) -> SU7AllowedPrimeEdgeSector
  alpha_nail_to_allowed_sector :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      SU7AllowedPrimeEdgeSector
  alpha_requires_convergence_to_allowed_sector :
    GrandUnification.AlphaStrongExactResidualRequiresCarrierConvergence ->
      SU7AllowedPrimeEdgeSector
  allowed_sector_extracts_selector :
    SU7AllowedPrimeEdgeSector -> SU7ConfinementPrimeEdgeSelector
  allowed_sector_extracts_witness :
    SU7AllowedPrimeEdgeSector -> ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 14: canonical SU(7) allowed-sector producer certificate. -/
def su7AllowedSectorProducerCertificate :
    SU7AllowedSectorProducerCertificate where
  allowed_sector_iff_filtered :=
    nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer
  allowed_sector_iff_selector :=
    nonemptyAllowedPrimeEdgeSector_iff_confinementSelector
  allowed_sector_iff_alpha_nail :=
    nonemptyAllowedPrimeEdgeSector_iff_alphaStrongConvergentCarrierNail
  allowed_sector_iff_unit_bracket :=
    nonemptyAllowedPrimeEdgeSector_iff_unitBracketProducer
  allowed_sector_iff_fixed_point :=
    nonemptyAllowedPrimeEdgeSector_iff_fixedPointProducer
  filtered_producer_to_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfFilteredProducer
  no_holonomy_to_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfNoPermanentHolonomy
  alpha_nail_to_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfAlphaStrongConvergentCarrierNail
  alpha_requires_convergence_to_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfAlphaRequiresConvergence
  allowed_sector_extracts_selector :=
    confinementSelectorOfAllowedPrimeEdgeSector
  allowed_sector_extracts_witness :=
    colorLoopWitnessOfAllowedPrimeEdgeSector

end StandardModelConstraint
end SaturationMonoid
