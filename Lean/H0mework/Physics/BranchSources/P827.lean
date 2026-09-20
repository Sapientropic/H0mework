import H0mework.Physics.RunningSources.P826

/-!
# Proposition 827: the low-level SU(7) confinement selector

P826 says that an `AlphaStrongConvergentCarrierNail` is exactly the same object
as no permanent color holonomy, a SU(7)-filtered prime-edge loop producer, the
unit bracket, and the fixed-point witness producer.

This file lowers the remaining inhabitance target from a proposition with
existentials to a data-level selector.  The next producer is now a concrete
function:

`(n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent`

with a SU(7) color-adjoint/traceless filter certificate for the selected loop.
Lean proves that this selector directly produces the prime-pair witness, the
unit bracket, the fixed-point witness, no permanent holonomy, and the alpha
convergence nail.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## The data-level selector -/

/-- A concrete SU(7) confinement selector: for every even fiber `2n >= 4`,
return the prime-edge pair selected by the confinement/filter rule, together
with the SU(7) color-adjoint/traceless filter certificate. -/
structure SU7ConfinementPrimeEdgeSelector where
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  filtered :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      GrandUnification.SU7ColorAdjointRepresentationFilter
        (primeEdgeColorLoopMatrix n (pick n hn).1 (pick n hn).2)

/-- THEOREM 1: a data selector gives the P824 proposition-level filtered
producer. -/
theorem su7FilteredProducer_of_confinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    SU7FilteredPrimeEdgeLoopProducer := by
  intro n hn
  exact ⟨(S.pick n hn).1, (S.pick n hn).2, S.filtered n hn⟩

/-- Build the data selector from a proposition-level filtered producer using
choice.  This is the only noncomputable direction: it packages the existential
producer into an explicit selector object. -/
noncomputable def confinementSelectorOfSU7FilteredProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7ConfinementPrimeEdgeSelector where
  pick := fun n hn =>
    let p : PrimeExponent := Classical.choose (P n hn)
    let q : PrimeExponent := Classical.choose (Classical.choose_spec (P n hn))
    (p, q)
  filtered := by
    intro n hn
    exact Classical.choose_spec (Classical.choose_spec (P n hn))

/-- THEOREM 2: the data selector is exactly the SU(7)-filtered producer. -/
theorem nonemptyConfinementSelector_iff_su7FilteredProducer :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      SU7FilteredPrimeEdgeLoopProducer := by
  constructor
  · rintro ⟨S⟩
    exact su7FilteredProducer_of_confinementSelector S
  · intro P
    exact ⟨confinementSelectorOfSU7FilteredProducer P⟩

/-! ## Direct witness extraction from the selector -/

/-- THEOREM 3: a SU(7) confinement selector directly produces ordinary
prime-pair witnesses. -/
noncomputable def primePairProducerOfConfinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    EvenGoldbachPrimePairProducer where
  pick := S.pick
  sum_pick := by
    intro n hn
    have htrace :
        ColorLoopTraceExact
          (primeEdgeColorLoopMatrix n (S.pick n hn).1 (S.pick n hn).2) :=
      (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n (S.pick n hn).1 (S.pick n hn).2)).mp
        (S.filtered n hn)
    exact
      (primeEdgeColorLoop_trace_zero_iff n
        (S.pick n hn).1 (S.pick n hn).2).mp htrace

/-- THEOREM 4: a SU(7) confinement selector directly produces the
unit-bracket producer. -/
theorem unitBracketProducer_of_confinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    ColorLoopTraceUnitBracketProducer :=
  (colorLoopTraceUnitBracketProducer_iff_primePairProducer).mpr
    ⟨primePairProducerOfConfinementSelector S⟩

/-- THEOREM 5: a SU(7) confinement selector directly produces the fixed-point
witness producer, using the same selected prime-edge pairs. -/
noncomputable def fixedPointProducerOfConfinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    EvenGoldbachDynamicalFixedPointProducer where
  pick := S.pick
  fixed := by
    intro n hn
    exact
      (goldbachDynamicalFixedPoint_iff_sum (2 * n) (S.pick n hn)).mpr
        ((primePairProducerOfConfinementSelector S).sum_pick n hn)

/-- THEOREM 6: a SU(7) confinement selector excludes permanent prime-edge
color holonomy. -/
theorem noPermanentPrimeEdgeColorHolonomy_of_confinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mpr
    (su7FilteredProducer_of_confinementSelector S)

/-- THEOREM 7: a SU(7) confinement selector produces the alpha convergence
nail. -/
theorem alphaStrongConvergentCarrierNail_of_confinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    GrandUnification.AlphaStrongConvergentCarrierNail :=
  (alphaStrongConvergentCarrierNail_iff_su7FilteredProducer).mpr
    (su7FilteredProducer_of_confinementSelector S)

/-- THEOREM 8: the data-level SU(7) confinement selector is exactly the alpha
convergence nail. -/
theorem nonemptyConfinementSelector_iff_alphaStrongConvergentCarrierNail :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      GrandUnification.AlphaStrongConvergentCarrierNail := by
  exact
    nonemptyConfinementSelector_iff_su7FilteredProducer.trans
      alphaStrongConvergentCarrierNail_iff_su7FilteredProducer.symm

/-- THEOREM 9: the data-level SU(7) confinement selector is exactly the
fixed-point witness producer. -/
theorem nonemptyConfinementSelector_iff_fixedPointProducer :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  exact
    nonemptyConfinementSelector_iff_su7FilteredProducer.trans
      su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer

/-! ## Certificate -/

/-- P827 certificate: the remaining producer debt has a concrete selector
form, and this selector directly outputs the unit bracket, fixed point, no
permanent holonomy, and alpha convergence nail. -/
structure SU7ConfinementPrimeEdgeSelectorCertificate : Prop where
  selector_iff_su7_filtered :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      SU7FilteredPrimeEdgeLoopProducer
  selector_iff_alpha_nail :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      GrandUnification.AlphaStrongConvergentCarrierNail
  selector_iff_fixed_point :
    Nonempty SU7ConfinementPrimeEdgeSelector ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  selector_extracts_prime_pair :
    SU7ConfinementPrimeEdgeSelector -> Nonempty EvenGoldbachPrimePairProducer
  selector_extracts_unit_bracket :
    SU7ConfinementPrimeEdgeSelector -> ColorLoopTraceUnitBracketProducer
  selector_extracts_fixed_point :
    SU7ConfinementPrimeEdgeSelector ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  selector_excludes_permanent_holonomy :
    SU7ConfinementPrimeEdgeSelector ->
      ¬ PermanentPrimeEdgeColorHolonomy
  selector_produces_alpha_nail :
    SU7ConfinementPrimeEdgeSelector ->
      GrandUnification.AlphaStrongConvergentCarrierNail

/-- THEOREM 10: canonical selector certificate. -/
theorem su7ConfinementPrimeEdgeSelectorCertificate :
    SU7ConfinementPrimeEdgeSelectorCertificate where
  selector_iff_su7_filtered :=
    nonemptyConfinementSelector_iff_su7FilteredProducer
  selector_iff_alpha_nail :=
    nonemptyConfinementSelector_iff_alphaStrongConvergentCarrierNail
  selector_iff_fixed_point :=
    nonemptyConfinementSelector_iff_fixedPointProducer
  selector_extracts_prime_pair :=
    fun S => ⟨primePairProducerOfConfinementSelector S⟩
  selector_extracts_unit_bracket :=
    unitBracketProducer_of_confinementSelector
  selector_extracts_fixed_point :=
    fun S => ⟨fixedPointProducerOfConfinementSelector S⟩
  selector_excludes_permanent_holonomy :=
    noPermanentPrimeEdgeColorHolonomy_of_confinementSelector
  selector_produces_alpha_nail :=
    alphaStrongConvergentCarrierNail_of_confinementSelector

end StandardModelConstraint
end SaturationMonoid
