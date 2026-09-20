import H0mework.Physics.GaugeFlow.P833

/-!
# Proposition 834: confinement law as residual-split no-holonomy

P831 proved the equivalence:

`permanent color holonomy ↔ residual-split permanent holonomy`.

P832/P833 then made the positive target a real data object:

`SU7AllowedPrimeEdgeSector`.

This file names the missing law object directly.  A SU(7) confinement law is
not a selector and not a number-theoretic witness.  It is the assertion that no
active residual-transport readout can carry permanent color holonomy.  Lean
then extracts the whole chain:

`no-gap -> allowed sector -> unit bracket -> fixed point -> witness`.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## Confinement as residual-split no-holonomy -/

/-- SU(7) confinement read as a residual-transport law: no active scalar
readout of the color-loop trace carrier admits residual-split permanent
holonomy. -/
structure SU7ConfinementResidualSplitLaw : Prop where
  forbids_residual_split_permanent :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      ¬ ColorLoopResidualSplitPermanentHolonomy sigma

/-- THEOREM 1: the confinement law forbids ordinary permanent prime-edge color
holonomy. -/
theorem noPermanentColorHolonomy_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    ¬ PermanentPrimeEdgeColorHolonomy := by
  have hno :
      ¬ ColorLoopResidualSplitPermanentHolonomy (1 : ℝ) :=
    L.forbids_residual_split_permanent 1 (by norm_num)
  exact
    (noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
      1 (by norm_num)).mp hno

/-- THEOREM 2: the confinement law produces the prime-edge trace-spectrum
no-gap statement. -/
theorem primeEdgeTraceSpectrumNoGap_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    PrimeEdgeTraceSpectrumNoGap := by
  have hfiltered :
      SU7FilteredPrimeEdgeLoopProducer :=
    (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mp
      (noPermanentColorHolonomy_of_confinementResidualSplitLaw L)
  exact
    (primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer).mpr hfiltered

/-- THEOREM 3: the confinement law produces the SU(7)-filtered prime-edge
producer. -/
theorem su7FilteredProducer_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7FilteredPrimeEdgeLoopProducer :=
  (primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer).mp
    (primeEdgeTraceSpectrumNoGap_of_confinementResidualSplitLaw L)

/-- THEOREM 4: the confinement law produces the global allowed-sector data. -/
noncomputable def su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7AllowedPrimeEdgeSector :=
  su7AllowedPrimeEdgeSectorOfFilteredProducer
    (su7FilteredProducer_of_confinementResidualSplitLaw L)

/-- THEOREM 5: the confinement-produced allowed sector normalizes to trace-zero
on every even fiber. -/
theorem su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw_trace_zero
    (L : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw L)).loop
            n hn).leftPrime
        ((su7AllowedPrimeEdgeSectorNormalForm
          (su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw L)).loop
            n hn).rightPrime) :=
  ((su7AllowedPrimeEdgeSectorNormalForm
    (su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw L)).loop
      n hn).trace_zero

/-- THEOREM 6: the confinement law produces the concrete selector readout. -/
noncomputable def confinementSelectorOfResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7ConfinementPrimeEdgeSelector :=
  confinementSelectorOfAllowedPrimeEdgeSector
    (su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw L)

/-- THEOREM 7: the confinement law produces the data-level
unit-bracket/fixed-point witness. -/
noncomputable def colorLoopWitnessOfConfinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfAllowedPrimeEdgeSector
    (su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw L)

/-- THEOREM 8: the confinement law produces the unit-bracket producer. -/
theorem unitBracketProducer_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducerOfColorLoopWitness
    (colorLoopWitnessOfConfinementResidualSplitLaw L)

/-- THEOREM 9: the confinement law produces the fixed-point witness producer. -/
noncomputable def fixedPointProducer_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducerOfColorLoopWitness
    (colorLoopWitnessOfConfinementResidualSplitLaw L)

/-- THEOREM 10: a SU(7)-filtered producer induces the residual-split
confinement law.  This is the old positive producer read as the new no-holonomy
law. -/
theorem confinementResidualSplitLaw_of_su7FilteredProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7ConfinementResidualSplitLaw where
  forbids_residual_split_permanent := by
    intro sigma hsigma
    exact noResidualSplitPermanentHolonomy_of_su7FilteredProducer
      sigma hsigma P

/-- THEOREM 11: an alpha-convergent carrier nail induces the residual-split
confinement law. -/
theorem confinementResidualSplitLaw_of_alphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_su7FilteredProducer
    (su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail H)

/-- THEOREM 12: the confinement residual-split law is exactly the absence of
permanent prime-edge color holonomy. -/
theorem confinementResidualSplitLaw_iff_noPermanentColorHolonomy :
    SU7ConfinementResidualSplitLaw ↔
      ¬ PermanentPrimeEdgeColorHolonomy := by
  constructor
  · exact noPermanentColorHolonomy_of_confinementResidualSplitLaw
  · intro hno
    refine ⟨?_⟩
    intro sigma hsigma
    exact
      (noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
        sigma hsigma).mpr hno

/-- THEOREM 13: the confinement residual-split law is exactly no trace-spectrum
gap. -/
theorem confinementResidualSplitLaw_iff_primeEdgeTraceSpectrumNoGap :
    SU7ConfinementResidualSplitLaw ↔
      PrimeEdgeTraceSpectrumNoGap := by
  exact
    confinementResidualSplitLaw_iff_noPermanentColorHolonomy.trans
      (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer.trans
        primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer.symm)

/-- THEOREM 14: the confinement residual-split law is exactly nonempty
allowed-sector data. -/
theorem confinementResidualSplitLaw_iff_allowedSector :
    SU7ConfinementResidualSplitLaw ↔
      Nonempty SU7AllowedPrimeEdgeSector := by
  exact
    confinementResidualSplitLaw_iff_noPermanentColorHolonomy.trans
      (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer.trans
        nonemptyAllowedPrimeEdgeSector_iff_su7FilteredProducer.symm)

/-- THEOREM 15: the confinement residual-split law is exactly the data-level
unit-bracket/fixed-point witness. -/
theorem confinementResidualSplitLaw_iff_colorLoopWitness :
    SU7ConfinementResidualSplitLaw ↔
      Nonempty ColorLoopUnitBracketFixedPointWitness := by
  exact
    confinementResidualSplitLaw_iff_allowedSector.trans
      (nonemptyAllowedPrimeEdgeSector_iff_confinementSelector.trans
        nonemptyColorLoopWitness_iff_confinementSelector.symm)

/-! ## Certificate -/

/-- P834 certificate: the shortest no-gap chain is now a confinement law:
residual-split permanent holonomy is forbidden, hence trace-spectrum gaps are
absent, hence allowed-sector data and the unit-bracket/fixed-point witness are
produced. -/
structure SU7ConfinementResidualSplitLawCertificate where
  law_iff_no_permanent_color_holonomy :
    SU7ConfinementResidualSplitLaw ↔
      ¬ PermanentPrimeEdgeColorHolonomy
  law_iff_trace_spectrum_no_gap :
    SU7ConfinementResidualSplitLaw ↔
      PrimeEdgeTraceSpectrumNoGap
  law_iff_allowed_sector :
    SU7ConfinementResidualSplitLaw ↔
      Nonempty SU7AllowedPrimeEdgeSector
  law_iff_witness :
    SU7ConfinementResidualSplitLaw ↔
      Nonempty ColorLoopUnitBracketFixedPointWitness
  law_produces_allowed_sector :
    SU7ConfinementResidualSplitLaw -> SU7AllowedPrimeEdgeSector
  law_produces_selector :
    SU7ConfinementResidualSplitLaw -> SU7ConfinementPrimeEdgeSelector
  law_produces_witness :
    SU7ConfinementResidualSplitLaw -> ColorLoopUnitBracketFixedPointWitness
  law_produces_unit_bracket :
    SU7ConfinementResidualSplitLaw -> ColorLoopTraceUnitBracketProducer
  law_produces_fixed_point :
    SU7ConfinementResidualSplitLaw -> EvenGoldbachDynamicalFixedPointProducer
  filtered_producer_induces_law :
    SU7FilteredPrimeEdgeLoopProducer -> SU7ConfinementResidualSplitLaw
  alpha_nail_induces_law :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      SU7ConfinementResidualSplitLaw

/-- THEOREM 16: canonical confinement residual-split law certificate. -/
def su7ConfinementResidualSplitLawCertificate :
    SU7ConfinementResidualSplitLawCertificate where
  law_iff_no_permanent_color_holonomy :=
    confinementResidualSplitLaw_iff_noPermanentColorHolonomy
  law_iff_trace_spectrum_no_gap :=
    confinementResidualSplitLaw_iff_primeEdgeTraceSpectrumNoGap
  law_iff_allowed_sector :=
    confinementResidualSplitLaw_iff_allowedSector
  law_iff_witness :=
    confinementResidualSplitLaw_iff_colorLoopWitness
  law_produces_allowed_sector :=
    su7AllowedPrimeEdgeSectorOfConfinementResidualSplitLaw
  law_produces_selector :=
    confinementSelectorOfResidualSplitLaw
  law_produces_witness :=
    colorLoopWitnessOfConfinementResidualSplitLaw
  law_produces_unit_bracket :=
    unitBracketProducer_of_confinementResidualSplitLaw
  law_produces_fixed_point :=
    fixedPointProducer_of_confinementResidualSplitLaw
  filtered_producer_induces_law :=
    confinementResidualSplitLaw_of_su7FilteredProducer
  alpha_nail_induces_law :=
    confinementResidualSplitLaw_of_alphaStrongConvergentCarrierNail

end StandardModelConstraint
end SaturationMonoid
