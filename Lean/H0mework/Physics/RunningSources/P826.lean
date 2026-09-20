import H0mework.Arithmetic.CodePairs.P825

/-!
# Proposition 826: alpha convergence directly produces the color-loop witness

P825 names the real color-loop target:

* no permanent prime-edge color holonomy;
* equivalently, a SU(7)-filtered prime-edge loop producer;
* equivalently, the unit-bracket producer;
* equivalently, the fixed-point witness producer.

This file welds that target to the P819 alpha-convergence nail.  The result is
not another carrier-consistency shell: an `AlphaStrongConvergentCarrierNail`
itself produces the no-holonomy statement, the SU(7)-filtered selector, the
unit bracket, and the fixed-point witness.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open GrandUnification
open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Old and new permanent-obstruction languages are the same -/

/-- THEOREM 1: P819's permanent Goldbach-side gauge obstruction is exactly
P825's permanent prime-edge color holonomy. -/
theorem permanentPrimeEdgeColorHolonomy_iff_goldbachGaugeObstruction :
    PermanentPrimeEdgeColorHolonomy ↔
      GrandUnification.PermanentGoldbachGaugeObstruction := by
  constructor
  · intro hperm
    have hnotSU7 :
        ¬ SU7FilteredPrimeEdgeLoopProducer :=
      (permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer).mp hperm
    intro hunit
    exact hnotSU7
      ((su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer).mpr hunit)
  · intro hobs
    exact
      (permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer).mpr
        (by
          intro hSU7
          exact hobs
            ((su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer).mp hSU7))

/-! ## Alpha convergence nail as the witness producer -/

/-- THEOREM 2: an alpha-convergent carrier nail rules out permanent prime-edge
color holonomy. -/
theorem noPermanentPrimeEdgeColorHolonomy_of_alphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  (noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer).mpr
    (GrandUnification.colorLoopTraceUnitBracketProducer_of_alphaStrongConvergentCarrierNail H)

/-- THEOREM 3: an alpha-convergent carrier nail produces the SU(7)-filtered
prime-edge loop selector. -/
theorem su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    SU7FilteredPrimeEdgeLoopProducer :=
  (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mp
    (noPermanentPrimeEdgeColorHolonomy_of_alphaStrongConvergentCarrierNail H)

/-- THEOREM 4: an alpha-convergent carrier nail produces the unit bracket. -/
theorem unitBracketProducerOfAlphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducerOfSU7FilteredLoopProducer
    (su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail H)

/-- THEOREM 5: an alpha-convergent carrier nail produces the fixed-point
witness producer. -/
theorem fixedPointProducerOfAlphaStrongConvergentCarrierNail
    (H : GrandUnification.AlphaStrongConvergentCarrierNail) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  (noPermanentPrimeEdgeColorHolonomy_iff_fixedPointProducer).mp
    (noPermanentPrimeEdgeColorHolonomy_of_alphaStrongConvergentCarrierNail H)

/-- THEOREM 6: an alpha-convergent carrier nail is exactly no permanent
prime-edge color holonomy. -/
theorem alphaStrongConvergentCarrierNail_iff_noPermanentPrimeEdgeColorHolonomy :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      ¬ PermanentPrimeEdgeColorHolonomy := by
  constructor
  · exact noPermanentPrimeEdgeColorHolonomy_of_alphaStrongConvergentCarrierNail
  · intro hno
    have hunit :
        ColorLoopTraceUnitBracketProducer :=
      (noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer).mp hno
    have hgoldbach :
        EvenGoldbachStatement :=
      (colorLoopTraceUnitBracketProducer_iff_evenGoldbach).mp hunit
    exact
      (GrandUnification.alphaStrongConvergentCarrierNail_iff_evenGoldbach).mpr
        hgoldbach

/-- THEOREM 7: the alpha-convergence nail is exactly the SU(7)-filtered
prime-edge loop producer. -/
theorem alphaStrongConvergentCarrierNail_iff_su7FilteredProducer :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      SU7FilteredPrimeEdgeLoopProducer :=
  alphaStrongConvergentCarrierNail_iff_noPermanentPrimeEdgeColorHolonomy.trans
    noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer

/-- THEOREM 8: the alpha-convergence nail is exactly the unit-bracket
producer. -/
theorem alphaStrongConvergentCarrierNail_iff_unitBracketProducer :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      ColorLoopTraceUnitBracketProducer :=
  alphaStrongConvergentCarrierNail_iff_noPermanentPrimeEdgeColorHolonomy.trans
    noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer

/-- THEOREM 9: the alpha-convergence nail is exactly the fixed-point witness
producer. -/
theorem alphaStrongConvergentCarrierNail_iff_fixedPointProducer :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  alphaStrongConvergentCarrierNail_iff_noPermanentPrimeEdgeColorHolonomy.trans
    noPermanentPrimeEdgeColorHolonomy_iff_fixedPointProducer

/-! ## Certificate -/

/-- P826 certificate: the concrete alpha-convergence nail is the same object as
the no-permanent-holonomy / SU(7)-filtered / unit-bracket / fixed-point
producer. -/
structure AlphaConvergenceColorLoopWitnessProducerCertificate : Prop where
  permanent_languages_equivalent :
    PermanentPrimeEdgeColorHolonomy ↔
      GrandUnification.PermanentGoldbachGaugeObstruction
  alpha_nail_excludes_permanent_holonomy :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      ¬ PermanentPrimeEdgeColorHolonomy
  alpha_nail_iff_no_permanent_holonomy :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      ¬ PermanentPrimeEdgeColorHolonomy
  alpha_nail_iff_su7_filtered :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      SU7FilteredPrimeEdgeLoopProducer
  alpha_nail_iff_unit_bracket :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      ColorLoopTraceUnitBracketProducer
  alpha_nail_iff_fixed_point :
    GrandUnification.AlphaStrongConvergentCarrierNail ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  alpha_nail_extracts_su7_filtered :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      SU7FilteredPrimeEdgeLoopProducer
  alpha_nail_extracts_unit_bracket :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      ColorLoopTraceUnitBracketProducer
  alpha_nail_extracts_fixed_point :
    GrandUnification.AlphaStrongConvergentCarrierNail ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer

/-- THEOREM 10: canonical alpha-convergence/color-loop witness producer
certificate. -/
theorem alphaConvergenceColorLoopWitnessProducerCertificate :
    AlphaConvergenceColorLoopWitnessProducerCertificate where
  permanent_languages_equivalent :=
    permanentPrimeEdgeColorHolonomy_iff_goldbachGaugeObstruction
  alpha_nail_excludes_permanent_holonomy :=
    noPermanentPrimeEdgeColorHolonomy_of_alphaStrongConvergentCarrierNail
  alpha_nail_iff_no_permanent_holonomy :=
    alphaStrongConvergentCarrierNail_iff_noPermanentPrimeEdgeColorHolonomy
  alpha_nail_iff_su7_filtered :=
    alphaStrongConvergentCarrierNail_iff_su7FilteredProducer
  alpha_nail_iff_unit_bracket :=
    alphaStrongConvergentCarrierNail_iff_unitBracketProducer
  alpha_nail_iff_fixed_point :=
    alphaStrongConvergentCarrierNail_iff_fixedPointProducer
  alpha_nail_extracts_su7_filtered :=
    su7FilteredPrimeEdgeLoopProducerOfAlphaStrongConvergentCarrierNail
  alpha_nail_extracts_unit_bracket :=
    unitBracketProducerOfAlphaStrongConvergentCarrierNail
  alpha_nail_extracts_fixed_point :=
    fixedPointProducerOfAlphaStrongConvergentCarrierNail

end StandardModelConstraint
end SaturationMonoid
