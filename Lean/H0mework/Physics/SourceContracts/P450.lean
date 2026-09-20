import H0mework.Physics.SourceContracts.P449

/-!
# Proposition 450: the faithful door is strictly stronger than the old door

P448 showed that the old P447 front door admits a degenerate `Unit/Unit/Unit`
toy inhabitant.  P449 added a physical-faithfulness layer and proved that this
particular toy kernel fails it.

This file closes the logical loophole: on the entire `Unit/Unit/Unit` carrier
there can be no faithful front door, because the coefficient group `Unit` makes
the CKM H¹ quotient subsingleton.  Therefore the old current central
holy-grail constants are genuinely too weak: they hold on the degenerate unit
carrier, while the faithful front door does not.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace GrandUnificationProducerNormalForm

/-! ## Unit H¹ collapses -/

/-- THEOREM 1: with coefficient group `Unit`, every P70 H¹ quotient is
subsingleton. -/
theorem unitCoefficientH1Quotient_subsingleton
    (Index : Type*) (C : CechAdditiveCover Index Unit) :
    Subsingleton (CechAdditiveCover.H1Quotient C) := by
  infer_instance

/-- THEOREM 2: any kernel whose coefficient group and CKM carrier are both
`Unit` has no nonzero CKM H¹ class. -/
theorem unitCarrier_no_nonzeroCKMH1Class
    (K : IrreducibleGrandUnificationProducerKernel Unit Unit Unit) :
    ¬ HasNonzeroCKMH1Class K := by
  rintro ⟨seed, hseed⟩
  exact hseed (Subsingleton.elim _ _)

/-- THEOREM 3: the physically faithful front door is impossible on the fully
degenerate `Unit/Unit/Unit` carrier. -/
theorem unitCarrier_no_faithfulFrontDoor :
    ¬ PhysicallyFaithfulGrandUnificationFrontDoor Unit Unit Unit := by
  rintro ⟨K, hK⟩
  exact unitCarrier_no_nonzeroCKMH1Class K hK.nonzeroCKMH1

/-! ## Strictness witness -/

/-- THEOREM 4: the old current central constants hold on the unit toy carrier,
but the faithful front door does not. -/
theorem unitCarrier_currentCentral_without_faithfulFrontDoor :
    CurrentFormalExactGeometryCentralHolyGrailConstants Unit Unit Unit ∧
      ¬ PhysicallyFaithfulGrandUnificationFrontDoor Unit Unit Unit := by
  exact
    ⟨DegenerateKernelAudit.unitToy_currentCentralHolyGrailConstants,
      unitCarrier_no_faithfulFrontDoor⟩

/-- THEOREM 5: likewise, the old single-source receipt holds on the unit toy
carrier while the faithful front door is impossible. -/
theorem unitCarrier_singleSourceReceipt_without_faithfulFrontDoor :
    Nonempty (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
        Unit Unit Unit) ∧
      ¬ PhysicallyFaithfulGrandUnificationFrontDoor Unit Unit Unit := by
  exact
    ⟨DegenerateKernelAudit.unitToy_singleSourcePhysicalHolyGrailReceipt,
      unitCarrier_no_faithfulFrontDoor⟩

/-- THEOREM 6: on the unit carrier, the old central holy-grail constants do
not imply the new faithful front door. -/
theorem unitCarrier_currentCentral_does_not_imply_faithfulFrontDoor :
    ¬ (CurrentFormalExactGeometryCentralHolyGrailConstants Unit Unit Unit ->
        PhysicallyFaithfulGrandUnificationFrontDoor Unit Unit Unit) := by
  intro h
  exact
    unitCarrier_no_faithfulFrontDoor
      (h DegenerateKernelAudit.unitToy_currentCentralHolyGrailConstants)

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
