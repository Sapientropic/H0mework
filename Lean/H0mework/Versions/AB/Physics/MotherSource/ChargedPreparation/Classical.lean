import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Full

/-! The charged preparation retains the independent dual by its original spin exchange. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF.Compatibility
open YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

def dualPreparation : Mother :=
  flipMatter.comp ((fromOperator (operator preparation).adjoint).comp flipMatter)

theorem paired_charge (matter : DiracExteriorMatterCarrier) :
    pairedMother preparation (chargeMother.comp preparation) matter =
      dualPreparation (currentAction 0 HyperchargeResponse.chargeDirection (preparation matter)) := by
  simp [pairedMother, dualPreparation, chargeMother, fromOperator, operator]

/-- The same classical current, evaluated on the prepared matter and transported independent dual. -/
theorem classical_current (point : BasePoint) :
    actual.conjugateMatter point
      (dualPreparation (currentAction 0 HyperchargeResponse.chargeDirection
        (preparation (actual.matter point)))) = -4 * (spinScale : ℂ) := by
  rw [← paired_charge, dual_gram]
  have compose : operator (chargeMother.comp preparation) (YangMills.FullPairing.prepared point) =
      operator chargeMother (operator preparation (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [compose, full_charge_pair]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation
