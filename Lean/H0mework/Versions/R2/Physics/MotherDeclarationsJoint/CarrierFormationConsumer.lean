import H0mework.Versions.R2.Physics.MotherDeclarationsJoint.CarrierFormationCoverage

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 8000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier

open MotherTypeFormation

noncomputable section

/-- This is the original computed feedback direction, not an extra factory operand. -/
def sourceFeedback : Joint :=
  ActualFormation.Transition.incidence
    (ActualFormation.event (0, .running ClockBFFeedback.sourcePrepared))

theorem source_feedback_formed :
    ∃ typeLaw actionLaw : Law, ∃ material : Material,
      form typeLaw material = some sourceFeedback ∧
      act typeLaw actionLaw material = some sourceFeedback ∧ sourceFeedback ≠ 0 := by
  obtain ⟨typeLaw, actionLaw, formed⟩ := whole_carrier_formed
  have retained : ActualFormation.Transition.nativeLift sourceFeedback = sourceFeedback ∧ sourceFeedback ≠ 0 :=
    ActualFormation.Transition.source_feedback_retained
  let material := (formed sourceFeedback).choose
  have generated := (formed sourceFeedback).choose_spec
  exact ⟨typeLaw, actionLaw, material, generated.1,
    generated.2.trans (congrArg some retained.1), retained.2⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier
