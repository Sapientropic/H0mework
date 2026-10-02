import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence
import H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential

/-! Earlier physical stages are read from the source projection of the same
Stage-10 occurrence. Their finite action and configuration keep their own
scope; the current holonomic actual is recovered separately. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Recovery

open StageEightProofFreeSource SU7MotherPhysicalUnifiedAdmission
open SU7GravityGaugeMatterJointCredential EmpiricalReferenceScaleCouplingBoundary

noncomputable section

def stageSix :
    SU7MotherPhysicalUnifiedAdmissionCredential
      Runtime.source.stageEight.toPhysicalSource unitBoundary :=
  canonicalPhysicalStageSix

def stageEight : StageEightGravityGaugeMatterCredential Runtime.source.stageEight stageSix :=
  canonicalStageEightGravityGaugeMatterCredential

theorem source_restriction : Runtime.source.stageEight = canonicalSource := rfl

theorem stageSix_generated : stageSix = canonicalPhysicalStageSix := rfl

theorem stageEight_generated : stageEight = canonicalStageEightGravityGaugeMatterCredential := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Recovery
