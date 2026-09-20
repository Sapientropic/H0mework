import H0mework.Physics.JointVariation.GeneratedProfiles
import H0mework.Physics.JointVariation.SectionFixed

/-!
# Fixed P506/L0 regression for complete-joint generated profiles

At time zero, full spacetime recentering reduces to the established spatial
recenter.  Consequently the source/current-only generated profile is exactly
the profile extracted from the already accepted fixed Cartan restart current.
This is a provenance regression; it does not assert a global field lift or an
arbitrary-time zero fiber.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- The profile bundle already generated from the authoritative fixed Cartan
restart at one spatial occurrence. -/
def fixedP506L0CompleteJointGeneratedProfiles
    (space : StageNineSpatialPoint) : CompleteJointGeneratedProfiles :=
  completeJointGeneratedProfilesFromCurrent positiveSmoothUnifiedSource
    (fixedP506L0CartanRestartActual space)

/-- The new full-occurrence profile producer restricts at time zero to the
existing fixed P506/L0 Cartan-restart profile, field for field. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointProfiles_fixed_timeZero
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedDiracDualCompleteJointProfiles
        positiveSmoothUnifiedSource FixedInput
        (canonicalCauchySlicePoint 0 space) =
      fixedP506L0CompleteJointGeneratedProfiles space := by
  unfold sourceActionGeneratedDiracDualCompleteJointProfiles
    completeJointGeneratedProfileRestartCurrent
    fixedP506L0CompleteJointGeneratedProfiles
  rw [fullyRecenterHolonomicConfiguration_timeZero]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506
