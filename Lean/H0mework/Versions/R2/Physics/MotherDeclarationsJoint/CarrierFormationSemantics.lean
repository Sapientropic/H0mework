import H0mework.Versions.R2.Physics.MotherDeclarationsJoint.CarrierFormationFactory
import H0mework.Versions.R2.Physics.MotherProgrammesFormationActual.Transition

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 8000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedIntegralCoherentJointAction
open MotherTypeFormation MotherSourceTypeOrigin MotherFamilyOccurrence Stage9C.Revision

noncomputable section

theorem orbit_action_value (stage : ℕ) (word current after : ActualFormation.IntegralCarrier)
    (currentRead : current = (ActualFormation.nativeAction ^ stage) word)
    (afterRead : after = ActualFormation.nativeAction current) :
    seedValue after + (orbitValue stage word - seedValue current) =
      ActualFormation.Transition.nativeLift (orbitValue stage word) := by
  have integral : ActualFormation.jointInput.integralFace (orbitValue stage word) =
      (ActualFormation.nativeAction ^ stage) word :=
    MotherOrbitWords.integral_orbit ActualFormation.jointInput (stage, word)
  have currentEq := currentRead.trans integral.symm
  have afterEq := afterRead.trans (congrArg ActualFormation.nativeAction currentEq)
  have computed := congrArg₂ (fun new old =>
    seedValue new + (orbitValue stage word - seedValue old)) afterEq currentEq
  exact computed.trans (ActualFormation.Transition.nativeLift_decomposition (orbitValue stage word)).symm

theorem every_term (typeLaw actionLaw : Law)
    (formedWords : ∀ target : ActualFormation.IntegralCarrier,
      ∃ material : WordMaterial, ∃ word : Carrier typeLaw,
        formWord typeLaw material = some word ∧ readWord typeLaw word = target)
    (acts : ∀ word : Carrier typeLaw, ∃ after : Carrier typeLaw,
      wordAction typeLaw actionLaw word = some after ∧
      readWord typeLaw after = ActualFormation.nativeAction (readWord typeLaw word))
    (parent : MotherVisit) (target : ActualFormation.IntegralCarrier) :
    ∃ wordMaterial : WordMaterial,
      formTerm typeLaw (parent, wordMaterial) = some (orbitValue (StageEightDiscreteFormation.codeOf parent) target) ∧
      actTerm typeLaw actionLaw (parent, wordMaterial) =
        some (ActualFormation.Transition.nativeLift (orbitValue (StageEightDiscreteFormation.codeOf parent) target)) := by
  obtain ⟨wordMaterial, word, formed, wordRead⟩ := formedWords target
  let material : OrbitMaterial := (parent, wordMaterial)
  have orbitEq : orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word) =
      orbitValue (StageEightDiscreteFormation.codeOf parent) target :=
    congrArg (orbitValue (StageEightDiscreteFormation.codeOf parent)) wordRead
  obtain ⟨current, iterated, currentRead⟩ :=
    iterateWord_native typeLaw actionLaw acts (StageEightDiscreteFormation.codeOf material.1) word
  obtain ⟨after, acted, afterRead⟩ := acts current
  refine ⟨wordMaterial, (formTerm_eq typeLaw material word formed).trans (congrArg some orbitEq), ?_⟩
  exact (actTerm_eq typeLaw actionLaw material word current after formed iterated acted).trans
    (congrArg some ((orbit_action_value (StageEightDiscreteFormation.codeOf material.1)
      (readWord typeLaw word) (readWord typeLaw current) (readWord typeLaw after) currentRead afterRead).trans
        (congrArg ActualFormation.Transition.nativeLift orbitEq)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier
