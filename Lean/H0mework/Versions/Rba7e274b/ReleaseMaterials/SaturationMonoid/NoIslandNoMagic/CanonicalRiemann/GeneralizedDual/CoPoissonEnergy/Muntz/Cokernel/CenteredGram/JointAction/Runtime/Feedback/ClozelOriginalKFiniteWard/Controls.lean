import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Feedback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem self_program_effect_zero (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (selfSourceCode observation nontrivial half).effect environment increment = 0 := by
  have update := Expr.eval_update (selfSourceCode observation nontrivial half) environment increment
  rw [self_source_code_owned, self_source_code_owned] at update
  exact (add_left_cancel ((add_zero _).trans update)).symm

theorem joint_program_keeps_self (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (actionCode observation nontrivial half).eval environment -
      (wardCode observation nontrivial half).eval environment =
      (selfSourceValue observation nontrivial half, 0) := by
  change (wardCode observation nontrivial half).eval environment +
    (selfSourceCode observation nontrivial half).eval environment -
      (wardCode observation nontrivial half).eval environment = _
  rw [self_source_code_owned]
  abel

theorem actual_increment_retained (ordinal : Nat) :
    updatedRInput observation nontrivial half depth ordinal =
      D.raw observation nontrivial half depth (ordinal + 1) +
        actualDelta (actionPacket observation nontrivial half depth ordinal) := by
  unfold updatedRInput
  rw [actual_R_born_input]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
