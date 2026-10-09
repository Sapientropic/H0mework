import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

abbrev JointCarrier := CoarseModel root recognition visit successor transition alignment U7 calculus count ×
  whole root recognition visit successor transition alignment U7 calculus count
local instance : Module ℤ (JointCarrier root recognition visit successor transition alignment U7 calculus count) :=
  AddCommGroup.toIntModule _
def together : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    JointCarrier root recognition visit successor transition alignment U7 calculus count := (coarseRestriction root recognition visit successor transition alignment U7 calculus count).prod
  (sourceMap root recognition visit successor transition alignment U7 calculus count)
theorem kernel_zero (value : Model root recognition visit successor transition alignment U7 calculus count)
    (invisible : together root recognition visit successor transition alignment U7 calculus count value=0) : value=0 := by
  revert invisible
  refine Submodule.Quotient.induction_on _ value (fun point => ?_)
  intro invisible
  have coarseZero := congrArg Prod.fst invisible
  have hilbertZero := (source_kernel root recognition visit successor transition alignment U7 calculus count
    (projection root recognition visit successor transition alignment U7 calculus count point)).mp (congrArg Prod.snd invisible)
  have originalRead := (all_prefix_zero root recognition visit successor transition alignment U7 calculus count
    (projection root recognition visit successor transition alignment U7 calculus count point)).mp
    ((prefix_kernel root recognition visit successor transition alignment U7 calculus count _).mpr hilbertZero)
  change projection root recognition visit successor transition alignment U7 calculus count point = 0
  rw [← map_zero (projection root recognition visit successor transition alignment U7 calculus count)]
  apply (SourceGeneratedActionWords.projection_fibre _ _ _ point 0).mpr
  intro word
  apply Prod.ext
  · change SourceGeneratedActionWords.projection _ _ _ point = 0 at coarseZero
    rw [← map_zero (SourceGeneratedActionWords.projection
      (actions root recognition visit successor transition alignment U7 calculus count)
      (coarseRead root recognition visit successor transition alignment U7 calculus count)
      (.simultaneous : Letter root recognition visit successor))] at coarseZero
    exact (SourceGeneratedActionWords.projection_fibre _ _ _ point 0).mp coarseZero word
  · apply Prod.ext
    · funext actor
      have given := originalRead word (.inl actor)
      rw [SourceGeneratedActionWords.run_source,Covariance.feature_source] at given
      change actor.val.2.measurement (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point).1 =
        actor.val.2.measurement (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word 0).1
      simpa only [Covariance.originalFeature,LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,Prod.fst_zero,Prod.snd_zero,map_zero] using given
    · funext actor
      have given := originalRead word (.inr actor)
      rw [SourceGeneratedActionWords.run_source,Covariance.feature_source] at given
      change actor.val.2.measurement (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point).2 =
        actor.val.2.measurement (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word 0).2
      simpa only [Covariance.originalFeature,LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,Prod.fst_zero,Prod.snd_zero,map_zero] using given
theorem injective : Function.Injective (together root recognition visit successor transition alignment U7 calculus count) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro value zero
  exact kernel_zero root recognition visit successor transition alignment U7 calculus count value zero

abbrev Range := (together root recognition visit successor transition alignment U7 calculus count).range

def equivalence := LinearEquiv.ofInjective
  (together root recognition visit successor transition alignment U7 calculus count)
  (injective root recognition visit successor transition alignment U7 calculus count)
abbrev emit := (equivalence root recognition visit successor transition alignment U7 calculus count).toLinearMap
abbrev recover := (equivalence root recognition visit successor transition alignment U7 calculus count).symm.toLinearMap

theorem recover_emit (value : Model root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (emit root recognition visit successor transition alignment U7 calculus count value)=value :=
  (equivalence root recognition visit successor transition alignment U7 calculus count).symm_apply_apply value

theorem emit_recover (value : Range root recognition visit successor transition alignment U7 calculus count) :
    emit root recognition visit successor transition alignment U7 calculus count
      (recover root recognition visit successor transition alignment U7 calculus count value)=value :=
  (equivalence root recognition visit successor transition alignment U7 calculus count).apply_symm_apply value

theorem full_recovery (value : Range root recognition visit successor transition alignment U7 calculus count) :
    together root recognition visit successor transition alignment U7 calculus count
      (recover root recognition visit successor transition alignment U7 calculus count value)=value.val :=
  LinearEquiv.ofInjective_symm_apply _ value

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
