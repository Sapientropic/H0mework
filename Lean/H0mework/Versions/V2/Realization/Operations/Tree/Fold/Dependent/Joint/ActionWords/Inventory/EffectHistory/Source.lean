import H0mework.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory.Equation
import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Evolution
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace I
export SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
  (SourceActor TargetActor Letter Carrier Model projection advance readout actions normal original sourceRoot sourceRootActor targetRootActor)
end I
namespace C
export SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
  (Actor feature evolution)
end C
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

abbrev Waves := SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Actor root recognition visit successor → H

def measurement : I.Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    Waves root recognition visit successor := LinearMap.pi
  (C.feature root recognition visit successor transition alignment U7 calculus count)
def wave (letter : I.Letter root recognition visit successor) :
    Waves root recognition visit successor →ₗ[ℤ] Waves root recognition visit successor := by
  classical
  exact LinearMap.pi fun actor =>
    if actor = match letter with
      | .source selected => .inl selected
      | .target selected => .inr selected
      | .simultaneous => .inl (I.sourceRootActor root recognition visit)
    then ((C.evolution root recognition visit successor actor).toLinearMap.restrictScalars ℤ).comp (LinearMap.proj actor)
    else if letter = (.simultaneous : I.Letter root recognition visit successor) ∧
      actor = .inr (I.targetRootActor root recognition visit successor)
    then ((C.evolution root recognition visit successor actor).toLinearMap.restrictScalars ℤ).comp (LinearMap.proj actor)
    else LinearMap.proj actor

theorem wave_source (selected : I.SourceActor root recognition visit) (value : Waves root recognition visit successor) :
    wave root recognition visit successor (.source selected) value (.inl selected) = selected.val.2.hilbertEvolution (value (.inl selected)) := by
  classical
  simp only [wave,LinearMap.pi_apply,ite_true,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.restrictScalars_apply,C.evolution,LinearIsometry.coe_toLinearMap]
theorem wave_target (selected : I.TargetActor root recognition visit successor) (value : Waves root recognition visit successor) :
    wave root recognition visit successor (.target selected) value (.inr selected) = selected.val.2.hilbertEvolution (value (.inr selected)) := by
  classical
  simp only [wave,LinearMap.pi_apply,ite_true,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.restrictScalars_apply,C.evolution,LinearIsometry.coe_toLinearMap]
theorem wave_source_other (selected current : I.SourceActor root recognition visit)
    (different : current ≠ selected) (value : Waves root recognition visit successor) :
    wave root recognition visit successor (.source selected) value (.inl current) = value (.inl current) := by
  classical
  simp [wave,different]
theorem wave_target_other (selected current : I.TargetActor root recognition visit successor)
    (different : current ≠ selected) (value : Waves root recognition visit successor) :
    wave root recognition visit successor (.target selected) value (.inr current) = value (.inr current) := by
  classical
  simp [wave,different]
variable (point : I.Carrier root recognition visit successor)
variable (word : List (I.Letter root recognition visit successor))
def total := SourceGeneratedActionEffectHistory.residual (I.actions root recognition visit successor transition alignment U7 calculus count)
  (wave root recognition visit successor)
  ((measurement root recognition visit successor transition alignment U7 calculus count).comp
    (I.projection root recognition visit successor transition alignment U7 calculus count)) word point
abbrev generatedSum := SourceGeneratedActionEffectHistory.accumulated (I.actions root recognition visit successor transition alignment U7 calculus count)
  (wave root recognition visit successor)
  ((measurement root recognition visit successor transition alignment U7 calculus count).comp
    (I.projection root recognition visit successor transition alignment U7 calculus count)) word point

theorem sum_equation : generatedSum root recognition visit successor transition alignment U7 calculus count point word =
    total root recognition visit successor transition alignment U7 calculus count point word := SourceGeneratedActionEffectHistory.accumulated_eq _ _ _ _ _
abbrev observe := (measurement root recognition visit successor transition alignment U7 calculus count).comp
  (I.projection root recognition visit successor transition alignment U7 calculus count)
abbrev sourceHistory := SourceGeneratedActionEffectHistory.history (I.actions root recognition visit successor transition alignment U7 calculus count)
  (wave root recognition visit successor) (observe root recognition visit successor transition alignment U7 calculus count) word point

theorem source_single (selected : I.SourceActor root recognition visit) :
    total root recognition visit successor transition alignment U7 calculus count point [.source selected] (.inl selected) =
      SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.effect
        root recognition visit successor transition alignment U7 calculus count (.inl selected)
        (I.projection root recognition visit successor transition alignment U7 calculus count point) := by
  change wave root recognition visit successor (.source selected)
      (measurement root recognition visit successor transition alignment U7 calculus count
        (I.projection root recognition visit successor transition alignment U7 calculus count point)) (.inl selected) -
    C.feature root recognition visit successor transition alignment U7 calculus count (.inl selected)
      (I.projection root recognition visit successor transition alignment U7 calculus count
        (I.actions root recognition visit successor transition alignment U7 calculus count (.source selected) point)) = _
  rw [wave_source]
  exact (SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.effect_source
    root recognition visit successor transition alignment U7 calculus count (.inl selected) point).symm.trans (by rfl)

theorem target_single (selected : I.TargetActor root recognition visit successor) :
    total root recognition visit successor transition alignment U7 calculus count point [.target selected] (.inr selected) =
      SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.effect
        root recognition visit successor transition alignment U7 calculus count (.inr selected)
        (I.projection root recognition visit successor transition alignment U7 calculus count point) := by
  change wave root recognition visit successor (.target selected)
      (measurement root recognition visit successor transition alignment U7 calculus count
        (I.projection root recognition visit successor transition alignment U7 calculus count point)) (.inr selected) -
    C.feature root recognition visit successor transition alignment U7 calculus count (.inr selected)
      (I.projection root recognition visit successor transition alignment U7 calculus count
        (I.actions root recognition visit successor transition alignment U7 calculus count (.target selected) point)) = _
  rw [wave_target]
  exact (SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.effect_source
    root recognition visit successor transition alignment U7 calculus count (.inr selected) point).symm.trans (by rfl)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
