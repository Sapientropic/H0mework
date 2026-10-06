import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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

theorem embed_run (word : List ActionWords.Letter.{u}) (value : Carrier root recognition visit successor) :
    SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count)
      (word.map (embed root recognition visit successor)) value =
        SourceGeneratedActionWords.run (ActionWords.actions root recognition visit successor transition alignment U7 calculus count) word value := by
  induction word generalizing value with
  | nil => rfl
  | cons letter rest previous =>
      change SourceGeneratedActionWords.run _ (rest.map _) (actions _ _ _ _ _ _ _ _ _ (embed _ _ _ _ letter) value) = _
      rw [embed_action,previous]
      rfl

private theorem oldKernel :
    LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
      (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
      (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
        (read root recognition visit successor transition alignment U7 calculus count))) ≤
    LinearMap.ker (ActionWords.projection root recognition visit successor transition alignment U7 calculus count) := by
  intro value invisible
  apply (SourceGeneratedScalarDifferentialResidual.canonicalResidual_eq_zero_iff _ _).mpr
  change value ∈ LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
    (ActionWords.actions root recognition visit successor transition alignment U7 calculus count ActionWords.Letter.simultaneous.{u})
    (SourceGeneratedActionWords.inventory (ActionWords.actions root recognition visit successor transition alignment U7 calculus count)
      (ActionWords.read root recognition visit successor transition alignment U7 calculus count)))
  rw [SourceGeneratedActionWords.original_kernel]
  rw [SourceGeneratedActionWords.original_kernel] at invisible
  apply LinearMap.mem_ker.mpr
  funext word
  have observed := congrArg Prod.fst (congrFun invisible (word.map (embed root recognition visit successor)))
  change coarseRead root recognition visit successor transition alignment U7 calculus count
    (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count)
      (word.map (embed root recognition visit successor)) value) = 0 at observed
  rw [embed_run] at observed
  exact observed

def oldModelRestriction : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    ActionWords.Model root recognition visit successor transition alignment U7 calculus count :=
  (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
    (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
    (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
      (read root recognition visit successor transition alignment U7 calculus count)))).liftQ
      (ActionWords.projection root recognition visit successor transition alignment U7 calculus count)
      (oldKernel root recognition visit successor transition alignment U7 calculus count)

theorem old_model_source (value : Carrier root recognition visit successor) :
    oldModelRestriction root recognition visit successor transition alignment U7 calculus count
      (projection root recognition visit successor transition alignment U7 calculus count value) =
        ActionWords.projection root recognition visit successor transition alignment U7 calculus count value := rfl
private theorem coarseKernel :
    LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
      (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
      (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
        (read root recognition visit successor transition alignment U7 calculus count))) ≤
    LinearMap.ker (SourceGeneratedActionWords.projection
      (actions root recognition visit successor transition alignment U7 calculus count)
      (coarseRead root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor)) := by
  intro value invisible
  apply (SourceGeneratedScalarDifferentialResidual.canonicalResidual_eq_zero_iff _ _).mpr
  change value ∈ LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
    (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
    (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
      (coarseRead root recognition visit successor transition alignment U7 calculus count)))
  rw [SourceGeneratedActionWords.original_kernel]
  rw [SourceGeneratedActionWords.original_kernel] at invisible
  apply LinearMap.mem_ker.mpr
  funext word
  exact congrArg Prod.fst (congrFun invisible word)

def coarseRestriction : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    CoarseModel root recognition visit successor transition alignment U7 calculus count :=
  (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
    (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
    (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
      (read root recognition visit successor transition alignment U7 calculus count)))).liftQ
      (SourceGeneratedActionWords.projection (actions root recognition visit successor transition alignment U7 calculus count)
        (coarseRead root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor))
      (coarseKernel root recognition visit successor transition alignment U7 calculus count)

theorem coarse_source (value : Carrier root recognition visit successor) :
    coarseRestriction root recognition visit successor transition alignment U7 calculus count
      (projection root recognition visit successor transition alignment U7 calculus count value) =
        SourceGeneratedActionWords.projection (actions root recognition visit successor transition alignment U7 calculus count)
          (coarseRead root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor) value := rfl

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
