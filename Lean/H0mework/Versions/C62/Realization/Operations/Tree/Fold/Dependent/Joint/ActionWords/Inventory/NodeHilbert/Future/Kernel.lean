import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Observation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
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

theorem all_prefix_zero (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (∀ bound, observation root recognition visit successor transition alignment U7 calculus count bound value=0) ↔
    ∀ letters : List (Letter root recognition visit successor), ∀ selected : Covariance.Actor root recognition visit successor,
      Covariance.feature root recognition visit successor transition alignment U7 calculus count selected
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters value)=0 := by
  constructor
  · intro vanish letters selected
    obtain ⟨code,same⟩ := word_coverage root recognition visit successor letters.length letters le_rfl
    obtain ⟨index,rfl⟩ := actor_surjective root recognition visit successor selected
    have coordinate := congrArg (fun values : Space root recognition visit successor letters.length => values (code,index)) (vanish letters.length)
    rw [cell_read,same] at coordinate
    exact coordinate
  · intro vanish bound
    apply (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).injective
    funext cell
    exact vanish (word root recognition visit successor cell.1) (actor root recognition visit successor cell.2)

abbrev inventory := SourceGeneratedActionWords.inventory
  (advance root recognition visit successor transition alignment U7 calculus count)
  (NodeHilbert.measurement root recognition visit successor transition alignment U7 calculus count)
theorem prefix_kernel (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (∀ bound, observation root recognition visit successor transition alignment U7 calculus count bound value=0) ↔
      inventory root recognition visit successor transition alignment U7 calculus count value=0 := by
  rw [all_prefix_zero]
  constructor
  · intro vanish
    funext letters
    apply (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).injective
    funext index
    exact vanish letters (actor root recognition visit successor index)
  · intro invisible letters selected
    obtain ⟨index,rfl⟩ := actor_surjective root recognition visit successor selected
    exact congrArg (fun reads => (reads letters : NodeHilbert.Space root recognition visit successor) index) invisible

theorem source_kernel (value : Model root recognition visit successor transition alignment U7 calculus count) :
    sourceMap root recognition visit successor transition alignment U7 calculus count value=0 ↔
      inventory root recognition visit successor transition alignment U7 calculus count value=0 := by
  rw [← prefix_kernel]
  constructor
  · intro invisible bound
    exact (data root recognition visit successor transition alignment U7 calculus count).evaluator_eq_zero_of_completionMap_eq_zero
      (compatible root recognition visit successor transition alignment U7 calculus count) value invisible bound
  · intro vanish
    apply CategoryTheory.Limits.Concrete.limit_ext
      ((data root recognition visit successor transition alignment U7 calculus count).quotientTower
        (compatible root recognition visit successor transition alignment U7 calculus count))
    intro stage
    have square := CategoryTheory.ConcreteCategory.congr_hom
      ((data root recognition visit successor transition alignment U7 calculus count).completionMap_restriction
        (compatible root recognition visit successor transition alignment U7 calculus count) stage.unop) value
    have quotientZero : (data root recognition visit successor transition alignment U7 calculus count).quotientMap stage.unop value=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (vanish stage.unop)
    exact square.trans (quotientZero.trans (map_zero _).symm)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
