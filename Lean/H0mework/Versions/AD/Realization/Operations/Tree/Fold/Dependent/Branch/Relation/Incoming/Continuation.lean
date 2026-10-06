import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Transport
import H0mework.Realization.Logic.FibreLift
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev completionMap (count : Nat) := CofinalHistoryTransition.GeneratedTransition.completionMap
  (combined root visit recognition count) (combined root visit recognition (count+1))
    (transition root visit recognition count)
abbrev generatorMap (count : Nat) := CofinalHistoryTransition.GeneratedTransition.generatorMap
  (combined root visit recognition count) (combined root visit recognition (count+1))
    (transition root visit recognition count)

theorem actual_word (count : Nat) (word : (combined root visit recognition count).generatorClosure) :
    completionMap root visit recognition count ((combined root visit recognition count).completionProjection word) =
      (combined root visit recognition (count+1)).completionProjection (generatorMap root visit recognition count word) :=
  CofinalHistoryTransition.GeneratedTransition.completionMap_projection _ _ _ word

theorem fibre_zero (count : Nat) (word : (combined root visit recognition count).generatorClosure) :
    completionMap root visit recognition count ((combined root visit recognition count).completionProjection word) = 0 ↔
      word.val ∈ (combined root visit recognition (count+1)).relationClosure :=
  SourceHistoryCommon.transition_fibre_zero _ _ (transition root visit recognition count) word

open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

theorem soundness (count : Nat) : GeneratedRelationSoundnessAt (face root visit recognition count) :=
  match (face root visit recognition count).settleRelations with
  | .sound generated => generated
  | .unsound impossible => False.elim (impossible.notSound (relations_sound root visit recognition count))

abbrev sourceEvaluation (count : Nat) := (face root visit recognition count).completionEvaluation (soundness root visit recognition count)
abbrev targetEvaluation (count : Nat) := (face root visit recognition (count+1)).completionEvaluation (soundness root visit recognition (count+1))

theorem evaluation_square (count : Nat) (word : (combined root visit recognition count).generatorClosure) :
    targetEvaluation root visit recognition count
      (completionMap root visit recognition count ((combined root visit recognition count).completionProjection word)) =
    sourceEvaluation root visit recognition count ((combined root visit recognition count).completionProjection word) := by
  rw [actual_word]
  change (face root visit recognition (count+1)).freeEvaluation word.val =
    (face root visit recognition count).freeEvaluation word.val
  exact (word_read root visit recognition (count+1) word.val).trans
    (word_read root visit recognition count word.val).symm
theorem full_evaluation_square (count : Nat) (value : (combined root visit recognition count).CompletionCarrier) :
    targetEvaluation root visit recognition count (completionMap root visit recognition count value) =
      sourceEvaluation root visit recognition count value := by
  refine Submodule.Quotient.induction_on (combined root visit recognition count).relationInGeneratorClosure value ?_
  intro word
  exact evaluation_square root visit recognition count word

open SourceGeneratedScalarDifferentialResidual SourceOperationLogic SourceOperationLogic.FibreLift

def morphism (count : Nat) : Morphism (sourceEvaluation root visit recognition count)
    (targetEvaluation root visit recognition count) where
  sourceMap := completionMap root visit recognition count
  targetMap := LinearMap.id
  commutes := by
    apply LinearMap.ext
    intro value
    exact (full_evaluation_square root visit recognition count value).symm
abbrev kernelTransport (count : Nat) := kernelMap (morphism root visit recognition count)
abbrev inverseTransport (count : Nat) := mapFibre (morphism root visit recognition count)
abbrev residualTransport (count : Nat) := liftingResidual (morphism root visit recognition count)
theorem inverse_fibre (count : Nat) (value : (combined root visit recognition count).CompletionCarrier)
    (target : Fibre (targetEvaluation root visit recognition count)
      (q (targetEvaluation root visit recognition count) (completionMap root visit recognition count value))) :
    residualTransport root visit recognition count value target = 0 ↔
      ∃ representative : Fibre (sourceEvaluation root visit recognition count)
        (q (sourceEvaluation root visit recognition count) value),
        inverseTransport root visit recognition count value representative = target :=
  liftingResidual_eq_zero_iff _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
