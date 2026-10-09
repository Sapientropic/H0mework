import H0mework.Versions.R9c73a630.Realization.Perfectification.Occurrence.Temporal.History.Common.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment no_refill wellFounded)
end P
open CofinalHistoryTransition

theorem actual_target : successor.targetOccurrence = root.emitted successor.targetCurrent :=
  successor_targetOccurrence_eq_emitted (step root visit recognition) successor

theorem normal : O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) =
    Finsupp.single (actualRaw root visit recognition successor) 1 :=
  (O.value_source root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans
    (SourceNativeBinary.lift_point _ _ _)

theorem cost : (O.trace root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).length = 3 :=
  (O.paid_history root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans (by rfl)

abbrev payment (count : Fin 3) := P.activePayment root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)
  ⟨count.1, by exact count.2⟩

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)

theorem source_completion (word : (sourceHistory root visit recognition).generatorClosure) :
    GeneratedTransition.completionMap (sourceHistory root visit recognition) (common root visit recognition successor)
      (left root visit recognition successor) ((sourceHistory root visit recognition).completionProjection word) =
      (common root visit recognition successor).completionProjection
        (GeneratedTransition.generatorMap (sourceHistory root visit recognition) (common root visit recognition successor)
          (left root visit recognition successor) word) :=
  GeneratedTransition.completionMap_projection _ _ _ _

theorem target_completion (word : (targetHistory root visit recognition successor).generatorClosure) :
    GeneratedTransition.completionMap (targetHistory root visit recognition successor) (common root visit recognition successor)
      (right root visit recognition successor) ((targetHistory root visit recognition successor).completionProjection word) =
      (common root visit recognition successor).completionProjection
        (GeneratedTransition.generatorMap (targetHistory root visit recognition successor) (common root visit recognition successor)
          (right root visit recognition successor) word) :=
  GeneratedTransition.completionMap_projection _ _ _ _

theorem source_inverse_fibre (word : (sourceHistory root visit recognition).generatorClosure) : type_of%
    (SourceHistoryCommon.left_fibre_zero (sourceHistory root visit recognition) (targetHistory root visit recognition successor)
      (RootedAccountedUnfolding.zero (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit)) word) :=
  SourceHistoryCommon.left_fibre_zero _ _ _ _

theorem target_inverse_fibre (word : (targetHistory root visit recognition successor).generatorClosure) : type_of%
    (SourceHistoryCommon.right_fibre_zero (sourceHistory root visit recognition) (targetHistory root visit recognition successor)
      (RootedAccountedUnfolding.zero (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit)) word) :=
  SourceHistoryCommon.right_fibre_zero _ _ _ _

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem history_read (count : Nat) : decodedHistory root visit recognition successor U7 calculus count =
    common root visit recognition successor := rfl

theorem source_action_read (count : Nat) : (face root visit recognition successor U7 calculus count).rootRead.1.source =
    sourceRaw root visit recognition := rfl

theorem target_action_read (count : Nat) : (face root visit recognition successor U7 calculus count).rootRead.1.target =
    targetRaw root visit recognition successor := rfl

theorem parent_next (count : Nat) : root.generatedNextCurrentAt
    (SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot
      (face root visit recognition successor U7 calculus count).rootRead.1.receipt.1) = root.generatedNextCurrentAt visit :=
  congrArg root.generatedNextCurrentAt (SourceTemporalMaterial.decode_encode _ _)

namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset⟩
theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
      (installedReader root visit recognition successor) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor) count
end SourceHistoryCommon.Root
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
