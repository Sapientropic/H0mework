import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.Installation
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.Consumer
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment activeContinuation no_refill wellFounded)
end P

theorem normal_inventory : O.value root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment) =
      (Finsupp.single (sourceOutcome root visit recognition successor transition alignment) 1,
        Finsupp.single (targetOutcome root visit recognition successor transition alignment) 1 -
          Finsupp.single (sourceOutcome root visit recognition successor transition alignment) 1) :=
  (O.value_source root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment)).trans
      (full_inventory root visit recognition successor transition alignment)

theorem original_effect : (sourceOutcome root visit recognition successor transition alignment).1 =
    settleTree (step root visit recognition) successor transition.history
      (D.nativeTree (step root visit recognition) successor transition alignment) := by
  rw [sourceOutcome, fold_original, original_tree]
  rfl

theorem temporal_receipt : (sourceOutcome root visit recognition successor transition alignment).2.1.root =
    T.actual root (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit) := by
  rw [sourceOutcome, fold_time, RootedAccountedUnfolding.root_map, tree, RootedAccountedUnfolding.root_map]


theorem original_visit : SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot
    (sourceOutcome root visit recognition successor transition alignment).2.1.root.1.1 = visit := by
  rw [temporal_receipt]
  exact SourceTemporalMaterial.decode_encode _ _

private theorem pair_remaining {Sorts : Type u} {Val Variables : Sorts → Type u}
    [∀ slot, AddCommGroup (Val slot)] {slot : Sorts} (term : Expr Val Variables slot) :
    remaining (liftExpr term) = remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add _ _ first second => simp only [liftExpr, remaining, first, second]
  | linear _ _ prior => simp only [liftExpr, remaining, prior]
  | bilinear _ _ _ first second => simp only [liftExpr, remaining, first, second]

theorem cost : (O.trace root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment)).length =
      F.budget (tree root visit recognition successor transition alignment) :=
  (O.paid_history root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment)).trans
      ((pair_remaining (programme root visit recognition successor transition alignment)).trans
        (F.program_budget _ _))

theorem inverse_read : type_of% ((sourceTrace root visit recognition successor transition alignment).updated_residual
    (R:=ℤ) (delta root visit recognition successor transition)) :=
  (sourceTrace root visit recognition successor transition alignment).updated_residual (R:=ℤ)
    (delta root visit recognition successor transition)

theorem exact_inverse_fibre : type_of% (SourceOperationLogic.FibreLift.liftingResidual_eq_zero_iff
    (morphism root visit recognition successor transition)
    (oldWord root visit recognition successor transition alignment) (target root visit recognition successor transition alignment)) :=
  SourceOperationLogic.FibreLift.liftingResidual_eq_zero_iff _ _ _

abbrev payment (count : Fin (remaining (raw root visit recognition successor transition alignment).expression)) :=
  P.activePayment root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment) count

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor transition alignment) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor transition alignment)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
abbrev actualRoot := C.sourceRoot (sourceRoot root visit recognition successor transition alignment)
  (sourceVisit root visit recognition successor transition alignment)
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset,
    M.activated_answer (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset,
    M.activated_next (actualRoot root visit recognition successor transition alignment) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) offset⟩
theorem recovered_tree (count : Nat) : SourceOperationNative.Tree.Fold.Inverse.readTree
    (face root visit recognition successor transition alignment U7 calculus count).rootRead.2.1 =
      some (tree root visit recognition successor transition alignment) :=
  SourceOperationNative.Tree.Fold.Inverse.read_program _ _

theorem recovered_original_tree (count : Nat) :
    (face root visit recognition successor transition alignment U7 calculus count).rootRead.1.map Prod.fst =
      D.nativeTree (step root visit recognition) successor transition alignment :=
  original_tree root visit recognition successor transition alignment

theorem retained_inverse (count : Nat) :
    (face root visit recognition successor transition alignment U7 calculus count).rootRead.2.2.2.2 =
      reverse root visit recognition successor transition alignment := rfl

theorem original_parent_next (count : Nat) : root.generatedNextCurrentAt
    (SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot
      (face root visit recognition successor transition alignment U7 calculus count).rootRead.1.root.2) =
        root.generatedNextCurrentAt visit := by
  change root.generatedNextCurrentAt (SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot
    (tree root visit recognition successor transition alignment).root.2) = _
  rw [tree, RootedAccountedUnfolding.root_map]
  exact congrArg root.generatedNextCurrentAt (SourceTemporalMaterial.decode_encode root.toAuthoritativeRoot.toLedgerRoot visit)

theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualRoot root visit recognition successor transition alignment).toAuthoritativeRoot visit.current
      (installedReader root visit recognition successor transition alignment) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition successor transition alignment).toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor transition alignment) count
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
