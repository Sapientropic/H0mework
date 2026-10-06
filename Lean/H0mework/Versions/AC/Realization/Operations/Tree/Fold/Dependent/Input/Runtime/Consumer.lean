import H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Source
/-! The original source code/tree and full mathematical state are read from
this existing runtime. Complete material, canonical whole-next and every
Shared query/answer remain restrictions of the source-owned construction. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Input.Runtime
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (old : RootInquiryStateAt N V) (recognition : RecognitionAt H old.root)
variable (original : SourceNativeRootInquiryInputAt old.root old.visit old.Query)
variable (next : StepLedgerSuccessorAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition))
variable (history : GeneratedStepJointTransitionAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next)
variable (zip : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition))
  (stepTargetPairingOccurrence (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next))

theorem source_raw : RootGeneratedDebtActivationJointSource.OwnerFree.raw
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip) =
      (actualInput old recognition original next history zip).query.raw := rfl

theorem original_tree : SourceOperationNative.Tree.Fold.Inverse.readTree
    (RootGeneratedDebtActivationJointSource.OwnerFree.raw
      (actualState old recognition original next history zip).root.toAuthoritativeRoot
      (actualState old recognition original next history zip).visit.current
      (reader old recognition original next history zip)).expression =
    some (D.nativeTree (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next history zip) :=
  SourceOperationNative.Tree.Fold.Dependent.Input.actual_tree old recognition original next history zip

theorem actual_normal_history : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip)).length =
    SourceOperationNative.Tree.Fold.budget
      (D.nativeTree (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next history zip) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip)).trans (SourceOperationNative.Tree.Fold.program_budget _ _)


theorem actual_normal_value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip) =
    Finsupp.single (settleTree (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition)
      next history.history (D.nativeTree (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next history zip)) 1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip)).trans (SourceOperationNative.Tree.Fold.program_value _ _)

theorem actual_math_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualState old recognition original next history zip).root.toAuthoritativeRoot
      (actualState old recognition original next history zip).visit.current
      (reader old recognition original next history zip) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualState old recognition original next history zip).root.toAuthoritativeRoot
    (actualState old recognition original next history zip).visit.current
    (reader old recognition original next history zip) count

theorem actual_source_material (count : Nat) : type_of% (M.original_material
    (actualState old recognition original next history zip) (reader old recognition original next history zip) count) :=
  M.original_material (actualState old recognition original next history zip) (reader old recognition original next history zip) count

theorem actual_query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualState old recognition original next history zip)
      (reader old recognition original next history zip) offset) ∧
    type_of% (M.activated_answer (actualState old recognition original next history zip)
      (reader old recognition original next history zip) offset) ∧
    type_of% (M.activated_next (actualState old recognition original next history zip)
      (reader old recognition original next history zip) offset) :=
  ⟨M.activated_query (actualState old recognition original next history zip) (reader old recognition original next history zip) offset,
    M.activated_answer (actualState old recognition original next history zip) (reader old recognition original next history zip) offset,
    M.activated_next (actualState old recognition original next history zip) (reader old recognition original next history zip) offset⟩



end SourceOperationNative.Tree.Fold.Dependent.Input.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
