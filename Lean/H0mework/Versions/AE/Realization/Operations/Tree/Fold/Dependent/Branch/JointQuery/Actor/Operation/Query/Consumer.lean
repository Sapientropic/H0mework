import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Source
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RootLawDependentJointStateController.RecognitionAt H root)
theorem source_inventory : (expression root visit recognition).eval (environment root visit recognition) =
    ((A.expression root visit recognition).eval (A.environment root visit recognition),
      (Finsupp.single (function root recognition (A.oldActor root visit recognition)) 1,
        Finsupp.single (function root recognition (A.nextActor root visit recognition)) 1 -
          Finsupp.single (function root recognition (A.oldActor root visit recognition)) 1)) := by
  change projection root visit recognition ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed
    _ _ _ (A.expression root visit recognition)).eval _) = _
  rw [environment,SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed_eval]
  apply Prod.ext
  · rfl
  · change functionPairMap root recognition
      ((A.expression root visit recognition).eval (A.environment root visit recognition)).2 = _
    rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.source_inventory]
    change (Finsupp.mapDomain (function root recognition) (Finsupp.single (A.oldActor root visit recognition) (1:ℤ)),
      Finsupp.mapDomain (function root recognition)
        (Finsupp.single (A.nextActor root visit recognition) (1:ℤ) - Finsupp.single (A.oldActor root visit recognition) 1)) = _
    simp only [Finsupp.mapDomain_sub,Finsupp.mapDomain_single]

theorem paid_inventory : (paid root visit recognition).2.2.1 =
    ((A.expression root visit recognition).eval (A.environment root visit recognition),
      (Finsupp.single (function root recognition (A.oldActor root visit recognition)) 1,
        Finsupp.single (function root recognition (A.nextActor root visit recognition)) 1 -
          Finsupp.single (function root recognition (A.oldActor root visit recognition)) 1)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    root.toAuthoritativeRoot (reader root visit recognition) (root.emitted visit.current)).trans
      (source_inventory root visit recognition)

theorem actual_bundle : function root recognition (A.nextActor root visit recognition) =
    O.sourceOperation root visit recognition := rfl

theorem actual_next_operation : (paid root visit recognition).2.2.1.2.1 +
    (paid root visit recognition).2.2.1.2.2 = Finsupp.single (O.sourceOperation root visit recognition) 1 := by
  rw [paid_inventory,actual_bundle]
  exact add_sub_cancel _ _

theorem trace_fee : (trace root visit recognition).length = remaining (A.expression root visit recognition) + 1 := by
  rw [trace,execution_length]
  change remaining (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed
    _ _ _ (A.expression root visit recognition)) + 1 = _
  rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed_charge]

theorem paid_fee : (paid root visit recognition).2.1.2.length = (A.paid root visit recognition).2.1.2.length + 1 := by
  have current := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    root.toAuthoritativeRoot (reader root visit recognition) (root.emitted visit.current)
  have original := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    root.toAuthoritativeRoot
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.reader root visit recognition) (root.emitted visit.current)
  calc
    _ = remaining (expression root visit recognition) := current
    _ = remaining (A.expression root visit recognition) + 1 := by
      change remaining (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed
        _ _ _ (A.expression root visit recognition)) + 1 = _
      rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed_charge]
    _ = _ := congrArg (·+1) original.symm

theorem embed_output (term : Expr (A.Value root visit recognition) (A.Variable root visit recognition) (.inr PUnit.unit)) :
    (embedOutput root visit recognition term).eval (environment root visit recognition) =
      (term.eval (A.environment root visit recognition),0) := by
  change ((AddMonoidHom.id _).prod (0:A.Output root visit recognition →+ FunctionPair root recognition))
    ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed _ _ _ term).eval _) = _
  rw [environment,SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed_eval]
  rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
