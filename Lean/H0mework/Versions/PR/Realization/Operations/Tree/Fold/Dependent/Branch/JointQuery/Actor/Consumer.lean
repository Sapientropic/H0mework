import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RootLawDependentJointStateController.RecognitionAt H root)
theorem source_inventory : (expression root visit recognition).eval (environment root visit recognition) =
    ((Q.expression root visit recognition).eval (Q.environment root visit recognition),
      (Finsupp.single (oldActor root visit recognition) 1,
        Finsupp.single (nextActor root visit recognition) 1 - Finsupp.single (oldActor root visit recognition) 1)) := by
  change projection root visit recognition ((Extension.embed _ _ _ (Q.expression root visit recognition)).eval _) = _
  rw [Extension.embed_eval]
  apply Prod.ext
  · rfl
  · change completePairMap root visit recognition
      ((Q.expression root visit recognition).eval (Q.environment root visit recognition) 0) = _
    rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.core_inventory]
    change (Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
      (Finsupp.single (B.outcome root visit recognition) (1:ℤ)),
      Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
        (Finsupp.single (B.nextOutcome root visit recognition) (1:ℤ) -
          Finsupp.single (B.outcome root visit recognition) (1:ℤ))) = _
    simp only [Finsupp.mapDomain_sub,Finsupp.mapDomain_single]
theorem actual_paid_inventory : (paid root visit recognition).2.2.1 =
    ((Q.expression root visit recognition).eval (Q.environment root visit recognition),
      (Finsupp.single (oldActor root visit recognition) 1,
        Finsupp.single (nextActor root visit recognition) 1 - Finsupp.single (oldActor root visit recognition) 1)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (source_inventory root visit recognition)
theorem actual_next_actor : (paid root visit recognition).2.2.1.2.1 + (paid root visit recognition).2.2.1.2.2 =
    Finsupp.single (nextActor root visit recognition) 1 := by
  rw [actual_paid_inventory]
  exact add_sub_cancel _ _
theorem trace_fee : (trace root visit recognition).length = remaining (Q.expression root visit recognition) + 1 := by
  rw [trace,execution_length]
  change remaining (Extension.embed _ _ _ (Q.expression root visit recognition)) + 1 = _
  rw [Extension.embed_charge]
theorem paid_fee : (paid root visit recognition).2.1.2.length = (originalPaid root visit recognition).2.1.2.length + 1 := by
  have paidFee := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    root.toAuthoritativeRoot (reader root visit recognition) (root.emitted visit.current)
  have originalFee := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    root.toAuthoritativeRoot (fun {_current} _ => Q.raw root visit recognition) (root.emitted visit.current)
  calc
    _ = remaining (expression root visit recognition) := paidFee
    _ = remaining (Q.expression root visit recognition) + 1 := by
      change remaining (Extension.embed _ _ _ (Q.expression root visit recognition)) + 1 = _
      rw [Extension.embed_charge]
    _ = _ := congrArg (· + 1) originalFee.symm
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
