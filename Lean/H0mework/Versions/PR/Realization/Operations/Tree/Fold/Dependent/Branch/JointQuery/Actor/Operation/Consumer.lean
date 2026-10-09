import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Consumer

set_option autoImplicit false
noncomputable section
universe u w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open RootLawDependentJointStateController RootLawDependentJointTransition
namespace SomePacket
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
variable (data : Data root recognition code successor)
variable (source_eq : sourceSeed root recognition code successor data = (SourceHistory root recognition code).seed)
variable (target_eq : targetSeed root recognition code successor data = (TargetHistory root recognition code successor).seed)
theorem source_environment (slot : PUnit.{u+1}) (index : Index root recognition code successor data) :
    (binding root recognition code successor data slot ⟨index⟩).eval
      (environment root recognition code successor data source_eq target_eq) =
      action root recognition code successor data index
        (point root recognition code successor data source_eq target_eq index) := rfl
theorem paid_trace : (trace root recognition code successor data source_eq target_eq).length =
    InventoryVector.charge (Index root recognition code successor data) (items root recognition code successor data) :=
  (execution_length _ _).trans (InventoryVector.query_charge _ _)
theorem query_content (coordinate : Index root recognition code successor data) :
    (raw root recognition code successor data source_eq target_eq).expression.eval
      (raw root recognition code successor data source_eq target_eq).environment coordinate =
    ((indices root recognition code successor data).map (fun index => if coordinate=index then
      action root recognition code successor data index
        (point root recognition code successor data source_eq target_eq index) else 0)).sum := by
  have read := InventoryVector.query_read (Index root recognition code successor data)
    (items root recognition code successor data)
    (environment root recognition code successor data source_eq target_eq) coordinate
  simpa only [raw,expression,items,List.map_map,Function.comp_def,source_environment] using read

theorem indices_complete (index : Index root recognition code successor data) :
    index ∈ indices root recognition code successor data := by
  rcases index with ⟨first,second⟩ | (⟨first,second⟩ | ⟨first,second⟩)
  all_goals simp only [indices,List.mem_append,List.mem_flatten,List.mem_ofFn]
  all_goals aesop


theorem paid_value (coordinate : Index root recognition code successor data) :
    (paid root recognition code successor data source_eq target_eq).2.2.1 coordinate =
      ((indices root recognition code successor data).map (fun index => if coordinate=index then
        action root recognition code successor data index
          (point root recognition code successor data source_eq target_eq index) else 0)).sum :=
  (congrFun (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    root.toAuthoritativeRoot (reader root recognition code successor data source_eq target_eq)
    (root.emitted (currentVisit root code).current)) coordinate).trans
      (query_content root recognition code successor data source_eq target_eq coordinate)

theorem exact_fee : (trace root recognition code successor data source_eq target_eq).length =
    (indices root recognition code successor data).length * 4 := by
  rw [paid_trace]
  have fee (rows : List (Index root recognition code successor data)) :
      InventoryVector.charge (Index root recognition code successor data)
        (rows.map (fun index => (index,binding root recognition code successor data PUnit.unit ⟨index⟩))) =
      rows.length * 4 := by
    induction rows with
    | nil => rfl
    | cons head tail previous =>
        rw [List.map_cons,InventoryVector.charge,previous]
        simp only [List.length_cons,binding,remaining]
        omega
  exact fee _

theorem actual_paid_fee : (paid root recognition code successor data source_eq target_eq).2.1.2.length =
    (indices root recognition code successor data).length * 4 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    root.toAuthoritativeRoot (reader root recognition code successor data source_eq target_eq)
    (root.emitted (currentVisit root code).current)).trans
      ((execution_length _ _).symm.trans (exact_fee root recognition code successor data source_eq target_eq))
end SomePacket

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
theorem actual_actor : (sourceOperation root visit recognition).1 =
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.nextActor root visit recognition := rfl
theorem actual_packet : (sourceOperation root visit recognition).1.1 =
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.nextActor root visit recognition).1 := rfl
theorem actual_paid_actor : (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.paid root visit recognition).2.2.1.2.1 +
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.paid root visit recognition).2.2.1.2.2 =
    Finsupp.single (sourceOperation root visit recognition).1 1 :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.actual_next_actor root visit recognition
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
