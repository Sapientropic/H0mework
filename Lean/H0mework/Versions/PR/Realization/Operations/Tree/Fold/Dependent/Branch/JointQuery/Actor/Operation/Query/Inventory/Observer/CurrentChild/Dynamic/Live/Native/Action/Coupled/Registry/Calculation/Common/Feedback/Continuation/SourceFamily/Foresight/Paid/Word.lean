import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Effect
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Paid
namespace U
export Lower.SourceFamily.Foresight.Update (decoder increment nextEnv actual_environment actual_word)
end U
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance groups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (scalar₁ scalar₂ : Lower.SourceFamily.Seed W X s (n+1))
variable (pair₁ pair₂ : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s)))
theorem decoder_stock_independent : U.decoder binding n seed frame scalar₁ pair₁=U.decoder binding n seed frame scalar₂ pair₂ := rfl
theorem increment_stock_independent : U.increment binding n seed frame scalar₁ pair₁=U.increment binding n seed frame scalar₂ pair₂ := rfl
theorem environment_stock_independent : U.nextEnv binding n seed frame scalar₁ pair₁=U.nextEnv binding n seed frame scalar₂ pair₂ :=
 (U.actual_environment binding n seed frame scalar₁ pair₁).trans
 ((congrArg₂ pairEnvironment (decoder_stock_independent binding n seed frame scalar₁ scalar₂ pair₁ pair₂)
  (increment_stock_independent binding n seed frame scalar₁ scalar₂ pair₁ pair₂)).trans
 (U.actual_environment binding n seed frame scalar₂ pair₂).symm)

variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
def sourceScalar := Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.factory (s:=s) binding) n data
def sourcePair := Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.factory (s:=s) binding) n data
def sourceEnv := U.nextEnv binding n data.2 data.1 (sourceScalar binding n data) (sourcePair binding n data)
abbrev Word (t : S) := Formal ℤ (PairValue (Lower.Value W n)) X t
def expression (t : S) (word : Word (W:=W) (X:=X) n t) := Coefficients.expression (liftMap (R:=ℤ) word)
def raw (t : S) (word : Word (W:=W) (X:=X) n t) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (Lower.Value W (n+1))) (Var:=X) (sort:=t) :=
 ⟨sourceEnv binding n data,expression (W:=W) (X:=X) n t word⟩
def result (t : S) (word : Word (W:=W) (X:=X) n t) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base data.1).root.toAuthoritativeRoot
  (fun {_current} _ => raw binding n data t word)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence data.1)
abbrev paidTrace (t : S) (word : Word (W:=W) (X:=X) n t) := (result binding n data t word).2.1.2
def writtenAt (word : Word (W:=W) (X:=X) n s) := SourceOperationPaidRelations.exposure (paidTrace binding n data s word)
theorem source_action_value (t : S) (word : Word (W:=W) (X:=X) n t) : (result binding n data t word).2.2.1=
 updateInventory (R:=ℤ) (s:=t)
 (U.decoder binding n data.2 data.1 (sourceScalar binding n data) (sourcePair binding n data))
 (U.increment binding n data.2 data.1 (sourceScalar binding n data) (sourcePair binding n data)) word :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
 ((Coefficients.expression_eval _ _).trans
 (U.actual_word binding n data.2 data.1 (sourceScalar binding n data) (sourcePair binding n data) t word))
theorem complete_fee (t : S) (word : Word (W:=W) (X:=X) n t) : (paidTrace binding n data t word).length=
 remaining (expression (W:=W) (X:=X) n t word) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem all_paid_relations (t : S) (word : Word (W:=W) (X:=X) n t) :
 (SourceOperationPaidRelations.words (paidTrace binding n data t word)).length=(paidTrace binding n data t word).length :=
 SourceOperationPaidRelations.complete_steps _
theorem generated_new_kernel (t : S) (word : Word (W:=W) (X:=X) n t) :
 evaluation (R:=ℤ) (sourceEnv binding n data)
  (relationMap (R:=ℤ) (sourceEnv binding n data) ((paidTrace binding n data t word).relationWords (R:=ℤ)))=0 :=
 (paidTrace binding n data t word).relation_old (R:=ℤ)
end Lower.SourceFamily.Foresight.Paid
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

end
