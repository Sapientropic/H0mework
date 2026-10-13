import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Completion.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyActualCurrentMaterialCompletedDisposition

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (state presentation compiles_settled birthProgram target_current successor_valid)
end ST
namespace Registry
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry (query)
end Registry
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn)
end S
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

abbrev completedEvent :=
 (SO.root (completedBorn frame cfg) (AS.stockCfg cfg)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (completedBorn frame cfg) (AS.stockCfg cfg))

def completedAction :=
 (ST.birthProgram (completedBorn frame cfg) (AS.stockCfg cfg)).generate (completedEvent frame cfg)

theorem completed_compiles : type_of% (ST.compiles_settled (completedBorn frame cfg) (AS.stockCfg cfg)
  (completed_born_actual frame cfg).1 (completed_born_actual frame cfg).2.down) :=
 ST.compiles_settled (completedBorn frame cfg) (AS.stockCfg cfg)
  (completed_born_actual frame cfg).1 (completed_born_actual frame cfg).2.down

theorem completed_target_current :
 (completedAction frame cfg).target.targetAnswerAndNext.nextCurrent =
 ⟨_,(SO.root (S.nextBorn (completedBorn frame cfg) (AS.stockCfg cfg)) (AS.stockCfg cfg)).toAuthoritativeRoot,
  SO.visit (S.nextBorn (completedBorn frame cfg) (AS.stockCfg cfg)) (AS.stockCfg cfg)⟩ :=
 ST.target_current (completedBorn frame cfg) (AS.stockCfg cfg) (completedEvent frame cfg)

theorem completed_successor_valid : type_of% (ST.successor_valid (completedBorn frame cfg) (AS.stockCfg cfg)
  (Registry.query (completedBorn frame cfg) (AS.stockCfg cfg))) :=
 ST.successor_valid (completedBorn frame cfg) (AS.stockCfg cfg)
  (Registry.query (completedBorn frame cfg) (AS.stockCfg cfg))

def completedOldRow :=
 let target := (completedAction frame cfg).target
 target.firstSuccessor.ledgerEvolution.destination target.translatedSourceEntry

def completedBornRow :=
 let target := (completedAction frame cfg).target
 target.firstSuccessor.ledgerEvolution.destination target.bornEntry

-- The original action is the dependent carrier; its causal answer and complete rows are consumed directly.
def consume_completed_answer {Result : Sort v}
 (consumer : (generated : type_of% (completedAction frame cfg)) →
  (answer : type_of% generated.target.targetAnswerAndNext.answer) →
  generated.target.Receipt generated.answer →
  type_of% (completed_compiles frame cfg) →
  type_of% (completed_target_current frame cfg) →
  type_of% (completed_successor_valid frame cfg) →
  type_of% generated.target.firstDestination_heq →
  Result) : Result :=
 let generated := completedAction frame cfg
 consumer generated generated.target.targetAnswerAndNext.answer generated.receipt
  (completed_compiles frame cfg) (completed_target_current frame cfg)
  (completed_successor_valid frame cfg) generated.target.firstDestination_heq
end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace E
export SourceFamilyActualCurrentMaterialRootedEffect (canonical_request_effect)
end E
namespace RC
export ActualCofinalRootResidualConsumer (source rootedMaterial selected base)
end RC
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance integratedFamilyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance integratedGroups : (target : Sorts) → AddCommGroup
 (ActualCofinalNativeTower.NativeValue (P.queryFactory factory) initial sourceCfg language (ordinal+1) target) :=
 fun target => L.groups W (RC.source (P.queryFactory factory) initial sourceCfg language (ordinal+1)).1 target

theorem completed_rooted_state_value :
 HEq (completed_born_actual
  (Native.selected (P.queryFactory factory) (RC.source (P.queryFactory factory) initial sourceCfg language ordinal))
  (Native.nativePacket (P.queryFactory factory) (RC.source (P.queryFactory factory) initial sourceCfg language ordinal)).2.2.1).1.1
 ((RC.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).state.1.eval
  (RC.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).environment) :=
 (heq_of_eq (completed_native_effect factory (RC.source (P.queryFactory factory) initial sourceCfg language ordinal))).trans
 ((E.canonical_request_effect factory initial sourceCfg language ordinal).symm.trans
  (heq_of_eq (RC.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).state.2.sound))

def consume_rooted_completed_answer {Result : Sort v}
 (consumer :
  (generated : type_of% (completedAction
   (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (RC.base (P.queryFactory factory) initial sourceCfg language ordinal))) →
  (answer : type_of% generated.target.targetAnswerAndNext.answer) →
  generated.target.Receipt generated.answer →
  type_of% (completed_rooted_state_value factory initial sourceCfg language ordinal) →
  type_of% (rooted_paid_trace_effect factory initial sourceCfg language ordinal) →
  type_of% (completed_compiles
   (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)) →
  type_of% (completed_target_current
   (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)) →
  type_of% (completed_successor_valid
   (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)) →
  type_of% generated.target.firstDestination_heq → Result) : Result :=
 consume_completed_answer
  (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
  (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)
  (fun generated answer receipt compiled next valid whole =>
   consumer generated answer receipt
    (completed_rooted_state_value factory initial sourceCfg language ordinal)
    (rooted_paid_trace_effect factory initial sourceCfg language ordinal) compiled next valid whole)
end

end SourceFamilyActualCurrentMaterialCompletedDisposition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
