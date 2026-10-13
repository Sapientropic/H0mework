import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Consumer
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
namespace E
export SourceFamilyActualCurrentMaterialRootedEffect (born_request_input born_has_credit)
end E
namespace B
export ActualNativeBornSourceEffect (born)
end B
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
 (completedEvent completedRuntime completed completed_value completed_budget event)
end C
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (root visit current)
end SO
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end AS
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

def completedBorn : M.Frame (Value := Value) (Var := Var) (sort := s) :=
 { B.born frame cfg with depth := remaining (B.born frame cfg).registered.input.expression - 1 }

theorem completed_born_clock :
 (completedBorn frame cfg).depth + 1 = remaining (completedBorn frame cfg).registered.input.expression := by
 have credit := E.born_has_credit frame cfg
 have generated := SourceRegisteredClaimClock.remainder_generated (B.born frame cfg)
 change remaining (B.born frame cfg).event.state.1 = remaining (B.born frame cfg).registered.input.expression - 1 at generated
 change remaining (B.born frame cfg).registered.input.expression - 1 + 1 = remaining (B.born frame cfg).registered.input.expression
 omega

theorem completed_born_state :
 (completedBorn frame cfg).event.state =
 (C.completedEvent (B.born frame cfg).old.root.toAuthoritativeRoot
  (B.born frame cfg).registered (B.born frame cfg).packetAt).state := by
 have actual := SourceRegisteredClaimClock.current_event (completedBorn frame cfg)
 have count := completed_born_clock frame cfg
 exact actual.trans (congrArg (fun count =>
  (C.event (B.born frame cfg).old.root.toAuthoritativeRoot
   (B.born frame cfg).registered (B.born frame cfg).packetAt count).state) count)

theorem completed_born_suffix :
 (completedBorn frame cfg).event.state =
 (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
  (B.born frame cfg).old.root.toAuthoritativeRoot (B.born frame cfg).registered (B.born frame cfg).packetAt
  (SourceRegisteredClaimClock.suffixHistory (B.born frame cfg)).target).2.state :=
 (completed_born_state frame cfg).trans
  (SourceRegisteredClaimClock.suffix_no_restart (B.born frame cfg) (E.born_has_credit frame cfg)).symm

theorem completed_born_root :
 SO.root (completedBorn frame cfg) (AS.stockCfg cfg) = SO.root (B.born frame cfg) (AS.stockCfg cfg) := rfl

def completed_born_settlement : SourceOperationExecutionDebt.Settlement (completedBorn frame cfg).event.state :=
 (completed_born_state frame cfg).symm ▸
 C.completed (B.born frame cfg).old.root.toAuthoritativeRoot (B.born frame cfg).registered (B.born frame cfg).packetAt

theorem completed_born_zero : remaining (completedBorn frame cfg).event.state.1 = 0 :=
 (congrArg (fun state => remaining state.1) (completed_born_state frame cfg)).trans
  (C.completed_budget (B.born frame cfg).old.root.toAuthoritativeRoot (B.born frame cfg).registered (B.born frame cfg).packetAt)

def completed_born_actual :
 Σ settled : SourceOperationExecutionDebt.Settlement (completedBorn frame cfg).event.state,
 PLift ((completedBorn frame cfg).action = .inl settled) := by
 cases actual : (completedBorn frame cfg).action with
 | inl settled => exact ⟨settled, ⟨rfl⟩⟩
 | inr paid =>
  have strict := (RootGeneratedDebtActivationJointSource.law (completedBorn frame cfg).registered).step_budget_lt paid.2
  change remaining paid.1.1 < remaining (completedBorn frame cfg).event.state.1 at strict
  rw [completed_born_zero] at strict
  exact False.elim (Nat.not_lt_zero _ strict)
end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace R
export RootGeneratedDebtActivationJointSource.Successor.Restructuring (runtimeCurrent finiteVisit)
end R
namespace E
export SourceFamilyActualCurrentMaterialRootedEffect (native_residual_effect canonical_request_pair)
end E
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion (runtime runtime_depth)
end C
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

theorem completed_born_full_current :
 (completedBorn frame cfg).currentState.visit.current =
 R.runtimeCurrent (B.born frame cfg).old.root.toAuthoritativeRoot
  (B.born frame cfg).registered (B.born frame cfg).packetAt
  (SourceRegisteredClaimClock.suffixHistory (B.born frame cfg)).target := by
 rw [SourceRegisteredClaimClock.suffix_ends_at_original (B.born frame cfg) (E.born_has_credit frame cfg)]
 change (RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit
  (B.born frame cfg).old (B.born frame cfg).registered (B.born frame cfg).packetAt
  ((completedBorn frame cfg).depth + 1)).current = _
 rw [completed_born_clock]
 unfold C.completedRuntime R.runtimeCurrent
 rw [C.runtime_depth]
 exact SourceRegisteredClaimClock.source_current (B.born frame cfg) _

theorem completed_born_value :
 (completed_born_actual frame cfg).1.1 =
 (B.born frame cfg).registered.input.expression.eval (B.born frame cfg).registered.input.environment :=
 RootGeneratedDebtActivationJointSource.local_completed_value (completedBorn frame cfg).event
  (completed_born_actual frame cfg).1

theorem completed_born_input_value :
 (completed_born_actual frame cfg).1.1 =
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (ActualNativeRelationTransport.paid frame)).eval
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (ActualNativeRelationTransport.paid frame)).environment := by
 have source := E.born_request_input frame cfg
 exact (completed_born_value frame cfg).trans (by rw [source.1, source.2])

section Native
namespace L
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.L (Value groups)
end L
namespace SF
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.SF (Factory)
end SF
namespace AS
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.AS (AdmissionPacket)
end AS
namespace P
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory)
end P
namespace Native
export ActualCofinalSourceAction (selected nativePacket)
end Native
namespace AN
export ActualNativeRelationTransport (paid)
end AN
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression)
end N
variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance nativeGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s) (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))

theorem completed_native_effect :
 (completed_born_actual (Native.selected (P.queryFactory factory) packet)
  (Native.nativePacket (P.queryFactory factory) packet).2.2.1).1.1 =
 (AN.paid (Native.selected (P.queryFactory factory) packet)).raw.effect
 (AN.paid (Native.selected (P.queryFactory factory) packet)).environment
 (AN.paid (Native.selected (P.queryFactory factory) packet)).increment := by
 exact (completed_born_input_value (Native.selected (P.queryFactory factory) packet)
  (Native.nativePacket (P.queryFactory factory) packet).2.2.1).trans
  (E.native_residual_effect factory packet)
end Native
end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
section RootedMaterial
variable {Sorts : Type u} {s : Sorts}
variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance rootedFamilyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance rootedGroups : (target : Sorts) → AddCommGroup
 (ActualCofinalNativeTower.NativeValue (P.queryFactory factory) initial sourceCfg language (ordinal+1) target) :=
 fun target => L.groups W (ActualCofinalRootResidualConsumer.source
  (P.queryFactory factory) initial sourceCfg language (ordinal+1)).1 target

theorem rooted_paid_trace_effect :
 HEq ((ActualCofinalRootResidualConsumer.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).state.1.eval
  (ActualCofinalRootResidualConsumer.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).environment)
 (SourceOperationInquiry.Context.Installation.materialAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch
   (ActualCofinalRootResidualConsumer.selected (P.queryFactory factory) initial sourceCfg language ordinal))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
   (ActualCofinalRootResidualConsumer.selected (P.queryFactory factory) initial sourceCfg language ordinal))).pair.2 :=
 (heq_of_eq (ActualCofinalRootResidualConsumer.rootedMaterial
  (P.queryFactory factory) initial sourceCfg language ordinal).state.2.sound.symm).trans
 (E.canonical_request_pair factory initial sourceCfg language ordinal)
end RootedMaterial
end

end SourceFamilyActualCurrentMaterialCompletedDisposition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
