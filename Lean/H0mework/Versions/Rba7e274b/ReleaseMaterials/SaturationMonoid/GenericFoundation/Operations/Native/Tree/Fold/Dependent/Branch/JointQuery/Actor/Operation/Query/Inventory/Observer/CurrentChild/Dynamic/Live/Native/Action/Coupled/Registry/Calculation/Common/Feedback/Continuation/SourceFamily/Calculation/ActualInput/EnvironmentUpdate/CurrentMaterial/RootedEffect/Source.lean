import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.Consumer
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyActualCurrentMaterialRootedEffect

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace P
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (reader reader_pair reader_paid_environment actual_action_isLeft)
end P
namespace AN
export ActualNativeRelationTransport (paid paid_state paid_raw paid_environment)
end AN
namespace B
export ActualNativeBornSourceEffect (born actual_born_registered_expression actual_born_registered_environment)
end B
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression expression_eval)
end N
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

theorem paid_updated_environment : (N.input (AN.paid frame)).environment = frame.activeEnvironment := by
 change frame.registered.input.environment +
  (frame.activeEnvironment - frame.registered.input.environment) = _
 abel

theorem born_request_input :
 (B.born frame cfg).registered.input.environment = (N.input (AN.paid frame)).environment ∧
 (B.born frame cfg).registered.input.expression = N.expression (AN.paid frame) :=
 ⟨(B.actual_born_registered_environment frame cfg).trans (paid_updated_environment frame).symm,
  B.actual_born_registered_expression frame cfg⟩


section ResidualEffect
variable {Nw : WorldRelationNetwork.{u}} {Voc : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure Nw Voc} {sourceCurrent : Voc.Current}
variable {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt sourceCurrent}
variable (material : RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value := Value) (Var := Var) (sort := s) occurrence)

private theorem residual_value_of_endpoint (value : Value s) (endpoint : material.state.1 = .const value) :
 (N.expression material).eval (N.input material).environment =
 material.raw.effect material.environment material.increment := by
 rw [N.expression_eval, endpoint]
 simp only [Expr.eval]
 have old := material.state.2.sound
 rw [endpoint] at old
 simp only [Expr.eval] at old
 change material.raw.eval (material.environment + material.increment) - value = _
 rw [Expr.eval_update, old]
 abel
end ResidualEffect

section NativeEffect
namespace L
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.L (Value groups)
end L
namespace SF
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.SF (Factory)
end SF
namespace AS
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.AS (AdmissionPacket)
end AS
namespace Native
export ActualCofinalSourceAction (selected receipt)
end Native
namespace P
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory)
end P
variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance groups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s) (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))

theorem native_residual_effect :
 (N.expression (AN.paid (Native.selected (P.queryFactory factory) packet))).eval
 (N.input (AN.paid (Native.selected (P.queryFactory factory) packet))).environment =
 (AN.paid (Native.selected (P.queryFactory factory) packet)).raw.effect
 (AN.paid (Native.selected (P.queryFactory factory) packet)).environment
 (AN.paid (Native.selected (P.queryFactory factory) packet)).increment := by
 exact residual_value_of_endpoint (AN.paid (Native.selected (P.queryFactory factory) packet))
  (Native.receipt (P.queryFactory factory) packet).2.1.1
  (Native.receipt (P.queryFactory factory) packet).2.1.2.down
end NativeEffect
end

section
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
 (debtCurrent debtStep payment paidContinuation generatePayment continuation_wellFounded debt_current_actual debt_step_receipt no_refill)
end Pay
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

theorem born_has_credit :
 0 < SourceOperationExecution.remaining (B.born frame cfg).event.state.1 := by
 have balance := SourceRegisteredClaimClock.remainder_generated (B.born frame cfg)
 change SourceOperationExecution.remaining (B.born frame cfg).event.state.1 =
  SourceOperationExecution.remaining (B.born frame cfg).registered.input.expression - 1 at balance
 have inputFee := congrArg SourceOperationExecution.remaining (born_request_input frame cfg).2
 have syntaxFee := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (AN.paid frame)
 omega

def born_actual_paid :
 Σ paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.law (B.born frame cfg).registered)
  (B.born frame cfg).event.state,
 PLift ((B.born frame cfg).action = .inr paid) := by
 have credit := born_has_credit frame cfg
 cases selected : (B.born frame cfg).action with
 | inr paid => exact ⟨paid, ⟨rfl⟩⟩
 | inl settled =>
  have zero := (RootGeneratedDebtActivationJointSource.law (B.born frame cfg).registered).settlement_budget_zero settled
  change SourceOperationExecution.remaining (B.born frame cfg).event.state.1 = 0 at zero
  exact False.elim (by omega)

def born_actual_payment : SourceNativeRootDebtPaymentStepAt (Pay.debtCurrent (B.born frame cfg)) :=
 Pay.payment (B.born frame cfg) (born_actual_paid frame cfg).1 (born_actual_paid frame cfg).2.down
end

section
open RootInquiryCompletion
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (current root visit)
end SO
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end AS
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

theorem born_payment_ledger :
 (Pay.debtCurrent (B.born frame cfg)).rooted.root.toAuthoritativeRoot.toLedgerRoot =
 (SO.root (B.born frame cfg) (AS.stockCfg cfg)).toAuthoritativeRoot.toLedgerRoot := rfl

theorem born_payment_step :
 (born_actual_payment frame cfg).step = Pay.debtStep (B.born frame cfg) := rfl

theorem born_payment_visit :
 (Pay.debtCurrent (B.born frame cfg)).rooted.visit = SO.visit (B.born frame cfg) (AS.stockCfg cfg) := by
 have visits : (count : Nat) →
  RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
    (B.born frame cfg).old.root.toAuthoritativeRoot (B.born frame cfg).registered (B.born frame cfg).packetAt count =
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit
    (B.born frame cfg).old (B.born frame cfg).registered (B.born frame cfg).packetAt count := by
  intro count
  induction count with
  | zero => rfl
  | succ count prior => exact congrArg (fun visit => visit.next (by rfl)) prior
 exact congrArg SourceNativeTemporalVisitAt.finite (visits ((B.born frame cfg).depth + 1))

def born_whole_successor :=
 (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
   ((SO.root (B.born frame cfg) (AS.stockCfg cfg)).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (SO.visit (B.born frame cfg) (AS.stockCfg cfg))).wholeLedgerWriteBack).get (by rfl)

theorem born_whole_receipt :
 HEq (born_whole_successor frame cfg).ledgerEvolution
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment.canonicalSuccessor
  (B.born frame cfg).old (B.born frame cfg).registered (B.born frame cfg).packetAt (B.born frame cfg).depth).ledgerEvolution := by
 change HEq
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.patch
   (B.born frame cfg).registered (B.born frame cfg).packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit (B.born frame cfg).old
    (B.born frame cfg).registered (B.born frame cfg).packetAt ((B.born frame cfg).depth + 1)).current).toLedgerWriteEvolution
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.patch
   (B.born frame cfg).registered (B.born frame cfg).packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit (B.born frame cfg).old.root.toAuthoritativeRoot
    (B.born frame cfg).registered (B.born frame cfg).packetAt ((B.born frame cfg).depth + 1)).current).toLedgerWriteEvolution
 rw [SourceRegisteredClaimClock.source_current]

private theorem destination_apply_heq {Nw : WorldRelationNetwork.{u}} {source leftTarget rightTarget : Nw.Support}
 {left : LedgerWriteEvolutionAt Nw ⟨source⟩ ⟨leftTarget⟩}
 {right : LedgerWriteEvolutionAt Nw ⟨source⟩ ⟨rightTarget⟩}
 (supports : leftTarget = rightTarget) (receipt : HEq left right)
 (entry : OpenResponsibilityAt Nw source) :
 HEq (left.destination entry).2 (right.destination entry).2 := by
 cases supports
 cases eq_of_heq receipt
 rfl

theorem born_payment_whole_destination :
 HEq (born_actual_payment frame cfg).step.evolution
 ((born_whole_successor frame cfg).ledgerEvolution.destination
  (Pay.debtCurrent (B.born frame cfg)).entry).2 := by
 rw [born_payment_step]
 have supports := congrArg
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.supportAt (B.born frame cfg).registered)
  (SourceRegisteredClaimClock.source_current (B.born frame cfg) ((B.born frame cfg).depth + 2))
 exact (destination_apply_heq supports (born_whole_receipt frame cfg)
  (Pay.debtCurrent (B.born frame cfg)).entry).symm

private theorem math_entry_heq
 {first second : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (B.born frame cfg).registered}
 (same : first = second) :
 HEq (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry (B.born frame cfg).registered first)
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry (B.born frame cfg).registered second) := by
 cases same
 rfl

theorem born_payment_entry :
 (Pay.debtCurrent (B.born frame cfg)).entry = (B.born frame cfg).currentState.entryAt PUnit.unit := by
 have current := SourceRegisteredClaimClock.source_current (B.born frame cfg) ((B.born frame cfg).depth + 1)
 exact eq_of_heq (math_entry_heq frame cfg current).symm
end

end SourceFamilyActualCurrentMaterialRootedEffect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
