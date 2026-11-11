import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleySourceAdmissions
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativePortNoetherConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace W
export OriginalKPaNativeCayleySourceWriteback (admissions request generatedAction)
end W
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native sourceFrame sourceBase beforeStock beforeEnvironment)
end WN
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (betaState reader sourceOccurrence actualMaterial afterEnvironment firstStep first_action generatedAction request)
end SN
namespace J
export RootGeneratedDebtActivationJointSource
  (initialEvent mathAction mathTarget mathTarget_budget law)
end J
namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (sourceAction_eq)
end I
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end C
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
  (debtCurrent debtStep payment paidContinuation continuation_wellFounded debt_step_receipt)
end Pay
namespace Receipt
export SourceGeneratedInquiryReceiptAction (packetAt)
end Receipt
namespace Adapter
open SourceOperationInquiry.Context.Faces.Execution.Activation
variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}
variable (frame : M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable (base : Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s))
variable (before : SourceInventoryExecutionFeed.Inventory (V := V) (X := X) (s := s))
variable (oldEnvironment : Env V X)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
  (ActualNativeRelationTransport.AS.stockScalar frame base)))
local notation "req" => SN.request frame base before oldEnvironment admissions
local notation "oldState" => SN.betaState frame base before oldEnvironment admissions
local notation "packets" => Receipt.packetAt frame (ActualNativeRelationTransport.AS.stockCfg base)

/-- A restriction of the existing request at its first generated successor address. -/
private def debtFrame : C.Frame (Value := PairValue V) (Var := X) (sort := s) where
  N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
  V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
  old := oldState
  registered := req
  packetAt := packets
  environment := fun {_current} occurrence =>
    (SN.reader frame base before oldEnvironment admissions occurrence).environment
  depth := 0

private abbrev firstPaid := SN.firstStep frame base before oldEnvironment admissions

private theorem first_selected : J.mathAction (J.initialEvent req) =
    .inr (firstPaid frame base before oldEnvironment admissions) :=
  (I.sourceAction_eq oldState req packets).symm.trans
    (SN.first_action frame base before oldEnvironment admissions)

private theorem first_state : (debtFrame frame base before oldEnvironment admissions).event.state =
    (firstPaid frame base before oldEnvironment admissions).1 := by
  change J.mathTarget (J.initialEvent req) = _
  unfold J.mathTarget
  rw [first_selected]

private theorem first_ledger :
    (debtFrame frame base before oldEnvironment admissions).currentState.root.toAuthoritativeRoot.toLedgerRoot =
      (SN.generatedAction frame base before oldEnvironment admissions).target.targetRoot.toAuthoritativeRoot.toLedgerRoot := rfl

private theorem first_visit : HEq
    (debtFrame frame base before oldEnvironment admissions).currentState.visit
    (SN.generatedAction frame base before oldEnvironment admissions).target.targetVisit := HEq.rfl

private theorem first_occurrence : HEq
    ((debtFrame frame base before oldEnvironment admissions).currentState.root.emitted
      (debtFrame frame base before oldEnvironment admissions).currentState.visit.current)
    ((SN.generatedAction frame base before oldEnvironment admissions).target.targetRoot.emitted
      (SN.generatedAction frame base before oldEnvironment admissions).target.targetVisit.current) := HEq.rfl

private theorem first_paid_history : HEq
    (debtFrame frame base before oldEnvironment admissions).event.state.2
    (firstPaid frame base before oldEnvironment admissions).1.2 := by
  exact (Sigma.mk.inj_iff.mp (show
    Sigma.mk (debtFrame frame base before oldEnvironment admissions).event.state.1
      (debtFrame frame base before oldEnvironment admissions).event.state.2 =
    Sigma.mk (firstPaid frame base before oldEnvironment admissions).1.1
      (firstPaid frame base before oldEnvironment admissions).1.2 from
        first_state frame base before oldEnvironment admissions)).2

private theorem remaining_positive :
    0 < remaining (debtFrame frame base before oldEnvironment admissions).event.state.1 := by
  have initialBudget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget
    (SN.actualMaterial frame base before oldEnvironment admissions)
  have debit := J.mathTarget_budget (J.initialEvent req)
  change remaining (debtFrame frame base before oldEnvironment admissions).event.state.1 =
    remaining (req).input.expression - 1 at debit
  change remaining (req).input.expression = _ at initialBudget
  omega

private def actualPaid : Σ paid : DebtActivationWorld.GeneratedStepAt
    (J.law req) (debtFrame frame base before oldEnvironment admissions).event.state,
    PLift ((debtFrame frame base before oldEnvironment admissions).action = .inr paid) := by
  cases selected : (debtFrame frame base before oldEnvironment admissions).action with
  | inr paid => exact ⟨paid, ⟨rfl⟩⟩
  | inl settled =>
      have zero := (J.law req).settlement_budget_zero settled
      change remaining (debtFrame frame base before oldEnvironment admissions).event.state.1 = 0 at zero
      exact False.elim ((Nat.ne_of_gt (remaining_positive frame base before oldEnvironment admissions)) zero)

private def payment : SourceNativeRootDebtPaymentStepAt
    (Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)) :=
  Pay.payment (debtFrame frame base before oldEnvironment admissions)
    (actualPaid frame base before oldEnvironment admissions).1
    (actualPaid frame base before oldEnvironment admissions).2.down

private theorem payment_claim :
    (Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)).entry.claim =
      .inr (req).input.expression := rfl

private theorem strict_debit :
    ((Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)).next
      (payment frame base before oldEnvironment admissions).step).budget <
        (Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)).budget :=
  (payment frame base before oldEnvironment admissions).strictDebit

private theorem payment_whole_receipt : HEq
    (payment frame base before oldEnvironment admissions).step.evolution
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment.debtStep
      oldState req packets 0).evolution :=
  Pay.debt_step_receipt (debtFrame frame base before oldEnvironment admissions)

private def paidMacro : SourceNativePaidRootDebtMacroContinuationAt
    (Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)) :=
  Pay.paidContinuation (debtFrame frame base before oldEnvironment admissions)
    (actualPaid frame base before oldEnvironment admissions).1
    (actualPaid frame base before oldEnvironment admissions).2.down

private theorem paid_macro_strict : (paidMacro frame base before oldEnvironment admissions).target.budget <
    (Pay.debtCurrent (debtFrame frame base before oldEnvironment admissions)).budget :=
  (paidMacro frame base before oldEnvironment admissions).strictDebit

private theorem paid_history_wellFounded : type_of%
    (Pay.continuation_wellFounded (debtFrame frame base before oldEnvironment admissions)) :=
  Pay.continuation_wellFounded (debtFrame frame base before oldEnvironment admissions)
end Adapter

local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "stock" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "items" => W.admissions observation nontrivial half depth ordinal
private abbrev SourceValue := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1
private abbrev SourceVar := (AS.bornAfterNative native).2.2.1.LowVar
local notation "Vn" => SourceValue observation nontrivial half depth ordinal
local notation "Xn" => SourceVar observation nontrivial half depth ordinal

def debtFrame := Adapter.debtFrame (V := Vn) (X := Xn) frame base stock oldEnv items
def firstPaid := Adapter.firstPaid (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_selected : type_of% (Adapter.first_selected (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_selected (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_state : type_of% (Adapter.first_state (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_state (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_ledger : type_of% (Adapter.first_ledger (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_ledger (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_visit : type_of% (Adapter.first_visit (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_visit (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_occurrence : type_of% (Adapter.first_occurrence (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_occurrence (V := Vn) (X := Xn) frame base stock oldEnv items

theorem first_paid_history : type_of% (Adapter.first_paid_history (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.first_paid_history (V := Vn) (X := Xn) frame base stock oldEnv items

def payment := Adapter.payment (V := Vn) (X := Xn) frame base stock oldEnv items

theorem payment_claim : type_of% (Adapter.payment_claim (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.payment_claim (V := Vn) (X := Xn) frame base stock oldEnv items

theorem strict_debit : type_of% (Adapter.strict_debit (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.strict_debit (V := Vn) (X := Xn) frame base stock oldEnv items

theorem payment_whole_receipt : type_of% (Adapter.payment_whole_receipt (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.payment_whole_receipt (V := Vn) (X := Xn) frame base stock oldEnv items

def paidMacro := Adapter.paidMacro (V := Vn) (X := Xn) frame base stock oldEnv items

theorem paid_macro_strict : type_of% (Adapter.paid_macro_strict (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.paid_macro_strict (V := Vn) (X := Xn) frame base stock oldEnv items

theorem paid_history_wellFounded : type_of% (Adapter.paid_history_wellFounded (V := Vn) (X := Xn) frame base stock oldEnv items) :=
  Adapter.paid_history_wellFounded (V := Vn) (X := Xn) frame base stock oldEnv items

end OriginalKPaNativePortNoetherConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
