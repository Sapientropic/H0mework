import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalRootedRequestEffectPaymentGate
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace E
export SourceFamilyActualCurrentMaterialRootedEffect
 (paid_updated_environment born_request_input native_residual_effect born_has_credit born_actual_paid
  born_actual_payment born_payment_step born_payment_entry born_payment_ledger born_payment_visit
  born_payment_whole_destination bornWholeWrite BornWholeWrite canonical_request_effect canonical_request_pair
  canonical_born_current RootedWholeEffect consume_rooted)
end E
namespace B
export ActualNativeBornSourceEffect (born)
end B
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment (debtCurrent debtStep continuation_wellFounded no_refill)
end Pay
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace SF
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.SF (Factory)
end SF
namespace L
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.L (Value groups)
end L
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
example : type_of% (E.paid_updated_environment frame) := E.paid_updated_environment frame
example : type_of% (E.born_request_input frame cfg) := E.born_request_input frame cfg
example : 0 < remaining (B.born frame cfg).event.state.1 := E.born_has_credit frame cfg
example : (B.born frame cfg).action = .inr (E.born_actual_paid frame cfg).1 := (E.born_actual_paid frame cfg).2.down
example : (E.born_actual_payment frame cfg).step = Pay.debtStep (B.born frame cfg) := E.born_payment_step frame cfg
example : type_of% (E.born_actual_payment frame cfg).step.sameDebtTarget_unique :=
 (E.born_actual_payment frame cfg).step.sameDebtTarget_unique
example : type_of% (E.born_payment_entry frame cfg) := E.born_payment_entry frame cfg
example : type_of% (E.born_payment_whole_destination frame cfg) := E.born_payment_whole_destination frame cfg
example : type_of% (E.born_payment_ledger frame cfg) := E.born_payment_ledger frame cfg
example : type_of% (E.born_payment_visit frame cfg) := E.born_payment_visit frame cfg
example : ((Pay.debtCurrent (B.born frame cfg)).next (E.born_actual_payment frame cfg).step).budget <
 (Pay.debtCurrent (B.born frame cfg)).budget := (E.born_actual_payment frame cfg).strictDebit
example : ((Pay.debtCurrent (B.born frame cfg)).next (E.born_actual_payment frame cfg).step).budget ≠
 (Pay.debtCurrent (B.born frame cfg)).budget := (E.born_actual_payment frame cfg).target_budget_ne_source
example : type_of% (Pay.no_refill (B.born frame cfg)) := Pay.no_refill (B.born frame cfg)
example : type_of% (Pay.continuation_wellFounded (B.born frame cfg)) := Pay.continuation_wellFounded (B.born frame cfg)
def born_write_control : E.BornWholeWrite frame cfg := E.bornWholeWrite frame cfg

section Rooted
variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance requestGroups : (target : Sorts) → AddCommGroup
 (ActualCofinalNativeTower.NativeValue (SourceFamilyActualCurrentMaterialEnvironmentUpdate.queryFactory factory)
  initial sourceCfg language (ordinal+1) target) :=
 fun target => L.groups W (ActualCofinalRootResidualConsumer.source
  (SourceFamilyActualCurrentMaterialEnvironmentUpdate.queryFactory factory) initial sourceCfg language (ordinal+1)).1 target
example : type_of% (E.canonical_request_effect factory initial sourceCfg language ordinal) :=
 E.canonical_request_effect factory initial sourceCfg language ordinal
example : type_of% (E.canonical_request_pair factory initial sourceCfg language ordinal) :=
 E.canonical_request_pair factory initial sourceCfg language ordinal
example : type_of% (E.canonical_born_current factory initial sourceCfg language ordinal) :=
 E.canonical_born_current factory initial sourceCfg language ordinal
def rooted_consumer_control : E.RootedWholeEffect factory initial sourceCfg language ordinal :=
 E.consume_rooted factory initial sourceCfg language ordinal (fun generated _ _ _ _ => generated)
end Rooted

section ZeroEffectCredit
variable {Nw : WorldRelationNetwork.{u}} {Voc : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure Nw Voc} {current : Voc.Current}
variable {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
variable (material : RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value := Value) (Var := Var) (sort := s) occurrence)
example (value : Value s) (raw : material.raw = .const value) :
 material.raw.effect material.environment material.increment = 0 ∧
 0 < remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression material) := by
 constructor
 · rw [raw]
   rfl
 · have fee := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget material
   omega
end ZeroEffectCredit
end CanonicalRootedRequestEffectPaymentGate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
