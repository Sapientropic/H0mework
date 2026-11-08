import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Prefix
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Head

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch
open Exchange (nativeAccount nativeAccount_heq_of_eq)
open Abolition.Innovation.Contribution.Pricing.Root.Runtime (native_head_uses_the_original_admission_or_consumption)
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
private abbrev items (cut : C) :=
  Public.Accounting.items cut.native.input cut.native.depth cut.native.count cut.native.prefixLimit
    cut.native.renewalLimit cut.native.oldPast cut.native.start

private def MaterialQueue (cut : C) : Prop :=
  ∀ item ∈ items cut, Responsibility.NonFinancialOperation
    (item.instruction cut.native.input cut.native.depth cut.native.count).request.operation

private theorem pending_material_head (cut : C) (pending : Pending cut) (material : MaterialQueue cut) :
    MaterialQueue cut.advance ∧ HEq (nativeAccount cut.advance) (nativeAccount cut) := by
  have works : Public.Inquiry.HasWork cut.native.frame cut.native.actual.actual := pending
  let head := Public.Accounting.item? cut.native.input cut.native.depth cut.native.count cut.native.prefixLimit
    cut.native.renewalLimit cut.native.oldPast cut.native.start cut.native.actual.actual
  have present : head.isSome = true := by
    rcases works with unpaid | someHead
    · rw [cut.native.bodyPaid] at unpaid
      contradiction
    · exact someHead
  cases found : head with
  | none =>
    rw [found] at present
    cases present
  | some item =>
    have listed : item ∈ items cut := List.mem_of_getElem? (by
      simpa only [head, Public.Accounting.item?, cut.native.bodyPaid, if_true] using found)
    have retained := an_original_nonfinancial_item_keeps_the_literal_native_account
      _ _ _ item (material item listed) (nativeAccount cut)
    refine ⟨?_, (native_head_uses_the_original_admission_or_consumption cut item found).trans
      (heq_of_eq retained)⟩
    unfold Current.advance
    rw [dif_pos works]
    split <;> exact material

private theorem native_material_drain (cut : C) (material : MaterialQueue cut) :
    HEq (nativeAccount (Execution.endAt cut (Execution.drain cut))) (nativeAccount cut) := by
  suffices bounded : ∀ (count : Nat) (current : C), count ≤ Execution.remainingNative current →
      MaterialQueue current →
      HEq (nativeAccount (Execution.endAt current (Execution.nativePayments count))) (nativeAccount current) by
    exact bounded _ _ le_rfl material
  intro count
  induction count with
  | zero => intro current _ _; rfl
  | succ count prior =>
    intro current within original
    have pending := (Execution.pending_iff_positive_original_positions current).mpr (by omega)
    have spent := Execution.a_native_payment_spends_one_original_position current pending
    have next := pending_material_head current pending original
    change HEq (nativeAccount (Execution.endAt current.advance (Execution.nativePayments count))) (nativeAccount current)
    exact (prior current.advance (by
      change Execution.remainingNative current.advance + 1 = Execution.remainingNative current at spent
      omega) next.1).trans next.2

private theorem the_body_queue_reads_the_public_inventory (cut : C)
    (ready : ¬ Public.Inquiry.HasWork cut.native.frame cut.native.actual.actual) :
    ((items (Transition.next cut ready)).map
      (Epoch.Finance.ActualItem.instruction cut.native.input cut.native.depth cut.native.count)) =
      cut.physicalResult.execution.items :=
  Public.Accounting.actual_items_are_the_same_public_execution cut.native.input cut.native.depth cut.native.count
    cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast (Transition.next cut ready).native.start

/-- Material-only instructions consume their original queue positions and
keep the full native financial state, including its original closed slots. -/
theorem a_material_body_and_its_native_drain_keep_the_original_account (cut : C)
    (ready : ¬ Public.Inquiry.HasWork cut.native.frame cut.native.actual.actual)
    (material : ∀ item ∈ cut.physicalResult.execution.items,
      Responsibility.NonFinancialOperation item.request.operation) :
    HEq (nativeAccount (Execution.endAt cut.advance (Execution.drain cut.advance))) (nativeAccount cut) := by
  let body := Transition.next cut ready
  have same : cut.advance = body := Current.advance_eq_epoch cut ready
  have sameDrain := congrArg (fun current : C => Execution.endAt current (Execution.drain current)) same
  have bodyMaterial : MaterialQueue body := by
    intro item listed
    have original : item.instruction _ _ _ ∈
        (items body).map (Epoch.Finance.ActualItem.instruction cut.native.input cut.native.depth cut.native.count) :=
      List.mem_map.mpr ⟨item, listed, rfl⟩
    exact material _ (the_body_queue_reads_the_public_inventory cut ready ▸ original)
  have carries : nativeAccount body = nativeAccount cut :=
    (Transition.body_is_not_replayed_or_financially_reset cut ready).1
  exact (nativeAccount_heq_of_eq sameDrain).trans
    ((native_material_drain body bodyMaterial).trans (heq_of_eq carries))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
