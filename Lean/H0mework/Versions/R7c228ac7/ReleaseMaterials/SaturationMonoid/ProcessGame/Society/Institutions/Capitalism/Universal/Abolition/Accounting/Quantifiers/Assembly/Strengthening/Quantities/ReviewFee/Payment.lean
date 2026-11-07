import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.MicroBudget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolving.Epoch
open Abolition.Review (FeeScope valid_iff_permission_and_stock)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev law (source : C) := Physical.Public.interpreter source.native.input

def script (source : C) : Script := none :: Execution.drain (Execution.next source none)

def Fits (source : C) (fee : SelectedAt source) : Prop :=
  fee.fee.scope.amount ≤ ceiling source fee.fee.scope.payer fee.fee.scope.good

theorem the_independent_fee_is_physically_valid_iff_its_original_cell_can_pay
    (source : C) (fee : SelectedAt source) :
    (law source).Valid source.raw fee.fee.request ↔
      fee.fee.scope.amount ≤ source.raw.stock fee.fee.scope.payer fee.fee.scope.good := by
  rw [valid_iff_permission_and_stock (law source) fee.fee.request fee.fee.scope source.raw]
  exact ⟨And.right, fun paid => ⟨⟨rfl, fun _ _ => Or.inl rfl⟩, paid⟩⟩

structure PaidAt (source : C) (fee : SelectedAt source) : Prop where
  actualItem : Execution.inventory source (script source) = [⟨0, source.raw, fee.fee.request⟩]
  accepted : (Execution.next source none).control.review = some { fee.cursor with feePaid := true, halted := false }
  balance :
    (Execution.endAt source (script source)).raw.stock fee.fee.scope.payer fee.fee.scope.good + fee.fee.scope.amount =
      source.raw.stock fee.fee.scope.payer fee.fee.scope.good
  ready : ¬ Pending (Execution.endAt source (script source))
  whole : Recorded source (script source)

private theorem actualControl (source : C) (fee : SelectedAt source) (ready : ¬ Pending source) :
    (Execution.next source none).control.review = some { fee.cursor with
      feePaid := source.physicalResult.isAccepted, halted := !source.physicalResult.isAccepted } := by
  have original : ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual := ready
  change source.advance.control.review = _
  rw [source.advance_eq_epoch original, Transition.next_reads_the_written_control]
  exact fee.writeBack

theorem the_chosen_fee_debits_its_original_payer_and_activates_the_actual_review
    (source : C) (fee : SelectedAt source) (ready : ¬ Pending source)
    (capacity : fee.fee.scope.amount ≤ source.raw.stock fee.fee.scope.payer fee.fee.scope.good) :
    PaidAt source fee := by
  have valid := (the_independent_fee_is_physically_valid_iff_its_original_cell_can_pay source fee).mpr capacity
  obtain ⟨raw, accepted, items⟩ := Execution.the_selected_primitive_is_paid_by_the_original_root source fee.fee.request
    ready fee.selected fee.signed valid
  let next := Execution.next source none
  obtain ⟨finished, same, empty, _, _⟩ := Execution.the_first_exhausted_native_cut_is_the_original_paid_drain next
  let payment : Abolition.Review.PaymentAt (law source) fee.fee.request source.raw := ⟨valid⟩
  refine ⟨?_, ?_, ?_, finished, record source _⟩
  · change Execution.inventory source ([none] ++ Execution.drain next) = _
    rw [Execution.inventory_append, show Execution.endAt source [none] = next from rfl, items, empty]
    rfl
  · rw [actualControl source fee ready, accepted]
    rfl
  · change (Execution.endAt next (Execution.drain next)).raw.stock fee.fee.scope.payer fee.fee.scope.good +
      fee.fee.scope.amount = _
    rw [same, raw]
    exact payment.micro_stock_balance fee.fee.scope

theorem the_fee_ceiling_is_exact_at_the_actual_paid_cut
    (source : C) (fee : SelectedAt source) (paid : PaidAt source fee) :
    Fits source fee ↔ necessities source fee.fee.scope.payer fee.fee.scope.good ≤
      (Execution.endAt source (script source)).raw.stock fee.fee.scope.payer fee.fee.scope.good := by
  unfold Fits ceiling
  constructor <;> intro fits <;> linarith [paid.balance]

theorem a_fee_shortfall_preserves_the_original_debts_and_reopens_recourse
    (source : C) (fee : SelectedAt source) (ready : ¬ Pending source)
    (short : source.raw.stock fee.fee.scope.payer fee.fee.scope.good < fee.fee.scope.amount) :
    (Execution.next source none).raw = source.raw ∧
      (Execution.next source none).control.review = some { fee.cursor with feePaid := false, halted := true } ∧
      Recorded source (script source) := by
  have denied := fun paid => (not_le_of_gt short)
    ((the_independent_fee_is_physically_valid_iff_its_original_cell_can_pay source fee).mp paid)
  obtain ⟨same, refused⟩ := Execution.the_selected_refusal_keeps_the_exact_original_material_current source fee.fee.request
    ready fee.selected fee.signed denied
  refine ⟨same, ?_, record source _⟩
  rw [actualControl source fee ready, refused]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee
