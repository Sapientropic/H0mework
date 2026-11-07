import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

structure SafeAt (source : C) where
  fee : SelectedAt source
  original : selected? source = some fee
  ready : ¬ Pending source
  paid : PaidAt source fee
  protects : Fits source fee

inductive Issue (source : C)
  | noFee (absent : selected? source = none)
  | pending (original : NativeObstruction source)
  | stock (fee : SelectedAt source) (original : selected? source = some fee)
      (unpaid : source.raw.stock fee.fee.scope.payer fee.fee.scope.good < fee.fee.scope.amount)
  | displaced (fee : SelectedAt source) (original : selected? source = some fee)
      (paid : PaidAt source fee)
      (loss : (Execution.endAt source (script source)).raw.stock fee.fee.scope.payer fee.fee.scope.good <
        necessities source fee.fee.scope.payer fee.fee.scope.good)

theorem Issue.refutes {source : C} (issue : Issue source) : ¬ Nonempty (SafeAt source) := by
  rintro ⟨safe⟩
  cases issue with
  | noFee absent =>
    have impossible := safe.original.symm.trans absent
    cases impossible
  | pending original => exact safe.ready original.pending
  | stock fee original unpaid =>
    have same : safe.fee = fee := Option.some.inj (safe.original.symm.trans original)
    have floor : 0 ≤ necessities source fee.fee.scope.payer fee.fee.scope.good := le_max_left _ _
    have protect := safe.protects
    rw [same] at protect
    unfold Fits ceiling at protect
    linarith
  | displaced fee original paid loss =>
    have same : safe.fee = fee := Option.some.inj (safe.original.symm.trans original)
    exact (not_le_of_gt loss) ((the_fee_ceiling_is_exact_at_the_actual_paid_cut source fee paid).mp
      (same ▸ safe.protects))

inductive Decision (source : C)
  | safe (actual : SafeAt source)
  | blocked (issue : Issue source)

private instance (source : C) (fee : SelectedAt source) : Decidable (Fits source fee) := by
  unfold Fits
  infer_instance

/-- The original fee may physically execute and still have an unacceptable
living deficit. The fee is recorded in both cases. -/
def decideFee (source : C) : Decision source :=
  match pending : inspectNative source with
  | some original => .blocked (.pending original)
  | none =>
    match original : selected? source with
    | none => .blocked (.noFee original)
    | some fee =>
      let ready := native_is_finished_without_a_pending_item source pending
      if capacity : fee.fee.scope.amount ≤ source.raw.stock fee.fee.scope.payer fee.fee.scope.good then
        let paid := the_chosen_fee_debits_its_original_payer_and_activates_the_actual_review source fee ready capacity
        if protects : Fits source fee then .safe ⟨fee, original, ready, paid, protects⟩
        else .blocked (.displaced fee original paid (lt_of_not_ge fun preserved =>
          protects ((the_fee_ceiling_is_exact_at_the_actual_paid_cut source fee paid).mpr preserved)))
      else .blocked (.stock fee original (lt_of_not_ge capacity))

def inspect (source : C) : Option (Issue source) :=
  match decideFee source with
  | .safe _ => none
  | .blocked issue => some issue

theorem inspection_recognizes_exactly_the_original_safe_fee (source : C) :
    inspect source = none ↔ Nonempty (SafeAt source) := by
  unfold inspect
  cases decideFee source with
  | safe actual => exact ⟨fun _ => ⟨actual⟩, fun _ => rfl⟩
  | blocked issue =>
    simp only [reduceCtorEq, false_iff]
    exact issue.refutes

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee
