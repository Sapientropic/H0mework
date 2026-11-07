import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def remainingNative (source : C) : Nat :=
  let native := source.native
  Public.Accounting.mass native.input native.depth native.count native.prefixLimit native.renewalLimit
    native.oldPast native.start native.actual.actual

theorem pending_iff_positive_original_positions (source : C) :
    Pending source ↔ 0 < remainingNative source :=
  Public.Accounting.Drain.actual_work_iff_positive_source_mass source.native.frame source.native.actual.actual

theorem a_native_payment_spends_one_original_position (source : C) (pending : Pending source) :
    remainingNative (next source none) + 1 = remainingNative source := by
  change Public.Inquiry.HasWork source.native.frame source.native.actual.actual at pending
  change remainingNative source.advance + 1 = _
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos pending]
  split
  · exact Public.Accounting.the_original_admission_spends_exactly_its_actual_head
      source.native.input source.native.depth source.native.count source.native.prefixLimit
      source.native.renewalLimit source.native.oldPast source.native.start _
  · exact Public.Accounting.Drain.every_actual_internal_restriction_spends_one_position
      source.native.frame source.native.actual.actual pending

private theorem internal_payment_is_not_a_second_material_step (source : C) (pending : Pending source) :
    (next source none).raw = source.raw ∧ Optimality.Programme.Epoch.materialItems source = [] := by
  change Public.Inquiry.HasWork source.native.frame source.native.actual.actual at pending
  have unchanged := effective_step source none
  change Optimality.Programme.run source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Optimality.Programme.Epoch.effective source) = _ at unchanged
  have internal : Optimality.Programme.Epoch.effective source = [] := by
    unfold Optimality.Programme.Epoch.effective
    rw [if_pos pending]
  have noItems := effective_inventory source none
  change Optimality.Programme.items source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Optimality.Programme.Epoch.effective source) = Optimality.Programme.Epoch.materialItems source at noItems
  rw [internal] at unchanged noItems
  exact ⟨(congrArg (fun state => state.raw) unchanged).symm, noItems.symm⟩

def nativePayments (count : Nat) : Script := List.replicate count none

/-- Pending native rows have an exact last payment position on the original
root. The drain does not consume the next material or proposal event. -/
theorem an_original_native_prefix_preserves_material_and_pays_exactly_its_length
    (source : C) (count : Nat) (within : count ≤ remainingNative source) :
    remainingNative (endAt source (nativePayments count)) + count = remainingNative source ∧
      (endAt source (nativePayments count)).raw = source.raw ∧ inventory source (nativePayments count) = [] := by
  induction count generalizing source with
  | zero => exact ⟨Nat.add_zero _, rfl, rfl⟩
  | succ count prior =>
    have pending := (pending_iff_positive_original_positions source).mpr (by omega)
    have spent := a_native_payment_spends_one_original_position source pending
    obtain ⟨left, raw, items⟩ := prior (next source none) (by omega)
    obtain ⟨same, empty⟩ := internal_payment_is_not_a_second_material_step source pending
    change remainingNative (endAt (next source none) (nativePayments count)) + (count + 1) =
        remainingNative source ∧
      (endAt (next source none) (nativePayments count)).raw = source.raw ∧
      Optimality.Programme.Epoch.materialItems source ++ inventory (next source none) (nativePayments count) = []
    exact ⟨by omega, raw.trans same, by rw [empty, items]; rfl⟩

def drain (source : C) : Script := nativePayments (remainingNative source)

theorem the_first_exhausted_native_cut_is_the_original_paid_drain (source : C) :
    ¬ Pending (endAt source (drain source)) ∧
      (endAt source (drain source)).raw = source.raw ∧ inventory source (drain source) = [] ∧
      (∀ count < remainingNative source, Pending (endAt source (nativePayments count))) ∧
      Recorded source (drain source) := by
  obtain ⟨paid, material, noItems⟩ :=
    an_original_native_prefix_preserves_material_and_pays_exactly_its_length source _ le_rfl
  refine ⟨?_, material, noItems, ?_, record source _⟩
  · intro pending
    have left := (pending_iff_positive_original_positions _).mp pending
    unfold drain at left
    omega
  · intro count earlier
    have left := (an_original_native_prefix_preserves_material_and_pays_exactly_its_length
      source count earlier.le).1
    exact (pending_iff_positive_original_positions _).mpr (by omega)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
