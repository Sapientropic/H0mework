import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Dispatch
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Word" => List Input

private theorem query_remaining (cut : C) (input : Input) :
    remainingNative (query cut input) = remainingNative cut := by cases input <;> rfl

private theorem query_control (cut : C) (input : Input) : (query cut input).control = cut.control := by
  cases input with
  | none => rfl
  | some _ => exact (cut.requery_keeps_control_and_complete_account _).1

theorem a_competing_input_cannot_add_native_work_to_the_pending_visit (cut : C) (input : Input)
    (pending : Quantities.Pending cut) :
    remainingNative (next cut input) + 1 = remainingNative cut ∧
      (next cut input).raw = cut.raw ∧ (next cut input).control = cut.control ∧
      inventory cut [input] = [] := by
  let asked := query cut input
  have work : Quantities.Pending asked := by cases input <;> exact pending
  have visited := an_original_native_prefix_preserves_material_and_pays_exactly_its_length asked 1 (by
    have positive := (pending_iff_positive_original_positions asked).mp work
    omega)
  have control : (next asked none).control = asked.control := by
    change asked.advance.control = asked.control
    have nativeWork : Macro.Public.Inquiry.HasWork asked.native.frame asked.native.actual.actual := work
    unfold Evolving.Epoch.Current.advance
    rw [dif_pos nativeWork]
    split
    · exact asked.native_birth_keeps_the_same_source_phase _
    · exact asked.the_unconsumed_source_phase_is_not_reset_by_ordinary_accounting
  exact ⟨visited.1.trans (query_remaining cut input),
    visited.2.1.trans (congrArg (fun state => state.raw) (query_physical cut input)),
    control.trans (query_control cut input), visited.2.2⟩

/-- The original native rank bounds every possible competing prefix up to
the first material choice, including actual financial registrations. -/
theorem all_native_interleavings_spend_the_same_backlog_without_material_effects (cut : C)
    (word : Word) (within : word.length ≤ remainingNative cut) :
    remainingNative (endAt cut word) + word.length = remainingNative cut ∧
      (endAt cut word).raw = cut.raw ∧ (endAt cut word).control = cut.control ∧
      inventory cut word = [] := by
  induction word generalizing cut with
  | nil => exact ⟨Nat.add_zero _, rfl, rfl, rfl⟩
  | cons input rest later =>
    have pending := (pending_iff_positive_original_positions cut).mpr (by
      simp only [List.length_cons] at within
      omega)
    obtain ⟨spent, raw, control, none⟩ :=
      a_competing_input_cannot_add_native_work_to_the_pending_visit cut input pending
    obtain ⟨remaining, rawTail, controlTail, itemsTail⟩ := later (next cut input) (by
      simp only [List.length_cons] at within
      omega)
    change remainingNative (endAt (next cut input) rest) + (rest.length + 1) = remainingNative cut ∧
      (endAt (next cut input) rest).raw = cut.raw ∧ (endAt (next cut input) rest).control = cut.control ∧
      inventory cut (input :: rest) = []
    refine ⟨by omega, rawTail.trans raw, controlTail.trans control, ?_⟩
    change inventory cut ([input] ++ rest) = []
    rw [inventory_append, none]
    exact itemsTail

theorem exactly_the_original_rank_precedes_the_first_material_visit (cut : C)
    (word : Word) (within : word.length ≤ remainingNative cut) :
    Quantities.Pending (endAt cut word) ↔ word.length < remainingNative cut := by
  have count := (all_native_interleavings_spend_the_same_backlog_without_material_effects cut word within).1
  rw [pending_iff_positive_original_positions]
  omega

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
