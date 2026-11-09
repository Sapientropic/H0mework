import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Window
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Trajectory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Backlog

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window)
open PublicFunction.Mandate
open Quantities.Execution (drain endAt inventory nativePayments remainingNative)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable (rival : Scheduler Party Good Port (State Party Technology) Instrument)
  (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- An accepted commitment occupies the original dispatch visits of its
literal word. All later lanes and offers belong to the existing scheduler. -/
def reserve : Scheduler Party Good Port M Instrument where
  lane tick history := if tick < word.length then .personal else rival.lane tick history
  personal tick history :=
    if inside : tick < word.length then word[tick] else rival.personal tick history
  rival := rival.rival
  offer := rival.offer

variable {word}

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem reserve_reads_the_literal_input (tick : Nat) (past : Word) (inside : tick < word.length) :
    (reserve rival word).proposal tick past = word[tick] := by
  simp only [Scheduler.proposal, reserve, if_pos inside, dif_pos inside]

theorem reserve_reads_the_original_owner_lanes {seed : C} (answers : OwnerAnswers seed) (person : Party)
    (tick : Nat) (past : Word) (inside : tick < word.length) :
    (reserve rival word).replies answers person tick past = answers := by
  simp only [Scheduler.replies, reserve, if_pos inside]

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- Check the original paid window for the exact next history. The
remainder of the already certified commitment supplies its continuation. -/
def paidProbe : Probe (MandateExit.PaidAt seed anchor) := fun history =>
  match Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length) with
  | .inl _ => none
  | .inr paid => some paid

theorem paid_probe_accepts_the_original_paid_prefix (history : Word) (paid : MandateExit.PaidAt seed anchor history) :
    ∃ verified, paidProbe seed anchor history = some verified := by
  unfold paidProbe
  cases Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length) with
  | inl failure => exact (failure.refutes _ paid).elim
  | inr verified => exact ⟨verified, rfl⟩

variable (cut : Root.Cut Party Good Port (State Party Technology) Instrument)
  (body : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- Resolve the original native backlog before selecting the first
material input of the offered body. -/
def afterBacklog : Word := drain cut ++ body

theorem original_backlog_gives_the_exact_dispatch_count :
    (afterBacklog cut body).length = remainingNative cut + body.length := by
  simp only [afterBacklog, drain, nativePayments, List.length_append, List.length_replicate]

theorem every_earlier_native_visit_is_still_pending (count : Nat) (earlier : count < remainingNative cut) :
    Quantities.Pending (endAt cut ((afterBacklog cut body).take count)) := by
  have enough : count ≤ (drain cut).length := by
    simpa only [drain, nativePayments, List.length_replicate] using earlier.le
  rw [afterBacklog, List.take_append_of_le_length enough]
  have waiting : (drain cut).take count = nativePayments count := by
    simp only [drain, nativePayments, List.take_replicate, Nat.min_eq_left earlier.le]
  rw [waiting]
  exact (Quantities.Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut).2.2.2.1 count earlier

theorem the_first_ready_position_has_the_original_clock_and_no_material_before_it :
    let waiting := (afterBacklog cut body).take (remainingNative cut)
    ¬ Quantities.Pending (endAt cut waiting) ∧
      (endAt cut waiting).raw.clock = cut.raw.clock ∧ inventory cut waiting = [] := by
  have length : (drain cut).length = remainingNative cut := List.length_replicate ..
  have waiting : (afterBacklog cut body).take (remainingNative cut) = drain cut := by
    rw [afterBacklog, ← length, List.take_append_of_le_length le_rfl, List.take_length]
  dsimp only
  rw [waiting]
  have exhausted := Quantities.Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut
  exact ⟨exhausted.1, congrArg (·.clock) exhausted.2.1, exhausted.2.2.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
