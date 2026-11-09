import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Backlog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution
open Reparation.Actual (State publishAfter)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Rival" => Nat → C → Input

private theorem observed_length (cut : C) (rival : Rival) (count : Nat) :
    (observedScript rival count cut).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [observedScript, List.length_append, List.length_singleton, ih]

/-- At a busy source, the first native visit records the submitted request.
The remaining native visits consume the competitor's actual inputs. -/
def queuedPrefix (cut : C) (submitted : Input) (rival : Rival) : Word :=
  match remainingNative cut with
  | 0 => []
  | n + 1 => submitted :: observedScript rival n (next cut submitted)

theorem queuedPrefix_length (cut : C) (submitted : Input) (rival : Rival) :
    (queuedPrefix cut submitted rival).length = remainingNative cut := by
  unfold queuedPrefix
  split
  · rename_i empty
    exact empty.symm
  · rename_i _ exactLength
    simp only [List.length_cons, observed_length, exactLength]

theorem the_busy_submission_is_in_the_actual_native_prefix (cut : C) (submitted : Input) (rival : Rival)
    (busy : Quantities.Pending cut) :
    ∃ tail : Word, queuedPrefix cut submitted rival = submitted :: tail := by
  have positive := (pending_iff_positive_original_positions cut).mp busy
  unfold queuedPrefix
  split
  · rename_i empty
    omega
  · exact ⟨_, rfl⟩

/-- The source reserves the first material visit for the original
submission. All other inputs before that visit remain on the actual path. -/
def reservation (cut : C) (submitted : Input) (rival : Rival) : Word :=
  queuedPrefix cut submitted rival ++ [submitted]

def publishReservation {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
    {past : Reparation.Actual.Script Party Good Port Technology Instrument}
    (live : State seed community past) (submitted : Input) (rival : Rival) :=
  publishAfter live (reservation (endAt seed past) submitted rival)

theorem the_first_material_visit_is_reserved_at_the_same_physical_cut (cut : C) (submitted : Input)
    (rival : Rival) :
    let queued := queuedPrefix cut submitted rival
    let material := endAt cut queued
    ¬ Quantities.Pending material ∧ material.raw = cut.raw ∧ material.control = cut.control ∧
      inventory cut queued = [] ∧
      ∀ other : Word, other.length < queued.length → Quantities.Pending (endAt cut other) := by
  have length := queuedPrefix_length cut submitted rival
  have cutExact := all_native_interleavings_spend_the_same_backlog_without_material_effects
    cut (queuedPrefix cut submitted rival) length.le
  refine ⟨?_, cutExact.2.1, cutExact.2.2.1, cutExact.2.2.2, ?_⟩
  · exact fun busy => (Nat.lt_irrefl _) (length ▸
      (exactly_the_original_rank_precedes_the_first_material_visit cut _ length.le).mp busy)
  · intro other sooner
    have early := sooner.trans_eq length
    exact (exactly_the_original_rank_precedes_the_first_material_visit cut other early.le).mpr early

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
