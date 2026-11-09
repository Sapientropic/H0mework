import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.NativeShortage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Failure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Quantities.Execution (endAt)
open Reparation.Actual (Published run publishAfter originalLosses publication_keeps_every_previous_loss)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community] {Observation : Type u}

local notation "Word" => Script Party Good Port Technology Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Script Party Good Port Technology Instrument}

def shortageWrite {word : Word} (missing : FirstNativeShortage (endAt seed past) word) :
    Published seed community (past ++ (missing.before ++ [missing.input])) :=
  publishAfter (run seed community past) (missing.before ++ [missing.input])

theorem the_named_native_shortage_keeps_its_original_whole_write {word : Word}
    (missing : FirstNativeShortage (endAt seed past) word) :
    let through := past ++ (missing.before ++ [missing.input])
    let written := shortageWrite (seed := seed) (community := community) (past := past) missing
    past ++ word = through ++ missing.after ∧
    (endAt seed through).raw = (endAt seed (past ++ missing.before)).raw ∧ Quantities.Recorded seed through ∧
    Evolving.Epoch.Current.ClosedAt (endAt seed through) ∧
    ∀ old ∈ originalLosses seed community past, ∃ balance, ∃ row, written.next.read row = .inr (old, balance) := by
  let written := shortageWrite (seed := seed) (community := community) (past := past) missing
  refine ⟨?_, ?_, written.recorded, written.recorded.next, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using congrArg (past ++ ·) missing.split
  · simpa only [Quantities.Execution.endAt_append seed past] using missing.original_prefix_and_next.2.1
  · exact publication_keeps_every_previous_loss seed community _ _

variable {command : List Party} {observe : Root.Cut Party Good Port Technology Instrument → Observation}
  {strategy : History Observation → Script Party Good Port Technology Instrument}
  {rival : List (Script Party Good Port Technology Instrument)}

local notation "opening" => endAt seed past
local notation "First" => FirstFailureWithExit opening command community observe strategy rival

/-- Read the original living shortage of the failed round, even when the
source refused the proposal before the physical clock could advance. -/
def namedShortageAtFailure (first : First) :=
  let already := (play opening observe strategy (submitted rival) first.round).script
  firstNativeShortage (endAt seed (past ++ already)) first.failure.consumed

theorem a_native_shortage_in_the_failed_round_is_written_on_that_original_path
    (first : First) (missing : FirstNativeShortage (endAt seed (past ++
      (play opening observe strategy (submitted rival) first.round).script)) first.failure.consumed) :
    let already := (play opening observe strategy (submitted rival) first.round).script
    let prior := past ++ already
    let through := prior ++ (missing.before ++ [missing.input])
    let written := shortageWrite (seed := seed) (community := community) (past := prior) missing
    past ++ first.originalScript = through ++ missing.after ∧
    (endAt seed through).raw = (endAt seed (prior ++ missing.before)).raw ∧
    Quantities.Recorded seed through ∧ Evolving.Epoch.Current.ClosedAt (endAt seed through) ∧
    ∀ old ∈ originalLosses seed community prior, ∃ balance, ∃ row, written.next.read row = .inr (old, balance) := by
  have reported := the_named_native_shortage_keeps_its_original_whole_write (seed := seed) (community := community)
    (past := past ++ (play opening observe strategy (submitted rival) first.round).script) missing
  simpa only [FirstFailureWithExit.originalScript, List.append_assoc] using reported

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace
