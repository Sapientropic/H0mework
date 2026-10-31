import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Codec

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

abbrev base (shared : Bool) := if shared then SharedAudit.source else Cell.source

def baseWord (shared : Bool) (ordinal : Nat) :=
  (base shared).frameWord ordinal ((base shared).frameAt ordinal)

def attempt (_current : Current) (register : Register) (actor : Party) (command : Command) : List RequestAt :=
  if CanRun (register actor) command then [request actor command] else []

def supplyLabor (current : Current) (donor actor : Party) (target : ℚ) : List RequestAt :=
  [transfer donor donor actor [(.labor, max 0 (target - current.stock actor .labor))]]

def optionalWork (register : Register) : List RequestAt :=
  ([1, 2] : List Party).flatMap fun actor => if register actor = .active then [audit actor] else []

def dispatch (shared : Bool) (current : Current) (register : Register) : List RequestAt :=
  match current.round with
  | 11 => supplyLabor current 0 1 3
  | 12 => attempt current register 1 .accept
  | 13 | 14 => attempt current register 1 .challenge
  | 15 => supplyLabor current 3 1 2
  | 16 => attempt current register 1 .challenge
  | 17 => supplyLabor current 3 1 1
  | 18 => attempt current register 1 .exit
  | 19 => attempt current register 2 .refuse
  | 20 => [transfer 0 0 1 [(.feed, max 0 (8 - current.stock 1 .feed)),
      (.labor, max 0 (1 - current.stock 1 .labor))]]
  | 21 => optionalWork register
  | 22 => firstCycle 1
  | 23 => supplyLabor current 3 1 1
  | 24 => attempt current register 1 .accept
  | _ =>
      let candidate := if shared then
        (SharedAudit.respond current (SharedAudit.frameAt current.round).method).word
        else (Feedback.respond current).word
      if candidate.any (fun request => match request.operation with
          | .use actor _ .contribution => decide (actor ∈ ([1, 2] : List Party) ∧ register actor ≠ .active)
          | _ => false) then [] else candidate

structure Frame where
  raw : Current
  register : Register

def wordAt (shared : Bool) (ordinal : Nat) (frame : Frame) : List RequestAt :=
  if ordinal < 11 then baseWord shared ordinal else dispatch shared frame.raw frame.register

def advanceFrame (shared : Bool) (ordinal : Nat) (frame : Frame) : Frame :=
  let word := wordAt shared ordinal frame
  ⟨law.next frame.raw word, (law.rawItems frame.raw word).foldl update frame.register⟩

def frameAt (shared : Bool) : Nat → Frame
  | 0 => ⟨initial, initialRegister⟩
  | ordinal + 1 => advanceFrame shared ordinal (frameAt shared ordinal)

theorem machine_round (shared : Bool) (ordinal : Nat) : (frameAt shared ordinal).raw.round = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change (frameAt shared ordinal).raw.round + 1 = ordinal + 1
    rw [ih]

def source (shared : Bool) : OutstandingSource Party Good Port Technology Unit :=
  { Cell.source with
    incoming? := fun _ => none
    completionReport := fun current => .original current
      (if current.round < 11 then baseWord shared current.round
       else dispatch shared current (frameAt shared current.round).register) }

theorem same_seed (shared : Bool) : (source shared).seed = (base shared).seed := by cases shared <;> rfl

theorem source_round (shared : Bool) (ordinal : Nat) : ((source shared).currentAt ordinal).round = ordinal := by
  have round := (source shared).current_round ordinal
  change ((source shared).currentAt ordinal).round = 0 + ordinal at round
  simpa only [Nat.zero_add] using round

theorem original_service_paid (shared : Bool) :
    (source shared).pendingSlots ((source shared).frameAt 2).payments = [] := by
  cases shared <;> decide +kernel

theorem actual_word (shared : Bool) (ordinal : Nat) (started : 2 ≤ ordinal) :
    ProgrammeSource.rawEvent (source shared).input (ProgrammeHistory.visitAt (source shared).input ordinal).current =
      (if ordinal < 11 then baseWord shared ordinal
       else dispatch shared ((source shared).currentAt ordinal) (frameAt shared ordinal).register) := by
  have complete := (source shared).completion_persists 2 (ordinal - 2) (original_service_paid shared)
  have emitted := (source shared).completed_word_is_source_continuation ordinal 0 started
    (by simpa only [Nat.add_sub_of_le started] using complete) rfl
  simp only [Nat.add_zero] at emitted
  rw [emitted]
  change (if ((source shared).currentAt ordinal).round < 11 then _ else _) = _
  rw [source_round]

theorem actual_current_is_the_machine (shared : Bool) (ordinal : Nat) :
    (source shared).currentAt ordinal = (frameAt shared ordinal).raw := by
  induction ordinal with
  | zero => cases shared <;> rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent (source shared).input
      (ProgrammeSource.next (source shared).input (ProgrammeHistory.visitAt (source shared).input ordinal).current) = _
    rw [ProgrammeSource.actual_raw_next]
    change law.next ((source shared).currentAt ordinal) _ = _
    by_cases zero : ordinal = 0
    · subst ordinal; cases shared <;> rfl
    by_cases first : ordinal = 1
    · subst ordinal; rw [ih]; cases shared <;> rfl
    · rw [actual_word shared ordinal (by omega), ih]
      rfl

theorem actual_word_is_the_machine (shared : Bool) (ordinal : Nat) :
    ProgrammeSource.rawEvent (source shared).input (ProgrammeHistory.visitAt (source shared).input ordinal).current =
      wordAt shared ordinal (frameAt shared ordinal) := by
  by_cases zero : ordinal = 0
  · subst ordinal; cases shared <;> rfl
  by_cases first : ordinal = 1
  · subst ordinal; cases shared <;> rfl
  · rw [actual_word shared ordinal (by omega), actual_current_is_the_machine]
    rfl

def itemsAt (shared : Bool) (ordinal : Nat) :=
  law.rawItems (frameAt shared ordinal).raw (wordAt shared ordinal (frameAt shared ordinal))

theorem items_are_original (shared : Bool) (ordinal : Nat) :
    itemsAt shared ordinal = law.rawItems ((source shared).currentAt ordinal)
      (ProgrammeSource.rawEvent (source shared).input (ProgrammeHistory.visitAt (source shared).input ordinal).current) := by
  rw [actual_current_is_the_machine, actual_word_is_the_machine]
  rfl

theorem prefix_raw (shared : Bool) (ordinal : Nat) (before_cut : ordinal ≤ 11) :
    (frameAt shared ordinal).raw = ((base shared).frameAt ordinal).raw := by
  induction ordinal with
  | zero => cases shared <;> rfl
  | succ ordinal ih =>
    change law.next (frameAt shared ordinal).raw _ = _
    rw [ih (by omega)]
    simp only [wordAt, if_pos (show ordinal < 11 by omega)]
    cases shared <;> rfl

theorem common_raw_cut (shared : Bool) :
    (source shared).currentAt 11 = (base shared).currentAt 11 :=
  (actual_current_is_the_machine shared 11).trans
    ((prefix_raw shared 11 (by decide)).trans ((base shared).canonical_frame 11).1.symm)

theorem common_original_items (shared : Bool) (ordinal : Nat) (before_cut : ordinal < 11) :
    itemsAt shared ordinal = law.rawItems ((base shared).frameAt ordinal).raw (baseWord shared ordinal) := by
  simp only [itemsAt, wordAt, if_pos before_cut, prefix_raw shared ordinal (by omega)]

theorem register_next_consumes_its_own_actual_items (shared : Bool) (ordinal : Nat) :
    (frameAt shared (ordinal + 1)).register = (itemsAt shared ordinal).foldl update (frameAt shared ordinal).register := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
