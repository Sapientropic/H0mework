import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : ProgrammeFamily base scope Index)
  (inputs : Index)

theorem native_admission_allocates_live (claim : Claim bound inputs) :
    (History.initial bound inputs claim).state.current.LiveAt 0 :=
  ⟨obligation bound inputs claim, rfl⟩

theorem History.live_of_pending {claim : Claim bound inputs} (history : History bound inputs claim)
    (pending : history.isPending bound inputs = true) : history.state.current.LiveAt 0 := by
  cases history with
  | pending target state slots => exact ⟨tracked bound inputs claim target, by simp [History.state, slots]⟩
  | closed state archive slots => cases pending

theorem original_admission_and_responsibility_are_retained (original : Claim bound inputs) (target : Target bound inputs original) :
    (tracked bound inputs original target).admission = (obligation bound inputs original).admission ∧
    (tracked bound inputs original target).bearer = original.actor bound inputs ∧
    (tracked bound inputs original target).content = original ∧
    (tracked bound inputs original target).scope = original.origin bound inputs ∧
    (tracked bound inputs original target).lineage = original.origin bound inputs := ⟨rfl, rfl, rfl, rfl, rfl⟩

def receiveRun {original : Claim bound inputs} (history : History bound inputs original) (position : Position bound inputs) :
    (process bound inputs original).Run history.state.current (history.receive bound inputs position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending target state slots =>
    cases renewed : readReconfirmation bound inputs original position with
    | some receipt =>
      simp only [History.receive, renewed]
      split
      · rename_i later
        exact .step .nil (.cross (P := process bound inputs original) ⟨0, by simp [History.state, slots]⟩
          (tracked bound inputs original target) (by simp [History.state, slots]) (.reaffirm target receipt later rfl))
      · exact .nil
    | none =>
      cases attempted : readAttempt bound inputs (target.claim bound inputs) position with
      | none => simp only [History.receive, renewed, attempted]; exact .nil
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · exact .step .nil (.cross (P := process bound inputs original) ⟨0, by simp [History.state, slots]⟩
            (tracked bound inputs original target) (by simp [History.state, slots]) (.attempt target receipt rfl))
        · exact .step .nil (.cross (P := process bound inputs original) ⟨0, by simp [History.state, slots]⟩
            (tracked bound inputs original target) (by simp [History.state, slots]) (.attempt target receipt rfl))

def visitRun {original : Claim bound inputs} (history : History bound inputs original) (positions : List (Position bound inputs)) :
    (process bound inputs original).Run history.state.current
      (positions.foldl (History.receive bound inputs) history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun bound inputs history position).concatRuns _ (ih (history.receive bound inputs position))

def continueFrom {original : Claim bound inputs} (history : History bound inputs original) (count : Nat) : Nat → History bound inputs original
  | 0 => history
  | later + 1 => (positionsAt bound inputs (count + later)).foldl (History.receive bound inputs) (continueFrom history count later)

def continuationRun {original : Claim bound inputs} (history : History bound inputs original) (count : Nat) : (later : Nat) →
    (process bound inputs original).Run history.state.current (continueFrom bound inputs history count later).state.current
  | 0 => .nil
  | later + 1 => (continuationRun history count later).concatRuns _
      (visitRun bound inputs (continueFrom bound inputs history count later) (positionsAt bound inputs (count + later)))

theorem continuation_is_own_actual_history (original : Claim bound inputs) (count later : Nat) :
    continueFrom bound inputs (through bound inputs original count) count later = through bound inputs original (count + later) := by
  induction later with
  | zero => rfl
  | succ later ih =>
      change (positionsAt bound inputs (count + later)).foldl (History.receive bound inputs)
        (continueFrom bound inputs (through bound inputs original count) count later) =
        (positionsAt bound inputs (count + later)).foldl (History.receive bound inputs)
          (through bound inputs original (count + later))
      rw [ih]

def fromActualCut (original : Claim bound inputs) (count later : Nat) :
    (process bound inputs original).Run (through bound inputs original count).state.current
      (through bound inputs original (count + later)).state.current :=
  (continuation_is_own_actual_history bound inputs original count later) ▸
    continuationRun bound inputs (through bound inputs original count) count later

theorem every_decoded_claim_is_consumed (position : Position bound inputs) (claim : Claim bound inputs)
    (decoded : read bound inputs position = some claim) (count : Nat) (inside : position.ordinal < count) :
    (⟨claim, through bound inputs claim count⟩ : Sigma fun original : Claim bound inputs => History bound inputs original) ∈
      recordsAt bound inputs count := by
  apply List.mem_flatMap.mpr
  refine ⟨position.ordinal, List.mem_range.mpr inside, List.mem_map.mpr ⟨claim, ?_, rfl⟩⟩
  apply List.mem_filterMap.mpr
  refine ⟨position, ?_, decoded⟩
  apply List.mem_map.mpr
  exact ⟨position.index, List.mem_finRange _, by cases position; rfl⟩

theorem fulfilled_receipt_has_actual_withdrawal (event : Event bound inputs) (claim : Claim bound inputs)
    (origin : Financial.InstructionOrigin (I bound inputs)) (receipt : Event.ResolvedAt bound inputs event claim origin) :
    ∃ (target : Target bound inputs claim) (attempt : Attempt bound inputs (target.claim bound inputs)),
      event = .attempt claim target attempt ∧
      (target.claim bound inputs).actor bound inputs = claim.actor bound inputs ∧
      (law base scope).Valid (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request ∧
      ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.holder = none ∧
      ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.offered = none ∧
      ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.version =
        ((target.claim bound inputs).snapshot bound inputs).version + 1 := by
  cases event with
  | birth original => exact nomatch receipt
  | reaffirm original previous renewed => exact nomatch receipt
  | remoteReaffirm original actualInputs previous renewed => exact nomatch receipt
  | remoteAttempt original actualInputs target attempt => exact nomatch receipt
  | scopeBoundary original source laterWindow boundary => exact nomatch receipt
  | attempt original target attempt =>
    rcases receipt with ⟨rfl, _, accepted⟩
    exact ⟨target, attempt, rfl, target.actor bound inputs, accepted, attempt.actual_withdrawal bound inputs _ accepted⟩

theorem actual_native_history (original : Claim bound inputs) (count : Nat) :
    (through bound inputs original count).state.current.history =
      (through bound inputs original count).state.generated.events :=
  (through bound inputs original count).state.history_eq

theorem a_terminal_archive_is_never_replaced {original : Claim bound inputs}
    (state : (process bound inputs original).GeneratedState) (archive : TerminalArchive (V bound inputs))
    (slots : state.current.slots = [.terminal archive]) (count later : Nat) :
    continueFrom bound inputs (.closed state archive slots) count later = .closed state archive slots := by
  induction later with
  | zero => rfl
  | succ later ih =>
    simp only [continueFrom, ih]
    have unchanged : ∀ positions : List (Position bound inputs),
        positions.foldl (History.receive bound inputs) (.closed state archive slots) = .closed state archive slots := by
      intro positions
      induction positions with
      | nil => rfl
      | cons position tail ih => exact ih
    exact unchanged _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge
