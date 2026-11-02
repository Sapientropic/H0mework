import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication.Comparison
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access
import Mathlib.Data.Rat.Floor

/-! Saved fuel funds actual unit maintenance requests.  The source reads its
own remaining stock, keeps one unit, and never receives a dividend or a
successful continuation as input.  The two branches have distinct roots. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal
open Source.Program
open Root
open Instances.OpenReplication

abbrev Current := Instances.OpenReplication.Current
abbrev RequestAt := Instances.OpenReplication.Input

def route (n : Nat) (shared : Bool) : List RequestAt :=
  if shared then publicRoute n else exclusive n

def maintenanceBudget (current : Current) : Nat := ⌊current.stock false false - 1⌋₊

def reinvest (current : Current) : List RequestAt :=
  List.replicate (maintenanceBudget current) maintain

def dispatch (n : Nat) (shared : Bool) (current : Current) : List RequestAt :=
  if current.round = 1 then route n shared
  else if current.round = 2 then reinvest current
  else if 3 ≤ current.round then (Access.respond n current).word else []

def report (n : Nat) (shared : Bool) (current : Current) :
    ProgrammeSource.ProgrammeReport Bool Bool (Option Bool) Bool Unit :=
  .original current (dispatch n shared current)

def input (n : Nat) (shared : Bool) : ProgrammeSource.Input Bool Bool (Option Bool) Bool Unit where
  law := law n
  initial := initial n
  instructions := []
  emission? := some (dispatch n shared)
  observedEmission? := some { generate := report n shared, word := ProgrammeSource.ProgrammeReport.word }

def currentAt (n : Nat) (shared : Bool) (visit : Nat) : Current :=
  ProgrammeSource.rawCurrent (input n shared) (ProgrammeHistory.visitAt (input n shared) visit).current

def execution (n : Nat) (shared : Bool) (visit : Nat) :=
  (ProgrammeLiving.projectionLaw (input n shared)).project .execution
    (ProgrammeSource.emitted (input n shared) (ProgrammeHistory.visitAt (input n shared) visit).current) ()

theorem word_from_current (n : Nat) (shared : Bool) (visit : Nat) :
    (execution n shared (visit + 1)).submitted = dispatch n shared (currentAt n shared (visit + 1)) := by
  change ProgrammeSource.rawEvent (input n shared)
    (ProgrammeSource.next (input n shared) (ProgrammeHistory.visitAt (input n shared) visit).current) =
      dispatch n shared (ProgrammeSource.rawCurrent (input n shared)
        (ProgrammeSource.next (input n shared) (ProgrammeHistory.visitAt (input n shared) visit).current))
  generalize (ProgrammeHistory.visitAt (input n shared) visit).current = frame
  cases frame <;> rfl

theorem actual_next (n : Nat) (shared : Bool) (visit : Nat) :
    (execution n shared visit).after = currentAt n shared (visit + 1) :=
  (execution n shared visit).root_next_exact

theorem first_current (n : Nat) (shared : Bool) :
    currentAt n shared 1 = (initial n).retime 1 1 := by
  change (law n).next (initial n) [] = _
  norm_num [RawLaw.next, RawLaw.execute, initial, state, law, RawCurrent.retime]

theorem first_word (n : Nat) (shared : Bool) :
    (execution n shared 1).submitted = route n shared := by
  rw [word_from_current n shared 0, first_current]
  simp [dispatch, initial, state, RawCurrent.retime]

theorem task_current (n : Nat) (shared : Bool) :
    currentAt n shared 2 =
      (state (if shared then (n : ℚ) + 2 else 1) 0 0 shared).retime 2 2 := by
  rw [← actual_next n shared 1]
  change (law n).next (currentAt n shared 1) (execution n shared 1).submitted = _
  rw [first_current, first_word]
  simp only [RawLaw.next, (law n).execute_retime (time_independent n)]
  cases shared
  · simp only [route, Bool.false_eq_true, ↓reduceIte, exclusive_execution]
    norm_num [initial, state, law, RawCurrent.retime]
  · simp only [route, ↓reduceIte, public_execution]
    norm_num [initial, state, law, RawCurrent.retime]

theorem reinvestment_budget (n : Nat) (shared : Bool) :
    maintenanceBudget (currentAt n shared 2) = if shared then n + 1 else 0 := by
  rw [task_current]
  cases shared
  · norm_num [maintenanceBudget, state, RawCurrent.retime]
  · simp only [maintenanceBudget, state, RawCurrent.retime, Bool.false_eq_true, ↓reduceIte]
    rw [show (n : ℚ) + 2 - 1 = ((n + 1 : Nat) : ℚ) by push_cast; ring]
    exact Nat.floor_natCast _

theorem reinvestment_word (n : Nat) (shared : Bool) :
    (execution n shared 2).submitted = List.replicate (if shared then n + 1 else 0) maintain := by
  rw [word_from_current n shared 1]
  change dispatch n shared (currentAt n shared 2) = _
  have round : (currentAt n shared 2).round = 2 := by rw [task_current]; rfl
  simp only [dispatch, round, show ¬(2 : Nat) = 1 by decide, ↓reduceIte, reinvest, reinvestment_budget]

theorem canonical_frame (n : Nat) (shared : Bool) (depth : Nat) :
    (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current =
      .running (currentAt n shared (depth + 1))
        (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current) := by
  change ProgrammeSource.next (input n shared) (ProgrammeHistory.visitAt (input n shared) depth).current = _
  unfold currentAt
  change ProgrammeSource.next (input n shared) (ProgrammeHistory.visitAt (input n shared) depth).current =
    .running (ProgrammeSource.rawCurrent (input n shared)
      (ProgrammeSource.next (input n shared) (ProgrammeHistory.visitAt (input n shared) depth).current))
      (ProgrammeSource.pastAt (ProgrammeSource.next (input n shared)
        (ProgrammeHistory.visitAt (input n shared) depth).current))
  generalize (ProgrammeHistory.visitAt (input n shared) depth).current = frame
  cases frame <;> rfl

def taskEntry (n : Nat) (shared : Bool) (depth : Nat) :
    OpenResponsibilityAt (ProgrammeSource.N (input n shared))
      (ProgrammeSource.supportAt (input n shared) (.running (currentAt n shared (depth + 1))
        (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current))) :=
  ⟨.instruction ⟨0, by change 0 < 1; decide⟩, ()⟩

def taskWrite (n : Nat) (shared : Bool) (depth : Nat) :=
  (ProgrammeLedger.evolution (input n shared) (.running (currentAt n shared (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current))).destination
      (taskEntry n shared depth)

def writtenReceipt (n : Nat) (shared : Bool) (depth : Nat) :=
  ProgrammeLedger.writtenTransferReceipt (input n shared) (currentAt n shared (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current)
    (taskEntry n shared depth)

theorem written_report (n : Nat) (shared : Bool) (depth : Nat) :
    (writtenReceipt n shared depth).val =
      .original (currentAt n shared (depth + 1)) (execution n shared (depth + 1)).submitted := by
  unfold writtenReceipt
  rw [ProgrammeLedger.writtenTransferReceipt_exact]
  rw [word_from_current]
  rfl

theorem actual_row_receipt (n : Nat) (shared : Bool) (depth : Nat) :
    ProgrammeLedger.transferReceiptOf (input n shared) (taskWrite n shared depth).2 =
      some (writtenReceipt n shared depth) := by
  unfold writtenReceipt
  rw [ProgrammeLedger.writtenTransferReceipt_exact]
  exact ProgrammeLedger.destination_transfer_receipt _ _ _ _

theorem actual_row_is_original_destination (n : Nat) (shared : Bool) (depth : Nat) :
    HEq (taskWrite n shared depth)
      ((ProgrammeLedger.evolution (input n shared)
        (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current).destination
          (ProgrammeSource.sourceEntry (input n shared)
            (ProgrammeHistory.visitAt (input n shared) (depth + 1)).current
            (.instruction ⟨0, by change 0 < 1; decide⟩))) := by
  have identify (frame : ProgrammeSource.Current Current)
      (running : frame = .running (ProgrammeSource.rawCurrent (input n shared) frame)
        (ProgrammeSource.pastAt frame)) :
      HEq ((ProgrammeLedger.evolution (input n shared)
        (.running (ProgrammeSource.rawCurrent (input n shared) frame) (ProgrammeSource.pastAt frame))).destination
          ⟨.instruction ⟨0, by change 0 < 1; decide⟩, ()⟩)
        ((ProgrammeLedger.evolution (input n shared) frame).destination
          (ProgrammeSource.sourceEntry (input n shared) frame
            (.instruction ⟨0, by change 0 < 1; decide⟩))) := by
    cases frame with
    | bootstrap => cases running
    | running current past => rfl
  exact identify _ (canonical_frame n shared depth)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend
