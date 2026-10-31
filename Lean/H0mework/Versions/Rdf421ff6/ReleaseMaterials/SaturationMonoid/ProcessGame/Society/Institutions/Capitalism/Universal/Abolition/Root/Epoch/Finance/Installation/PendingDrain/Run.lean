import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain.Rank
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth : Nat)

structure Result (start : Nat) where
  private mk ::
  last : Nat
  after : start ≤ last
  within : last ≤ start + budget input (Runtime.cursorAt input depth start)
  stoppedBeforeFresh : Cursor.FreshBody input (Runtime.cursorAt input depth last)
  physicalIndex : Cursor.physicalVisitIndex input (Runtime.cursorAt input depth last) =
    Cursor.physicalVisitIndex input (Runtime.cursorAt input depth start)
  native : (Financial.process input).Run (Runtime.cursorAt input depth start).account.current
    (Runtime.cursorAt input depth last).account.current
  bookkeeping : ∀ index, start ≤ index → index < last → ¬ Cursor.FreshBody input (Runtime.cursorAt input depth index)

/-- The only recursive call is the original runtime successor. Termination
is paid by its already occurred finite inventory, including boundary ticks. -/
def drain (start : Nat) : Result input depth start :=
  if fresh : Cursor.FreshBody input (Runtime.cursorAt input depth start) then
    ⟨start, le_refl _, Nat.le_add_right _ _, fresh, rfl, .nil, fun _ after before => by omega⟩
  else
    let rest := drain (start + 1)
    have paid := bookkeeping_uses_one_unit input (Runtime.cursorAt input depth start)
      (Runtime.cursorAt_accounting input depth start) (Runtime.cursorAt_position_bounded input depth start) fresh
    ⟨rest.last, by have later := rest.after; omega,
      by have bound := rest.within; change budget input (Runtime.cursorAt input depth (start + 1)) + 1 = _ at paid; omega,
      rest.stoppedBeforeFresh,
      rest.physicalIndex.trans (Cursor.bookkeeping_physical_index input (Runtime.cursorAt input depth start) fresh),
      (Cursor.native input (Runtime.cursorAt input depth start)).concatRuns (Financial.process input) rest.native,
      fun index after before => by
        by_cases first : index = start
        · subst index; exact fresh
        · exact rest.bookkeeping index (by omega) before⟩
termination_by budget input (Runtime.cursorAt input depth start)
decreasing_by
  exact bookkeeping_decreases input (Runtime.cursorAt input depth start)
    (Runtime.cursorAt_accounting input depth start) (Runtime.cursorAt_position_bounded input depth start) fresh

def frame (start : Nat) : Runtime.Frame input := Runtime.frames input depth (drain input depth start).last

theorem literal_runtime_frame (start : Nat) :
    frame input depth start = Runtime.frames input depth (drain input depth start).last := rfl

theorem no_physical_body_is_replayed (start : Nat) :
    Cursor.physicalVisit input ((frame input depth start).cursor input) =
      Cursor.physicalVisit input ((Runtime.frames input depth start).cursor input) := by
  rw [frame, Runtime.frames_cursor, Runtime.frames_cursor]
  exact congrArg (ProgrammeHistory.visitAt input) (drain input depth start).physicalIndex

theorem original_physical_claims_and_clock_are_unchanged (start : Nat) :
    (ProgrammeSource.rawCurrent input (Cursor.physicalVisit input ((frame input depth start).cursor input)).current).claims =
      (ProgrammeSource.rawCurrent input (Cursor.physicalVisit input ((Runtime.frames input depth start).cursor input)).current).claims ∧
    (ProgrammeSource.rawCurrent input (Cursor.physicalVisit input ((frame input depth start).cursor input)).current).clock =
      (ProgrammeSource.rawCurrent input (Cursor.physicalVisit input ((Runtime.frames input depth start).cursor input)).current).clock := by
  rw [no_physical_body_is_replayed]
  exact ⟨rfl, rfl⟩

theorem issued_step_is_the_original_root_birth (index : Nat)
    (registered : Registration input (Runtime.frames input depth index).native (Runtime.frames input depth index).visit.current)
    (selected : registration? input (Runtime.frames input depth index).native
      (Runtime.frames input depth index).visit.current = some registered) :
    Runtime.frames input depth (index + 1) = (Runtime.frames input depth index).born input registered := by
  change (Runtime.frames input depth index).next input = _
  rw [Runtime.Frame.next, selected]

theorem finite_bound_is_the_original_queue (start : Nat) :
    (drain input depth start).last - start ≤ budget input (Runtime.cursorAt input depth start) := by
  have bounded := (drain input depth start).within
  omega

#print axioms drain
#print axioms no_physical_body_is_replayed
#print axioms issued_step_is_the_original_root_birth
#print axioms finite_bound_is_the_original_queue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain
