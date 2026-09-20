import H0mework.Physics.MotherProgrammesFormationCoordinates.HistoriesConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths

open Stage9C.Revision WholePointFormation WholePointHistories MotherFamilyOccurrence
open MotherCoordinateCompletion

noncomputable section

def zeroEvent : Carrier := (fromRational (65 * 4) (fun _ => 0) : Carrier)

private theorem add_zero_event (value : Carrier) : completedAdd (65 * 4) value zeroEvent = value := by
  apply (coordinates_isometry (65 * 4)).injective
  rw [coordinates_add]
  have zero : coordinates (65 * 4) zeroEvent = 0 := by
    rw [show zeroEvent = (fromRational (65 * 4) (fun _ => 0) : Carrier) from rfl, coordinates_coe]
    funext slot
    exact Rat.cast_zero
  rw [zero, add_zero]

theorem act_at (visit : ℕ) (value event : Carrier) :
    act (SpinPair.visit visit, value) event =
      (SpinPair.visit (visit + 1), completedAdd (65 * 4) value event) := by
  apply Prod.ext
  · exact target_native _
  · rfl

theorem replay_visit (visit : ℕ) (value : Carrier) (events : List Carrier) :
    (replay (SpinPair.visit visit, value) events).1 = SpinPair.visit (visit + events.length) := by
  induction events generalizing visit value with
  | nil => rfl
  | cons event events induction =>
      rw [replay, act_at, induction]
      congr 1
      simp only [List.length_cons]
      omega

theorem trace_visits (visit : ℕ) (value : Carrier) (events : List Carrier) :
    (trace (SpinPair.visit visit, value) events).map Prod.fst =
      (List.range' visit (events.length + 1)).map SpinPair.visit := by
  induction events generalizing visit value with
  | nil => rfl
  | cons event events induction =>
      change SpinPair.visit visit :: (trace (act (SpinPair.visit visit, value) event) events).map Prod.fst = _
      rw [act_at, induction]
      rfl

theorem replay_wait (visit count : ℕ) (value : Carrier) :
    replay (SpinPair.visit visit, value) (List.replicate count zeroEvent) =
      (SpinPair.visit (visit + count), value) := by
  induction count generalizing visit with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, replay, act_at, add_zero_event, induction]
      congr 2
      omega

/-- Every waiting step executes the original successor; the last step
alone changes the complete operand to the requested carrier. -/
theorem segment_to (start finish : ℕ) (before after : Carrier) (late : start < finish) :
    ∃ events : List Carrier, events.length = finish - start ∧
      events ≠ [] ∧ replay (SpinPair.visit (10 + start), before) events =
        (SpinPair.visit (10 + finish), after) := by
  let delay := finish - start - 1
  let last := completedSub (65 * 4) after before
  refine ⟨List.replicate delay zeroEvent ++ [last], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    dsimp only [delay]
    omega
  · intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at lengths
    omega
  · rw [replay_append, replay_wait]
    change act (SpinPair.visit (10 + start + delay), before) last = _
    rw [act_at]
    apply Prod.ext
    · exact congrArg SpinPair.visit (show 10 + start + delay + 1 = 10 + finish by
        dsimp only [delay]
        omega)
    · exact (completed_event_recovered (65 * 4) before after).1

theorem replay_mem_steps (before : State) (events : List Carrier) (nonempty : events ≠ []) :
    replay before events ∈ steps before events := by
  induction events generalizing before with
  | nil => exact False.elim (nonempty rfl)
  | cons event events induction =>
      cases events with
      | nil => exact List.mem_cons_self
      | cons next rest =>
          exact List.mem_cons_of_mem _ (induction (act before event) (by simp))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths
