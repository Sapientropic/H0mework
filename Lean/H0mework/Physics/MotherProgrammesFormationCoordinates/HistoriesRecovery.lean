import H0mework.Physics.MotherProgrammesFormationCoordinates.HistoriesReplay

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories

open WholePointFormation MotherCoordinateCompletion MotherFamilyOccurrence

noncomputable section

def recover : List State → List Carrier
  | before :: after :: rest => completedSub (65 * 4) after.2 before.2 :: recover (after :: rest)
  | _ => []

def rawRecover : List GeneratedPotentialHistory.State → List PotentialSourceFormation.Points
  | before :: after :: rest => (after.2 - before.2) :: rawRecover (after :: rest)
  | _ => []

theorem adjacent_event (before : State) (event : Carrier) :
    completedSub (65 * 4) (act before event).2 before.2 = event :=
  (completed_event_recovered (65 * 4) before.2 event).2

theorem adjacent_points (before : State) (event : Carrier) :
    points (act before event).2 - points before.2 = points event := by
  change points (completedAdd (65 * 4) before.2 event) - points before.2 = _
  rw [WholePointFormation.points_add]
  abel

theorem recover_trace (before : State) (events : List Carrier) :
    recover (trace before events) = events := by
  induction events generalizing before with
  | nil => rfl
  | cons event events induction =>
      change completedSub (65 * 4) (act before event).2 before.2 ::
        recover (trace (act before event) events) = event :: events
      rw [adjacent_event, induction]

theorem raw_recover_trace (before : GeneratedPotentialHistory.State)
    (events : List PotentialSourceFormation.Points) : rawRecover (rawTrace before events) = events := by
  induction events generalizing before with
  | nil => rfl
  | cons event events induction =>
      change ((GeneratedPotentialHistory.act before event).2 - before.2) ::
        rawRecover (rawTrace (GeneratedPotentialHistory.act before event) events) = event :: events
      rw [GeneratedPotentialHistory.event_delta_recovered, induction]

theorem recover_from_points (before : State) (events : List Carrier) :
    (rawRecover ((trace before events).map WholePointFormation.statePoints)).map pointEquiv.symm = events := by
  rw [trace_commutes, raw_recover_trace, List.map_map]
  change events.map (fun event => pointEquiv.symm (pointEquiv event)) = events
  simp only [Equiv.symm_apply_apply]
  exact List.map_id _

theorem trace_injective (before : State) : Function.Injective (trace before) := by
  intro first last same
  have recovered := congrArg recover same
  simpa only [recover_trace] using recovered

/-- The only path constraint is the original successor at every adjacent visit. -/
def Lawful : List State → Prop
  | before :: after :: rest => after.1 = targetVisit before.1 ∧ Lawful (after :: rest)
  | _ => True

theorem trace_lawful (before : State) (events : List Carrier) : Lawful (trace before events) := by
  induction events generalizing before with
  | nil => trivial
  | cons event events induction => exact ⟨rfl, induction (act before event)⟩

theorem reconstruct_lawful (before : State) (rest : List State) (lawful : Lawful (before :: rest)) :
    trace before (recover (before :: rest)) = before :: rest := by
  induction rest generalizing before with
  | nil => rfl
  | cons after rest induction =>
      have native := lawful.1
      have step : act before (completedSub (65 * 4) after.2 before.2) = after :=
        Prod.ext native.symm (completed_event_recovered (65 * 4) before.2 after.2).1
      change before :: act before (completedSub (65 * 4) after.2 before.2) ::
        steps (act before (completedSub (65 * 4) after.2 before.2)) (recover (after :: rest)) = _
      rw [step]
      exact congrArg (List.cons before) (induction after lawful.2)

theorem every_lawful_trace (before : State) (rest : List State) :
    (∃! events : List Carrier, trace before events = before :: rest) ↔ Lawful (before :: rest) := by
  constructor
  · rintro ⟨events, generated, _⟩
    exact generated ▸ trace_lawful before events
  · intro lawful
    refine ⟨recover (before :: rest), reconstruct_lawful before rest lawful, ?_⟩
    intro events generated
    exact (trace_injective before) (generated.trans (reconstruct_lawful before rest lawful).symm)

private theorem cancelling_terminal (before : State) (event : Carrier) :
    replay before [event, completedNeg (65 * 4) event] =
      (targetVisit (targetVisit before.1), before.2) := by
  apply Prod.ext
  · rfl
  · apply (coordinates_isometry (65 * 4)).injective
    change coordinates (65 * 4) (completedAdd (65 * 4)
      (completedAdd (65 * 4) before.2 event) (completedNeg (65 * 4) event)) = _
    rw [coordinates_add, coordinates_add, coordinates_neg]
    abel

theorem same_terminal_distinct_histories (before : State) :
    ∃ first last : List Carrier, replay before first = replay before last ∧
      first.length = last.length ∧ trace before first ≠ trace before last := by
  let one : Carrier := (fromRational (65 * 4) (fun _ => 1) : Carrier)
  let zero : Carrier := (fromRational (65 * 4) (fun _ => 0) : Carrier)
  have different : one ≠ zero := by
    intro same
    have coordinate := congrArg (fun value : Carrier => coordinates (65 * 4) value 0) same
    dsimp only [one, zero] at coordinate
    rw [coordinates_coe, coordinates_coe] at coordinate
    change ((1 : ℚ) : ℝ) = ((0 : ℚ) : ℝ) at coordinate
    norm_num at coordinate
  refine ⟨[one, completedNeg (65 * 4) one], [zero, completedNeg (65 * 4) zero],
    (cancelling_terminal before one).trans (cancelling_terminal before zero).symm, rfl, ?_⟩
  intro same
  exact different (List.cons.inj ((trace_injective before) same)).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories
