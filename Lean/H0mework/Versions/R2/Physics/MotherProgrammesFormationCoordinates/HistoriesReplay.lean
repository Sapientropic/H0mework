import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.WholeConsumption

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories

open WholePointFormation MotherFamilyOccurrence

noncomputable section

def stateEquiv : State ≃ GeneratedPotentialHistory.State where
  toFun := statePoints
  invFun state := (state.1, pointEquiv.symm state.2)
  left_inv state := Prod.ext rfl (pointEquiv.symm_apply_apply state.2)
  right_inv state := Prod.ext rfl (pointEquiv.apply_symm_apply state.2)

def replay (before : State) : List Carrier → State
  | [] => before
  | event :: events => replay (act before event) events

def steps (before : State) : List Carrier → List State
  | [] => []
  | event :: events => act before event :: steps (act before event) events

def trace (before : State) (events : List Carrier) : List State := before :: steps before events

def rawReplay (before : GeneratedPotentialHistory.State) : List PotentialSourceFormation.Points →
    GeneratedPotentialHistory.State
  | [] => before
  | event :: events => rawReplay (GeneratedPotentialHistory.act before event) events

def rawSteps (before : GeneratedPotentialHistory.State) : List PotentialSourceFormation.Points →
    List GeneratedPotentialHistory.State
  | [] => []
  | event :: events => GeneratedPotentialHistory.act before event ::
      rawSteps (GeneratedPotentialHistory.act before event) events

def rawTrace (before : GeneratedPotentialHistory.State) (events : List PotentialSourceFormation.Points) :=
  before :: rawSteps before events

theorem replay_append (before : State) (first last : List Carrier) :
    replay before (first ++ last) = replay (replay before first) last := by
  induction first generalizing before with
  | nil => rfl
  | cons event events induction => simpa only [List.cons_append, replay] using induction (act before event)

theorem replay_next (before : State) (events : List Carrier) (event : Carrier) :
    replay before (events ++ [event]) = act (replay before events) event := by
  rw [replay_append]
  rfl

theorem steps_append (before : State) (first last : List Carrier) :
    steps before (first ++ last) = steps before first ++ steps (replay before first) last := by
  induction first generalizing before with
  | nil => rfl
  | cons event events induction => simp only [List.cons_append, steps, replay, induction]

theorem trace_prefix (before : State) (first last : List Carrier) :
    (trace before first).IsPrefix (trace before (first ++ last)) := by
  refine ⟨steps (replay before first) last, ?_⟩
  simp only [trace, List.cons_append, steps_append]

theorem steps_length (before : State) (events : List Carrier) :
    (steps before events).length = events.length := by
  induction events generalizing before with
  | nil => rfl
  | cons event events induction => simp only [steps, List.length_cons, induction]

theorem trace_length (before : State) (events : List Carrier) :
    (trace before events).length = events.length + 1 := by
  simp only [trace, List.length_cons, steps_length]

theorem replay_commutes (before : State) (events : List Carrier) :
    statePoints (replay before events) = rawReplay (statePoints before) (events.map points) := by
  induction events generalizing before with
  | nil => rfl
  | cons event events induction =>
      simp only [replay, List.map_cons, rawReplay, induction]
      rw [next_commutes]
      rfl

theorem steps_commute (before : State) (events : List Carrier) :
    (steps before events).map statePoints = rawSteps (statePoints before) (events.map points) := by
  induction events generalizing before with
  | nil => rfl
  | cons event events induction =>
      simp only [steps, List.map_cons, rawSteps, induction]
      rw [next_commutes]
      rfl

theorem trace_commutes (before : State) (events : List Carrier) :
    (trace before events).map statePoints = rawTrace (statePoints before) (events.map points) := by
  simp only [trace, rawTrace, List.map_cons, steps_commute]

private theorem events_readback (events : List PotentialSourceFormation.Points) :
    (events.map pointEquiv.symm).map points = events := by
  change (events.map pointEquiv.symm).map pointEquiv = events
  simp only [List.map_map, Function.comp_def, Equiv.apply_symm_apply]
  exact List.map_id _

theorem raw_replay_readback (before : GeneratedPotentialHistory.State)
    (events : List PotentialSourceFormation.Points) :
    replay (stateEquiv.symm before) (events.map pointEquiv.symm) =
      stateEquiv.symm (rawReplay before events) := by
  apply stateEquiv.injective
  rw [stateEquiv.apply_symm_apply]
  change statePoints (replay _ _) = _
  rw [replay_commutes, events_readback,
    show statePoints (stateEquiv.symm before) = before from stateEquiv.apply_symm_apply before]

theorem raw_trace_readback (before : GeneratedPotentialHistory.State)
    (events : List PotentialSourceFormation.Points) :
    (rawTrace before events).map stateEquiv.symm =
      trace (stateEquiv.symm before) (events.map pointEquiv.symm) := by
  have forward := trace_commutes (stateEquiv.symm before) (events.map pointEquiv.symm)
  rw [events_readback,
    show statePoints (stateEquiv.symm before) = before from stateEquiv.apply_symm_apply before] at forward
  rw [← forward, List.map_map]
  change (trace _ _).map (fun state => stateEquiv.symm (stateEquiv state)) = _
  simp only [Equiv.symm_apply_apply]
  exact List.map_id _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories
