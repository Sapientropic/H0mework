import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u v w

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {CivilView : Type u} {OpponentView : Type v} {Index : Type w}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Pos" => Position Party Good Port Technology Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

/-- Reconstruct the observations of a proposed sequence by the original
tick fold. These observations must pass the strategy compatibility check. -/
def tape (inputs : Nat → Input) : Nat → Pos
  | 0 => game.start
  | tick + 1 => game.extend (tape inputs tick) (inputs tick)

theorem each_matching_input_replays_the_same_original_position
    (plan : Plan) (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn)
    (inputs : Nat → Input) (agrees : ∀ tick, game.inputAt plan.submit opponent arbitrate tick = inputs tick)
    (tick : Nat) : game.play plan.submit opponent arbitrate tick = game.tape inputs tick := by
  induction tick with
  | zero => rfl
  | succ tick earlier =>
    change game.extend (game.play plan.submit opponent arbitrate tick) (game.inputAt plan.submit opponent arbitrate tick) =
      game.extend (game.tape inputs tick) (inputs tick)
    rw [agrees tick, earlier]

variable (plans : Index → CivilPlan Party Good Port Technology Instrument CivilView)
  (arbiters : Index → Nat → Root.Cut Party Good Port Technology Instrument → Turn)
  (inputs : Index → Nat → Reparation.Actual.Input Party Good Port Technology Instrument)

abbrev tapeTurn (i : Index) (tick : Nat) :=
  arbiters i tick (game.tape (inputs i) tick).window.current

/-- The opponent may use information revealed by actual prior visits.
All schedules and civilian policies sharing that readout have one action. -/
structure TapeCompatibility : Prop where
  civil : ∀ i tick, game.tapeTurn arbiters inputs i tick = .civil →
    inputs i tick = (plans i).submit (game.tape (inputs i) tick).civilSeen
  retained : ∀ i tick, game.tapeTurn arbiters inputs i tick = .retained → inputs i tick = none
  opponent : ∀ i j tick other, game.tapeTurn arbiters inputs i tick = .opponent →
    game.tapeTurn arbiters inputs j other = .opponent →
    (game.tape (inputs i) tick).opponentSeen = (game.tape (inputs j) other).opponentSeen →
    inputs i tick = inputs j other

private def observed (seen : List OpponentView) : Prop :=
  ∃ i tick, game.tapeTurn arbiters inputs i tick = .opponent ∧ (game.tape (inputs i) tick).opponentSeen = seen

private def compiledOpponent (seen : List OpponentView) : Input := by
  classical
  exact if reached : game.observed arbiters inputs seen then
    inputs (Classical.choose reached) (Classical.choose (Classical.choose_spec reached))
  else none

private theorem compiledOpponent_on_tape (compatible : game.TapeCompatibility plans arbiters inputs)
    (i : Index) (tick : Nat) (own : game.tapeTurn arbiters inputs i tick = .opponent) :
    game.compiledOpponent arbiters inputs (game.tape (inputs i) tick).opponentSeen = inputs i tick := by
  classical
  have reached : game.observed arbiters inputs (game.tape (inputs i) tick).opponentSeen := ⟨i, tick, own, rfl⟩
  have selected := Classical.choose_spec (Classical.choose_spec reached)
  unfold compiledOpponent
  rw [dif_pos reached]
  exact compatible.opponent _ i _ tick selected.1 own selected.2

theorem one_opponent_replays_exactly_the_observation_compatible_native_tapes :
    (∃ opponent : List OpponentView → Input, ∀ i tick,
      game.inputAt (plans i).submit opponent (arbiters i) tick = inputs i tick) ↔
    game.TapeCompatibility plans arbiters inputs := by
  constructor
  · rintro ⟨opponent, replay⟩
    have selected (i : Index) (tick : Nat) :
        inputs i tick = proposal (game.tape (inputs i) tick) (plans i).submit opponent
          (game.tapeTurn arbiters inputs i tick) := by
      have same := game.each_matching_input_replays_the_same_original_position
        (plans i) opponent (arbiters i) (inputs i) (replay i) tick
      unfold tapeTurn
      rw [← same]
      exact (replay i tick).symm
    refine ⟨?_, ?_, ?_⟩
    · intro i tick lane
      rw [selected i tick, lane]
      rfl
    · intro i tick lane
      rw [selected i tick, lane]
      rfl
    · intro i j tick other first second same
      rw [selected i tick, selected j other, first, second]
      exact congrArg opponent same
  · intro compatible
    let opponent := game.compiledOpponent arbiters inputs
    have selects (i : Index) (tick : Nat) :
        proposal (game.tape (inputs i) tick) (plans i).submit opponent
          (game.tapeTurn arbiters inputs i tick) = inputs i tick := by
      cases lane : game.tapeTurn arbiters inputs i tick with
      | civil => exact (compatible.civil i tick lane).symm
      | retained => exact (compatible.retained i tick lane).symm
      | opponent => exact game.compiledOpponent_on_tape plans arbiters inputs compatible i tick lane
    have position (i : Index) (tick : Nat) :
        game.play (plans i).submit opponent (arbiters i) tick = game.tape (inputs i) tick := by
      induction tick with
      | zero => rfl
      | succ tick earlier =>
        change game.extend (game.play (plans i).submit opponent (arbiters i) tick)
          (game.inputAt (plans i).submit opponent (arbiters i) tick) =
          game.extend (game.tape (inputs i) tick) (inputs i tick)
        unfold inputAt turnAt
        rw [earlier]
        exact congrArg (game.extend (game.tape (inputs i) tick)) (selects i tick)
    refine ⟨opponent, fun i tick => ?_⟩
    unfold inputAt turnAt
    rw [position i tick]
    exact selects i tick

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
