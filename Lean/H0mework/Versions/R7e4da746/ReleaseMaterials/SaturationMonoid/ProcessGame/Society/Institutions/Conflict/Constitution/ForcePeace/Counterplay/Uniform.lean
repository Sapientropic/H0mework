import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Observation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Quantifiers

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u v w

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v} {Index : Type w}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

abbrev tapeDamageAt (inputs : Nat → Input) (tick : Nat) :=
  Boundary.Actual.DamageAt (game.tape inputs tick).window.current (inputs tick) game.community

private theorem a_replayed_tape_has_the_same_material_damage
    (plan : Plan) (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn)
    (inputs : Nat → Input) (agrees : ∀ tick, game.inputAt plan.submit opponent arbitrate tick = inputs tick)
    (tick : Nat) :
    Nonempty (game.DamageAt plan opponent arbitrate tick) ↔ Nonempty (game.tapeDamageAt inputs tick) := by
  unfold DamageAt tapeDamageAt currentAt
  rw [agrees tick, game.each_matching_input_replays_the_same_original_position plan opponent arbitrate inputs agrees]

/-- Cross-history compatibility is the exact extra condition for one
opposing observation policy. An index can include the civilian policy and
the native interleaving, so the witness may be tested on the entire family. -/
theorem one_forcing_opponent_iff_the_actual_countertraces_agree_on_its_observations
    (plans : Index → Plan) (arbiters : Index → Nat → C → Turn) :
    (∃ opponent : List OpponentView → Input, ∀ i, Nonempty (game.FirstAttack (plans i) opponent (arbiters i))) ↔
      ∃ inputs : Index → Nat → Input, game.TapeCompatibility plans arbiters inputs ∧
        ∀ i, ∃ tick, Nonempty (game.tapeDamageAt (inputs i) tick) := by
  constructor
  · rintro ⟨opponent, attacks⟩
    let inputs (i : Index) := game.inputAt (plans i).submit opponent (arbiters i)
    have agrees (i : Index) (tick : Nat) : game.inputAt (plans i).submit opponent (arbiters i) tick = inputs i tick :=
      rfl
    refine ⟨inputs, (game.one_opponent_replays_exactly_the_observation_compatible_native_tapes
      plans arbiters inputs).mp ⟨opponent, agrees⟩, fun i => ?_⟩
    obtain ⟨first⟩ := attacks i
    exact ⟨first.tick, (game.a_replayed_tape_has_the_same_material_damage (plans i) opponent
      (arbiters i) (inputs i) (agrees i) first.tick).mp ⟨first.damage⟩⟩
  · rintro ⟨inputs, compatible, attacks⟩
    obtain ⟨opponent, agrees⟩ :=
      (game.one_opponent_replays_exactly_the_observation_compatible_native_tapes plans arbiters inputs).mpr compatible
    refine ⟨opponent, fun i => ⟨game.firstAttack (plans i) opponent (arbiters i) ?_⟩⟩
    obtain ⟨tick, damage⟩ := attacks i
    exact ⟨tick, (game.a_replayed_tape_has_the_same_material_damage (plans i) opponent
      (arbiters i) (inputs i) (agrees i) tick).mpr damage⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
