import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Exit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "P" => Prefix Party Good Port Technology Instrument Observation
local notation "Strategy" => History Observation → Word
local notation "Rival" => Nat → C → Word → Word

private def replyAt (strategy : Strategy) (choose : Rival) (round : Nat) (earlier : P) : Word :=
  let move := strategy earlier.position.seen
  choose round (earlier.position.window.run move).current move

/-- The rival may read the actual post-intervention cut and respond to the
submitted word. The civilian is still bound by its earlier observation. -/
def adaptivePlay (origin : C) (read : C → Observation) (strategy : Strategy) (choose : Rival) : Nat → P
  | 0 => ⟨[], Position.start origin read⟩
  | round + 1 =>
      let earlier := adaptivePlay origin read strategy choose round
      let move := strategy earlier.position.seen
      let reply := replyAt strategy choose round earlier
      ⟨earlier.script ++ (move ++ reply), earlier.position.extend read move reply⟩

def emitted (origin : C) (read : C → Observation) (strategy : Strategy) (choose : Rival) (round : Nat) : Word :=
  replyAt strategy choose round (adaptivePlay origin read strategy choose round)

theorem adaptive_play_is_the_actual_play_of_its_emitted_inputs
    (origin : C) (read : C → Observation) (strategy : Strategy) (choose : Rival) (round : Nat) :
    adaptivePlay origin read strategy choose round = play origin read strategy (emitted origin read strategy choose) round := by
  induction round with
  | zero => rfl
  | succ round earlier => simp only [adaptivePlay, play, emitted, ← earlier]

theorem a_protecting_strategy_pays_exit_against_every_adaptive_rival
    {origin : C} {command : List Party} {community : Party → Community} {read : C → Observation}
    {strategy : Strategy} (protects : ProtectsWithExit origin command community read strategy)
    (choose : Rival) (round : Nat) :
    let earlier := adaptivePlay origin read strategy choose round
    RequiresExit origin command community earlier.position (strategy earlier.position.seen)
      (emitted origin read strategy choose round) ∧
    Quantities.Recorded origin earlier.script ∧ Evolving.Epoch.Current.ClosedAt earlier.position.window.current := by
  rw [adaptive_play_is_the_actual_play_of_its_emitted_inputs]
  exact ⟨protects _ round, play_keeps_the_original_whole_ledger origin read strategy _ round⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
