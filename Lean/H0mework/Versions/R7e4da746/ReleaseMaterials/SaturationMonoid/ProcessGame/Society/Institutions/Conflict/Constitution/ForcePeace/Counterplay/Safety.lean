import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Interleave
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Exit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.NativeShortage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (ExitAtCut NativeShortage RoundFailure Script StepFailure StepGood Window
  inspectNativeShortage inspectRound inspectStep)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "Word" => Script Party Good Port Technology Instrument

/-- Both submission and the available independent exit use the same
civilian observation history. The exit remains an option at the cut. -/
structure CivilPlan (Party Good Port Technology Instrument : Type) (CivilView : Type u) where
  submit : List CivilView → Reparation.Actual.Input Party Good Port Technology Instrument
  exit : List CivilView → Script Party Good Port Technology Instrument

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

abbrev prefixAt (tick : Nat) : Word :=
  game.past ++ game.scriptAt plan.submit opponent arbitrate tick

abbrev exitAt (tick : Nat) : Word :=
  plan.exit (game.play plan.submit opponent arbitrate tick).civilSeen

abbrev stepGoodAt (tick : Nat) : Prop :=
  StepGood game.seed game.command game.community (game.turnAt plan.submit opponent arbitrate tick).isCivil
    (game.play plan.submit opponent arbitrate tick).window (game.inputAt plan.submit opponent arbitrate tick)

abbrev exitGoodAt (tick : Nat) : Prop :=
  ExitAtCut game.seed game.command game.community (game.currentAt plan.submit opponent arbitrate tick)
    (game.exitAt plan opponent arbitrate tick)

def SafeAt (tick : Nat) : Prop :=
  game.stepGoodAt plan opponent arbitrate tick ∧ game.exitGoodAt plan opponent arbitrate tick

def Safe : Prop := ∀ tick, game.SafeAt plan opponent arbitrate tick

/-- A due-service failure belongs to the actual next input. An unpayable
exit belongs to the actual cut and leaves its proposed exit unexecuted. -/
inductive Issue (tick : Nat) where
  | actual (issue : StepFailure game.seed game.command game.community
      (game.turnAt plan.submit opponent arbitrate tick).isCivil
      (game.play plan.submit opponent arbitrate tick).window (game.inputAt plan.submit opponent arbitrate tick))
  | exit (checked : game.stepGoodAt plan opponent arbitrate tick)
      (issue : RoundFailure game.seed game.command game.community
        (Window.at (game.currentAt plan.submit opponent arbitrate tick)) (game.exitAt plan opponent arbitrate tick) [])

theorem Issue.refutes {tick : Nat} (issue : game.Issue plan opponent arbitrate tick) :
    ¬ game.SafeAt plan opponent arbitrate tick := by
  intro safe
  cases issue with
  | actual failure => exact failure.refutes safe.1
  | exit _ failure => exact failure.refutes safe.2

def inspectTick (tick : Nat) :
    game.Issue plan opponent arbitrate tick ⊕ PLift (game.SafeAt plan opponent arbitrate tick) :=
  let prior := game.play plan.submit opponent arbitrate tick
  match inspectStep game.seed game.command game.community (game.turnAt plan.submit opponent arbitrate tick).isCivil
    prior.window (game.inputAt plan.submit opponent arbitrate tick) with
  | .inl issue => .inl (.actual issue)
  | .inr step =>
    match inspectRound game.seed game.command game.community (Window.at prior.window.current)
      (game.exitAt plan opponent arbitrate tick) [] with
    | .inl issue => .inl (.exit step.down issue)
    | .inr exit => .inr ⟨⟨step.down, exit.down⟩⟩

structure FirstDefeat where
  tick : Nat
  earlier : ∀ earlier < tick, game.SafeAt plan opponent arbitrate earlier
  issue : game.Issue plan opponent arbitrate tick

def firstDefeat (failed : ¬ game.Safe plan opponent arbitrate) : game.FirstDefeat plan opponent arbitrate := by
  classical
  have occurs : ∃ tick, ¬ game.SafeAt plan opponent arbitrate tick := by
    by_contra none
    exact failed (fun tick => Classical.byContradiction (fun bad => none ⟨tick, bad⟩))
  let tick := Nat.find occurs
  have bad := Nat.find_spec occurs
  have earlier : ∀ earlier < tick, game.SafeAt plan opponent arbitrate earlier := by
    intro n before
    exact Classical.byContradiction (Nat.find_min occurs before)
  cases game.inspectTick plan opponent arbitrate tick with
  | inl issue => exact ⟨tick, earlier, issue⟩
  | inr checked => exact (bad checked.down).elim

theorem safe_iff_no_first_defeat :
    game.Safe plan opponent arbitrate ↔ ¬ Nonempty (game.FirstDefeat plan opponent arbitrate) := by
  constructor
  · rintro safe ⟨failed⟩
    exact failed.issue.refutes game plan opponent arbitrate (safe failed.tick)
  · intro none
    exact Classical.byContradiction (fun bad => none ⟨game.firstDefeat plan opponent arbitrate bad⟩)

abbrev nativeShortageAt (tick : Nat) :
    Option (NativeShortage (game.currentAt plan.submit opponent arbitrate tick)
      (game.inputAt plan.submit opponent arbitrate tick)) :=
  inspectNativeShortage (game.currentAt plan.submit opponent arbitrate tick)
    (game.inputAt plan.submit opponent arbitrate tick)

omit [DecidableEq Community] in
/-- Even when a shortage stalls the clock before a due-service failure,
the exact original cell, deficit, retained input and whole successor exist. -/
theorem a_named_native_shortage_is_recorded_on_the_actual_next_visit (tick : Nat)
    (shortage : NativeShortage (game.currentAt plan.submit opponent arbitrate tick)
      (game.inputAt plan.submit opponent arbitrate tick)) :
    0 < shortage.amount ∧
      (game.currentAt plan.submit opponent arbitrate (tick + 1)).raw =
        (game.currentAt plan.submit opponent arbitrate tick).raw ∧
      Quantities.Recorded game.seed (game.prefixAt plan opponent arbitrate (tick + 1)) := by
  refine ⟨shortage.positive, ?_, game.every_interleaving_prefix_is_recorded plan.submit opponent arbitrate (tick + 1)⟩
  change (((game.play plan.submit opponent arbitrate tick).window.write
    (game.inputAt plan.submit opponent arbitrate tick)).current).raw = _
  rw [Window.write_current]
  exact shortage.rejected_tick_keeps_its_material_and_original_deferred_input.1

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
