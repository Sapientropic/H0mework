import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Pos" => Position Party Good Port Technology Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

def LocalMenusNonempty (allowed : Pos → Turn → Input → Prop) (family : Pos → Prop) (plan : Plan) : Prop :=
  ∀ position, family position → ∃ visit : Turn × Input,
    allowed position visit.1 (proposal position (fun _ => plan.submit position.civilSeen) (fun _ => visit.2) visit.1)

structure AllowedReplay (allowed : Pos → Turn → Input → Prop) (plan : Plan) where
  opponent : List OpponentView → Input
  arbitrate : Nat → C → Turn
  legal : ∀ tick, game.AllowsBefore allowed plan opponent arbitrate tick

/-- Nonempty local menus generate an original infinite play. The opposing
reply is selected by the length of its observed history. Every selected
input is dispatched on the position written by the preceding visit. -/
def compileFamilyReplay (allowed : Pos → Turn → Input → Prop) (family : Pos → Prop) (plan : Plan)
    (initial : family game.start)
    (closed : ∀ position, family position → ∀ lane reply,
      let input := proposal position (fun _ => plan.submit position.civilSeen) (fun _ => reply) lane
      allowed position lane input → family (game.extend position input))
    (live : LocalMenusNonempty allowed family plan) : game.AllowedReplay allowed plan := by
  let available := { position : Pos // family position }
  let chooseVisit (position : available) : Turn × Input := Classical.choose (live position.val position.property)
  let selected (position : available) : Input :=
    proposal position.val (fun _ => plan.submit position.val.civilSeen)
      (fun _ => (chooseVisit position).2) (chooseVisit position).1
  have isAllowed (position : available) : allowed position.val (chooseVisit position).1 (selected position) :=
    Classical.choose_spec (live position.val position.property)
  let advance (position : available) : available :=
    ⟨game.extend position.val (selected position),
      closed position.val position.property (chooseVisit position).1 (chooseVisit position).2 (isAllowed position)⟩
  let reached : Nat → available := Nat.rec ⟨game.start, initial⟩ (fun _ position => advance position)
  let opponent (seen : List OpponentView) : Input := (chooseVisit (reached (seen.length - 1))).2
  let arbitrate (tick : Nat) (_ : C) : Turn := (chooseVisit (reached tick)).1
  have replyAt (tick : Nat) :
      opponent (game.play plan.submit opponent arbitrate tick).opponentSeen = (chooseVisit (reached tick)).2 := by
    unfold opponent
    rw [game.opponent_history_length plan opponent arbitrate tick]
  have inputAt (tick : Nat) (same : game.play plan.submit opponent arbitrate tick = (reached tick).val) :
      game.inputAt plan.submit opponent arbitrate tick = selected (reached tick) := by
    let actual := game.play plan.submit opponent arbitrate tick
    let lane := (chooseVisit (reached tick)).1
    change proposal actual plan.submit opponent lane =
      proposal (reached tick).val (fun _ => plan.submit (reached tick).val.civilSeen)
        (fun _ => (chooseVisit (reached tick)).2) lane
    rw [← same]
    cases lane with
    | civil => rfl
    | opponent => exact replyAt tick
    | retained => rfl
  have replays (tick : Nat) : game.play plan.submit opponent arbitrate tick = (reached tick).val := by
    induction tick with
    | zero => rfl
    | succ tick earlier =>
      change game.extend (game.play plan.submit opponent arbitrate tick) (game.inputAt plan.submit opponent arbitrate tick) =
        game.extend (reached tick).val (selected (reached tick))
      rw [inputAt tick earlier, earlier]
  refine ⟨opponent, arbitrate, fun _ tick _ => ?_⟩
  change allowed (game.play plan.submit opponent arbitrate tick) (chooseVisit (reached tick)).1
    (game.inputAt plan.submit opponent arbitrate tick)
  rw [inputAt tick (replays tick), replays tick]
  exact isAllowed (reached tick)

def compileAllowedReplay (civilChoice : List CivilView → Input → Prop)
    (allowed : Pos → Turn → Input → Prop) (family : Pos → Prop)
    (initial : family game.start) (closed : game.FibreCloses civilChoice allowed family)
    (live : LocalMenusNonempty allowed family (game.compileFibre civilChoice allowed family closed)) :
    game.AllowedReplay allowed (game.compileFibre civilChoice allowed family closed) :=
  game.compileFamilyReplay allowed family (game.compileFibre civilChoice allowed family closed) initial
    (fun position inside lane reply permitted =>
      (((Classical.choose_spec (closed position.civilSeen)).2 position inside rfl).2 lane reply permitted).2) live

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
