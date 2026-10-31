import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs

/-!
# Independent finite rational strategic games

This file defines the classical target carrier used by process-generated
classical recovery.  It is deliberately independent of every Society source,
recovery, and regression module: a target game is presented on its own terms,
so an eventual essential-surjectivity theorem cannot obtain its conclusion by
definitionally reusing a generated image.

The outcome distinguishes a finite observation cutoff (`none`) from a world
terminal carrying every player's rational payoff (`some payoffs`).  Utilities
are derived coordinate readouts; they are not a second caller-supplied table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Independent

universe u v w x y z

-- The structure sort necessarily joins these universes with `max`; the two
-- fields remain intentionally independent in every public theorem.
set_option linter.checkUnivs false in
/-- An arbitrary finite rational strategic game.

The player carrier and every strategy fibre may be empty.  Thus the carrier
covers every finite dependent strategy family, including games with players
but no global pure profile. -/
structure FiniteStrategicGame where
  Player : Type u
  playerFintype : Fintype Player
  playerDecidableEq : DecidableEq Player
  Strategy : Player → Type v
  strategyFintype : (player : Player) → Fintype (Strategy player)
  strategyDecidableEq : (player : Player) → DecidableEq (Strategy player)
  outcome : ((player : Player) → Strategy player) → Option (Player → ℚ)

attribute [instance] FiniteStrategicGame.playerFintype
attribute [instance] FiniteStrategicGame.playerDecidableEq
attribute [instance] FiniteStrategicGame.strategyFintype
attribute [instance] FiniteStrategicGame.strategyDecidableEq

namespace FiniteStrategicGame

/-- The dependent product of the strategy fibres. -/
abbrev Profile (game : FiniteStrategicGame.{u, v}) :=
  (player : game.Player) → game.Strategy player

/-- A terminal payoff vector indexed by the game's own player carrier. -/
abbrev PayoffVector (game : FiniteStrategicGame.{u, v}) :=
  game.Player → ℚ

/-- Player utility is the coordinate readout of the optional world outcome.
It is absent exactly when the world outcome is absent. -/
def utility (game : FiniteStrategicGame.{u, v})
    (profile : game.Profile) (player : game.Player) : Option ℚ :=
  (game.outcome profile).map fun payoffs => payoffs player

@[simp] theorem utility_eq_none_iff
    (game : FiniteStrategicGame.{u, v})
    (profile : game.Profile) (player : game.Player) :
    game.utility profile player = none ↔ game.outcome profile = none := by
  cases result : game.outcome profile <;> simp [utility, result]

@[simp] theorem utility_eq_some_iff
    (game : FiniteStrategicGame.{u, v})
    (profile : game.Profile) (player : game.Player) (value : ℚ) :
    game.utility profile player = some value ↔
      ∃ payoffs, game.outcome profile = some payoffs ∧ payoffs player = value := by
  cases result : game.outcome profile with
  | none => simp [utility, result]
  | some payoffs => simp [utility, result]

end FiniteStrategicGame

/-- Reindex a payoff vector along a player equivalence. -/
def reindexPayoff {α : Type u} {β : Type v}
    (equiv : α ≃ β) (payoffs : α → ℚ) : β → ℚ :=
  fun player => payoffs (equiv.symm player)

/-- Strong isomorphism of finite rational strategic games.

Besides player and fibrewise strategy equivalences, the whole dependent
profile equivalence must commute at every coordinate.  Both the optional world
outcome and its derived utility coordinates are preserved. -/
structure StrategicGameIso
    (left : FiniteStrategicGame.{u, v})
    (right : FiniteStrategicGame.{w, x}) where
  playerEquiv : left.Player ≃ right.Player
  strategyEquiv :
    (player : left.Player) →
      left.Strategy player ≃ right.Strategy (playerEquiv player)
  profileEquiv : left.Profile ≃ right.Profile
  profile_strategy_commutes :
    ∀ (profile : left.Profile) (player : left.Player),
      profileEquiv profile (playerEquiv player) =
        strategyEquiv player (profile player)
  outcome_preserved :
    ∀ profile : left.Profile,
      right.outcome (profileEquiv profile) =
        (left.outcome profile).map (reindexPayoff playerEquiv)

namespace StrategicGameIso

/-- Outcome preservation forces preservation of every derived utility
coordinate; there is no second utility-table or utility-proof input. -/
theorem utility_preserved
    {left : FiniteStrategicGame.{u, v}}
    {right : FiniteStrategicGame.{w, x}}
    (iso : StrategicGameIso left right)
    (profile : left.Profile) (player : left.Player) :
    right.utility (iso.profileEquiv profile) (iso.playerEquiv player) =
      left.utility profile player := by
  unfold FiniteStrategicGame.utility
  rw [iso.outcome_preserved profile]
  cases result : left.outcome profile with
  | none => simp
  | some payoffs => simp [reindexPayoff]

private theorem dependentApply_eq_cast
    {α : Type u} {family : α → Type v} (valueAt : (index : α) → family index)
    {source target : α} (equal : source = target) :
    valueAt target = cast (congrArg family equal) (valueAt source) := by
  cases equal
  rfl

/-- The inverse fibre equivalence at a target player.  The cast is forced by
the dependent strategy family and is determined solely by `playerEquiv`. -/
def inverseStrategyEquiv
    {left : FiniteStrategicGame.{u, v}}
    {right : FiniteStrategicGame.{w, x}}
    (iso : StrategicGameIso left right) (player : right.Player) :
    right.Strategy player ≃ left.Strategy (iso.playerEquiv.symm player) :=
  (Equiv.cast (congrArg right.Strategy
      (iso.playerEquiv.apply_symm_apply player).symm)).trans
    (iso.strategyEquiv (iso.playerEquiv.symm player)).symm

/-- Identity isomorphism of an independently presented game. -/
protected def refl
    (game : FiniteStrategicGame.{u, v}) :
    StrategicGameIso game game where
  playerEquiv := Equiv.refl _
  strategyEquiv := fun _ => Equiv.refl _
  profileEquiv := Equiv.refl _
  profile_strategy_commutes := by
    intro profile player
    rfl
  outcome_preserved := by
    intro profile
    cases result : game.outcome profile with
    | none => simp [result]
    | some payoffs =>
        change game.outcome profile = some (reindexPayoff (Equiv.refl _) payoffs)
        rw [result]
        congr 1

/-- Symmetry of strong strategic-game isomorphism. -/
protected def symm
    {left : FiniteStrategicGame.{u, v}}
    {right : FiniteStrategicGame.{w, x}}
    (iso : StrategicGameIso left right) : StrategicGameIso right left where
  playerEquiv := iso.playerEquiv.symm
  strategyEquiv := iso.inverseStrategyEquiv
  profileEquiv := iso.profileEquiv.symm
  profile_strategy_commutes := by
    intro profile player
    apply (iso.strategyEquiv (iso.playerEquiv.symm player)).injective
    rw [← iso.profile_strategy_commutes
      (iso.profileEquiv.symm profile) (iso.playerEquiv.symm player)]
    simpa [inverseStrategyEquiv] using
      (dependentApply_eq_cast profile
        (iso.playerEquiv.apply_symm_apply player).symm)
  outcome_preserved := by
    intro profile
    have forward := iso.outcome_preserved (iso.profileEquiv.symm profile)
    rw [iso.profileEquiv.apply_symm_apply] at forward
    rw [forward]
    cases result : left.outcome (iso.profileEquiv.symm profile) with
    | none => simp
    | some payoffs =>
        simp only [Option.map_some, Option.some.injEq]
        funext player
        simp [reindexPayoff]

/-- Composition of strong strategic-game isomorphisms. -/
protected def trans
    {left : FiniteStrategicGame.{u, v}}
    {middle : FiniteStrategicGame.{w, x}}
    {right : FiniteStrategicGame.{y, z}}
    (first : StrategicGameIso left middle)
    (second : StrategicGameIso middle right) :
    StrategicGameIso left right where
  playerEquiv := first.playerEquiv.trans second.playerEquiv
  strategyEquiv := fun player =>
    (first.strategyEquiv player).trans
      (second.strategyEquiv (first.playerEquiv player))
  profileEquiv := first.profileEquiv.trans second.profileEquiv
  profile_strategy_commutes := by
    intro profile player
    change
      second.profileEquiv (first.profileEquiv profile)
          (second.playerEquiv (first.playerEquiv player)) = _
    rw [second.profile_strategy_commutes, first.profile_strategy_commutes]
    rfl
  outcome_preserved := by
    intro profile
    change
      right.outcome (second.profileEquiv (first.profileEquiv profile)) =
        (left.outcome profile).map
          (reindexPayoff (first.playerEquiv.trans second.playerEquiv))
    rw [second.outcome_preserved, first.outcome_preserved]
    cases result : left.outcome profile with
    | none => rfl
    | some payoffs =>
        simp only [Option.map_some, Option.some.injEq]
        funext player
        simp [reindexPayoff]

end StrategicGameIso

end Independent
end Classical
end Society
end ProcessGame
end SaturationMonoid
