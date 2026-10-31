import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Independent.FiniteStrategicGame

/-!
# An independently presented asymmetric four-player game

This is a direct consumer of the independent classical kernel.  It has no
process-generated source or recovery imports.  Four players carry strategy
fibres of cardinalities `2, 3, 4, 2`; one distinguished action of player two
produces an observation cutoff, while every other profile produces a world
terminal with a nonconstant rational payoff vector containing both gains and
losses.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Independent
namespace AsymmetricFourPlayerGame

abbrev Player := Fin 4

abbrev playerZero : Player := ⟨0, by decide⟩
abbrev playerOne : Player := ⟨1, by decide⟩
abbrev playerTwo : Player := ⟨2, by decide⟩
abbrev playerThree : Player := ⟨3, by decide⟩

/-- Exact strategy cardinality of each labelled player. -/
def strategyArity (player : Player) : Nat :=
  match player.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | _ => 2

theorem strategyArity_positive (player : Player) :
    0 < strategyArity player := by
  unfold strategyArity
  generalize player.val = value
  cases value with
  | zero => decide
  | succ value =>
      cases value with
      | zero => decide
      | succ value =>
          cases value with
          | zero => decide
          | succ _ => simp

/-- The strategy family is genuinely dependent on the player. -/
abbrev Strategy (player : Player) := Fin (strategyArity player)

abbrev Profile := (player : Player) → Strategy player

theorem strategy_nonempty (player : Player) : Nonempty (Strategy player) :=
  ⟨⟨0, strategyArity_positive player⟩⟩

def playerTwoLast : Strategy playerTwo := ⟨3, by decide⟩

def playerZeroOne : Strategy playerZero := ⟨1, by decide⟩

/-- The all-zero terminal profile. -/
def baseProfile : Profile :=
  fun player => ⟨0, strategyArity_positive player⟩

/-- Player two's last action triggers the finite-observation cutoff. -/
def cutoffProfile : Profile :=
  Function.update baseProfile playerTwo playerTwoLast

/-- A second terminal profile used to witness nonconstant utility. -/
def playerZeroOneProfile : Profile :=
  Function.update baseProfile playerZero playerZeroOne

@[simp] theorem playerZeroOneProfile_at_zero :
    playerZeroOneProfile playerZero = playerZeroOne := by
  simp [playerZeroOneProfile]

@[simp] theorem playerZeroOneProfile_at_one :
    playerZeroOneProfile playerOne = baseProfile playerOne := by
  simp [playerZeroOneProfile]

/-- Nonconstant mixed-sign payoff vector at a world terminal. -/
def payoff (profile : Profile) (player : Player) : ℚ :=
  if player = playerZero then
    if profile playerZero = playerZeroOne then 1 else 0
  else if player = playerOne then
    -3
  else if player = playerTwo then
    5
  else
    -1

/-- `none` is an actual cutoff, not a zero-payoff terminal. -/
def outcome (profile : Profile) : Option (Player → ℚ) :=
  if profile playerTwo = playerTwoLast then
    none
  else
    some (payoff profile)

/-- The independently presented game. -/
def game : FiniteStrategicGame where
  Player := Player
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := Strategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := outcome

theorem baseProfile_playerTwo_ne_last :
    baseProfile playerTwo ≠ playerTwoLast := by
  intro equal
  have impossible : (0 : Nat) = 3 := by
    simpa [baseProfile, playerTwoLast] using congrArg Fin.val equal
  cases impossible

theorem baseProfile_playerZero_ne_one :
    baseProfile playerZero ≠ playerZeroOne := by
  intro equal
  have impossible : (0 : Nat) = 1 := by
    simpa [baseProfile, playerZeroOne] using congrArg Fin.val equal
  cases impossible

/-- Four explicit equivalences expose the exact finite strategy carriers
without importing a cardinality or enumeration oracle. -/
def playerZeroStrategies : game.Strategy playerZero ≃ Fin 2 :=
  Equiv.refl _

def playerOneStrategies : game.Strategy playerOne ≃ Fin 3 :=
  Equiv.refl _

def playerTwoStrategies : game.Strategy playerTwo ≃ Fin 4 :=
  Equiv.refl _

def playerThreeStrategies : game.Strategy playerThree ≃ Fin 2 :=
  Equiv.refl _

/-- The cutoff domain is exactly player two's distinguished last action. -/
theorem outcome_eq_none_iff (profile : game.Profile) :
    game.outcome profile = none ↔
      profile playerTwo = playerTwoLast := by
  simp [game, outcome]

theorem baseProfile_world_terminal :
    game.outcome baseProfile = some (payoff baseProfile) := by
  simp [game, outcome, baseProfile_playerTwo_ne_last]

theorem cutoffProfile_is_cutoff :
    game.outcome cutoffProfile = none := by
  simp [game, outcome, cutoffProfile]

@[simp] theorem payoff_base_playerOne :
    payoff baseProfile playerOne = (-3 : ℚ) := by
  simp [payoff]

@[simp] theorem payoff_base_playerTwo :
    payoff baseProfile playerTwo = (5 : ℚ) := by
  simp [payoff]

@[simp] theorem payoff_base_playerZero :
    payoff baseProfile playerZero = (0 : ℚ) := by
  unfold payoff
  rw [if_pos rfl, if_neg baseProfile_playerZero_ne_one]

@[simp] theorem payoff_playerZeroOne_playerZero :
    payoff playerZeroOneProfile playerZero = (1 : ℚ) := by
  unfold payoff
  rw [if_pos rfl, if_pos playerZeroOneProfile_at_zero]

/-- The same game contains a loss, a gain, and a payoff coordinate that
changes across terminal profiles. -/
theorem mixed_sign_and_nonconstant :
    payoff baseProfile playerOne < 0 ∧
    0 < payoff baseProfile playerTwo ∧
    payoff baseProfile playerZero ≠
      payoff playerZeroOneProfile playerZero := by
  rw [payoff_base_playerOne, payoff_base_playerTwo,
    payoff_base_playerZero, payoff_playerZeroOne_playerZero]
  decide

/-- A payoff alteration which leaves the strategy fibres and cutoff domain
unchanged but changes the anchored terminal observation. -/
def alteredPayoff (profile : Profile) (player : Player) : ℚ :=
  if player = playerZero then 7 else payoff profile player

def alteredOutcome (profile : Profile) : Option (Player → ℚ) :=
  if profile playerTwo = playerTwoLast then
    none
  else
    some (alteredPayoff profile)

def alteredGame : FiniteStrategicGame where
  Player := Player
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := Strategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := alteredOutcome

theorem alteredGame_same_cutoff_domain (profile : Profile) :
    (game.outcome profile).isSome =
      (alteredGame.outcome profile).isSome := by
  simp only [game, alteredGame, outcome, alteredOutcome]
  split <;> rfl

theorem altered_baseProfile_world_terminal :
    alteredGame.outcome baseProfile = some (alteredPayoff baseProfile) := by
  simp [alteredGame, alteredOutcome, baseProfile_playerTwo_ne_last]

@[simp] theorem base_playerZero_utility :
    game.utility baseProfile playerZero = some 0 := by
  unfold FiniteStrategicGame.utility
  rw [baseProfile_world_terminal]
  change some (payoff baseProfile playerZero) = some 0
  rw [payoff_base_playerZero]

@[simp] theorem altered_base_playerZero_utility :
    alteredGame.utility baseProfile playerZero = some 7 := by
  unfold FiniteStrategicGame.utility
  rw [altered_baseProfile_world_terminal]
  change some (alteredPayoff baseProfile playerZero) = some 7
  unfold alteredPayoff
  rw [if_pos rfl]

/-- The observable anchor fixes both a player coordinate and the terminal
profile at which its utility is read. -/
structure PreservesBaseObservable
    (iso : StrategicGameIso game alteredGame) : Prop where
  player_anchor : iso.playerEquiv playerZero = playerZero
  profile_anchor : iso.profileEquiv baseProfile = baseProfile

/-- Changing the anchored payoff cannot be hidden by a strong game
isomorphism, even though the altered game has the identical cutoff domain and
strategy cardinalities. -/
theorem no_strong_iso_preserving_base_observable :
    ¬ ∃ iso : StrategicGameIso game alteredGame,
      PreservesBaseObservable iso := by
  rintro ⟨iso, anchor⟩
  have preserved := iso.utility_preserved baseProfile playerZero
  rw [anchor.profile_anchor, anchor.player_anchor] at preserved
  rw [altered_base_playerZero_utility, base_playerZero_utility] at preserved
  have impossible : (7 : ℚ) = 0 := Option.some.inj preserved
  have distinct : (7 : ℚ) ≠ 0 := by decide
  exact distinct impossible

end AsymmetricFourPlayerGame
end Independent
end Classical
end Society
end ProcessGame
end SaturationMonoid
