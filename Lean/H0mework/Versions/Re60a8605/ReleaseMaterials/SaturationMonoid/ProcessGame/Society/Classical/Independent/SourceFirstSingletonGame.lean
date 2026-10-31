import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Independent.FiniteStrategicGame

/-!
# Independently presented singleton terminal game

This target is defined without importing any source, recovery, exchange, or
regression module.  Its sole player has one strategy and receives terminal
payoff seven at the unique profile.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Independent
namespace SourceFirstSingletonGame

abbrev Player := Fin 1
abbrev Strategy (_player : Player) := Fin 1
abbrev Profile := (player : Player) → Strategy player

def payoff : Player → ℚ := fun _ => 7

def outcome (_profile : Profile) : Option (Player → ℚ) :=
  some payoff

def game : FiniteStrategicGame where
  Player := Player
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := Strategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := outcome

def uniquePlayer : game.Player := ⟨0, by decide⟩

def uniqueProfile : game.Profile :=
  fun _ => ⟨0, by decide⟩

@[simp] theorem outcome_uniqueProfile :
    game.outcome uniqueProfile = some payoff :=
  rfl

@[simp] theorem utility_uniqueProfile :
    game.utility uniqueProfile uniquePlayer = some 7 :=
  rfl

end SourceFirstSingletonGame
end Independent
end Classical
end Society
end ProcessGame
end SaturationMonoid
