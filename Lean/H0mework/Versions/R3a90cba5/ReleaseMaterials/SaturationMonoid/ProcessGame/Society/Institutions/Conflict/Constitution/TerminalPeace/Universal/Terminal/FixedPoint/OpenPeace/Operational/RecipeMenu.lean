import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Recipe

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (people : List Party)

abbrev RecipeMenu := List (RepeatCode input raw)

variable (menu : RecipeMenu input raw)

abbrev RejectedRecipes := (i : Fin menu.length) → RecipeIssue input origin raw people menu[i]

/-- The chosen word is at its actual registered position. Every preceding
position comes with the source's exact rejection. -/
structure SelectedRecipe where
  position : Fin menu.length
  recipe : Recipe input origin people raw (input.law.duration raw)
  word : recipe.move.word = menu[position].production
  earlier : (i : Fin menu.length) → i.val < position.val → RecipeIssue input origin raw people menu[i]

variable [DecidableEq (Request Party Good Port Technology Instrument)]

def chooseRecipe : (menu : RecipeMenu input raw) →
    RejectedRecipes input origin raw people menu ⊕ SelectedRecipe input origin raw people menu
  | [] => .inl (fun i => Fin.elim0 i)
  | head :: tail =>
    match checkRecipe input origin raw people head with
    | .inr selected => .inr ⟨0, selected.val, selected.property, fun i early => (Nat.not_lt_zero i early).elim⟩
    | .inl failed =>
      match chooseRecipe tail with
      | .inl rest => .inl (Fin.cases failed rest)
      | .inr picked =>
        .inr ⟨picked.position.succ, picked.recipe, picked.word,
          Fin.cases (fun _ => failed) (fun i early => picked.earlier i (Nat.lt_of_succ_lt_succ early))⟩

theorem chooseRecipe_finds_an_available_word (i : Fin menu.length)
    (available : RecipeConditions input origin raw people menu[i]) :
    ∃ selected, chooseRecipe input origin raw people menu = .inr selected := by
  cases chooseRecipe input origin raw people menu with
  | inl rejected => exact ((rejected i).refutes _ _ _ _ _ available).elim
  | inr selected => exact ⟨selected, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Recipe

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {people : List Party} {duration lower : ℚ}

/-- The original source clock can demand a smaller uniform increment
than the actual law pays. -/
def atMinimum (recipe : Recipe input origin people raw duration) (positive : 0 < lower)
    (within : lower ≤ duration) : Recipe input origin people raw lower :=
  ⟨recipe.move, ⟨recipe.law.timing, recipe.law.reserve, recipe.law.accumulating, positive,
    fun extra available clock round => within.trans (recipe.law.duration extra available clock round),
    recipe.law.registered⟩, recipe.registration, recipe.positiveGain⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Recipe
