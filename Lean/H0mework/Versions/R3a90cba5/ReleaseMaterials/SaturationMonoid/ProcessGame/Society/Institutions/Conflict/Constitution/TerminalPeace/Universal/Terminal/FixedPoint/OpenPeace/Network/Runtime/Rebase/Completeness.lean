import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.PublicWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Operational (RecipeMenu RepeatCode RejectedRecipes RecipeConditions)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (before : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase))
  (menu : RecipeMenu before.current.programme before.current.physical.raw)
  (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)

local notation "InputAt" => before.current.programme
local notation "RawAt" => before.current.physical.raw
local notation "Incumbent" => before.current.recipe.move.word
local notation "Limit" => refreshWidth before
local notation "OldRejects" => RejectedRecipes InputAt origin RawAt people menu
local notation "Edits" => Operational.Repair.candidates InputAt origin RawAt people menu Incumbent
local notation "Chosen" => Operational.Repair.select InputAt origin RawAt people menu Incumbent

/-- Full feasibility in the reached source's checked domain forces the
first write, even when no original or single-edit recipe could pay. -/
theorem available_joint_production_forces_the_first_write
    (clock : quantum ≤ before.current.programme.law.duration before.current.physical.raw)
    (each : OldRejects) (failed : RejectedRecipes InputAt origin RawAt people (Edits each))
    (exhausted : Chosen = .exhausted each failed) (listed : 0 < menu.length)
    (other : RepeatCode InputAt RawAt) (fresh : Operational.Repair.Fresh InputAt RawAt menu Incumbent other.production)
    (within : Operational.Joint.Within InputAt RawAt people Limit other)
    (paid : RecipeConditions InputAt origin RawAt people other) :
    let basis : Fin menu.length := ⟨0, listed⟩
    ∃ (width : Nat) (earlier : ∀ n < width, Operational.Joint.Obstruction InputAt origin RawAt people menu
        Incumbent menu[basis] n) (generated : JointRebased before menu basis width),
      chooseRefresh before menu home replies = .joint each failed basis width earlier generated ∧
      width ≤ Operational.Joint.widthOf InputAt RawAt people other := by
  let basis : Fin menu.length := ⟨0, listed⟩
  change ∃ width, ∃ earlier, ∃ generated : JointRebased before menu basis width,
    chooseRefresh before menu home replies = .joint each failed basis width earlier generated ∧ _
  let result := Operational.Joint.search InputAt origin RawAt people menu Incumbent menu[basis] Limit
  cases checked : result with
  | pending all =>
    exact ((all Limit le_rfl).excludes _ _ _ _ _ _ _ _ other fresh within paid).elim
  | found width inside earlier plan =>
    have lower : width ≤ Operational.Joint.widthOf InputAt RawAt people other := by
      by_contra! tooLate
      exact ((earlier _ tooLate).excludes _ _ _ _ _ _ _ _ other fresh
        (Operational.Joint.within_widthOf _ _ _ _) paid)
    exact ⟨width, earlier, _, chooseRefresh_posts_the_first_joint_choice before menu home replies
      clock each failed exhausted listed width inside earlier plan checked, lower⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
