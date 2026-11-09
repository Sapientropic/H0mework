import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace.Operational (RecipeMenu RejectedRecipes SelectedRecipe RecipeConditions chooseRecipe)
open FixedPoint.OpenPeace.Operational.Repair (candidates)
open private postRecipe retainDue from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase

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
local notation "Refusals" => RejectedRecipes InputAt origin RawAt people menu
local notation "Edits" => candidates InputAt origin RawAt people menu Incumbent
local notation "FitsClock" => quantum ≤ before.current.programme.law.duration before.current.physical.raw
local notation "Selected" => Operational.Repair.select InputAt origin RawAt people menu Incumbent

structure JointRebased (basis : Fin menu.length) (width : Nat) where
  plan : Operational.Joint.Plan InputAt origin RawAt people menu Incumbent menu[basis] width
  actual : Rebased before (Operational.Joint.codes InputAt origin RawAt people menu Incumbent
    menu[basis] width plan.personal)
  choice : actual.chosen = plan.selected

inductive RefreshDecision
  | retained (paid : RetainedDue before menu home replies)
  | registered (paid : Rebased before menu)
  | generated (refusals : Refusals) (paid : Rebased before (Edits refusals))
  | joint (refusals : Refusals) (edits : RejectedRecipes InputAt origin RawAt people (Edits refusals))
      (basis : Fin menu.length) (width : Nat)
      (earlier : ∀ n < width, Operational.Joint.Obstruction InputAt origin RawAt people menu Incumbent menu[basis] n)
      (paid : JointRebased before menu basis width)

/-- This is the material selection evidence. It lives at the existing
read universe and carries no resident or independent writing power. -/
inductive RefreshEvidence : Type
  | repaired (refusals : Refusals) (chosen : SelectedRecipe InputAt origin RawAt people (Edits refusals))
  | joint (refusals : Refusals) (edits : RejectedRecipes InputAt origin RawAt people (Edits refusals))
      (basis : Fin menu.length) (width : Nat)
      (earlier : ∀ n < width, Operational.Joint.Obstruction InputAt origin RawAt people menu Incumbent menu[basis] n)
      (plan : Operational.Joint.Plan InputAt origin RawAt people menu Incumbent menu[basis] width)

variable {before menu home replies} in
def RefreshDecision.evidence : RefreshDecision before menu home replies → Option (RefreshEvidence before menu)
  | .retained _ | .registered _ => none
  | .generated each paid => some (.repaired each paid.chosen)
  | .joint each edits basis width earlier paid => some (.joint each edits basis width earlier paid.plan)

private def reconsider (limit : Nat) (within : FitsClock) (each : Refusals)
    (edits : RejectedRecipes InputAt origin RawAt people (Edits each)) : RefreshDecision before menu home replies :=
  if listed : 0 < menu.length then
    let basis : Fin menu.length := ⟨0, listed⟩
    match Operational.Joint.search InputAt origin RawAt people menu Incumbent menu[basis] limit with
    | .pending tested => .retained (retainDue before menu home replies (.searching each edits basis limit tested))
    | .found width _ earlier plan =>
      .joint each edits basis width earlier ⟨plan, postRecipe before _ plan.selected within, rfl⟩
  else .retained (retainDue before menu home replies (.exhausted each edits))

/-- A repair is consumed by the same physical and whole-ledger writer as
a registered replacement. Exhaustion still pays the incumbent due round
and writes both sets of named refusals on its actual successor. -/
def chooseRefreshAt (limit : Nat) : RefreshDecision before menu home replies :=
  if within : FitsClock then
    match Selected with
    | .registered picked => .registered (postRecipe before menu picked within)
    | .generated refused picked => .generated refused (postRecipe before (Edits refused) picked within)
    | .exhausted refused edits => reconsider before menu home replies limit within refused edits
  else .retained (retainDue before menu home replies (.slow (lt_of_not_ge within)))

/-- The frontier widens with the reached physical ordinal. Its cutoff
limits this inspection, never the language of lawful production. -/
def refreshWidth : Nat :=
  before.current.physical.raw.round + before.current.recipe.move.word.length

def chooseRefresh : RefreshDecision before menu home replies :=
  chooseRefreshAt before menu home replies (refreshWidth before)

theorem chooseRefresh_keeps_the_registered_priority {paid : Rebased before menu}
    (registered : chooseReplacement before menu home replies = .inr paid) :
    chooseRefresh before menu home replies = .registered paid := by
  unfold chooseReplacement at registered
  split at registered
  · rename_i within
    cases picked : chooseRecipe InputAt origin RawAt people menu with
    | inl refused =>
      rw [picked] at registered
      cases registered
    | inr selected =>
      rw [picked] at registered
      cases registered
      simp only [chooseRefresh, chooseRefreshAt, dif_pos within, Operational.Repair.select, picked]
  · cases registered

theorem chooseRefresh_first_writes_the_generated_choice
    (clock : FitsClock) (each : Refusals)
    (picked : SelectedRecipe InputAt origin RawAt people (Edits each))
    (generated : Selected = .generated each picked) :
    ∃ paid : Rebased before (Edits each),
      chooseRefresh before menu home replies = .generated each paid ∧ paid.chosen = picked :=
  ⟨postRecipe before (Edits each) picked clock, by simp only [chooseRefresh, chooseRefreshAt, dif_pos clock, generated], rfl⟩

theorem chooseRefresh_keeps_the_due_when_the_catalogue_is_empty
    (clock : FitsClock) (each : Refusals)
    (failed : RejectedRecipes InputAt origin RawAt people (Edits each))
    (exhausted : Selected = .exhausted each failed) (empty : ¬ 0 < menu.length) :
    ∃ paid : RetainedDue before menu home replies,
      chooseRefresh before menu home replies = .retained paid ∧
        paid.diagnostic.read = .exhausted each failed :=
  ⟨retainDue before menu home replies (.exhausted each failed),
    by simp only [chooseRefresh, chooseRefreshAt, dif_pos clock, exhausted, reconsider, dif_neg empty], rfl⟩

theorem chooseRefreshAt_keeps_the_due_and_every_tested_width
    (limit : Nat) (clock : FitsClock) (each : Refusals)
    (failed : RejectedRecipes InputAt origin RawAt people (Edits each))
    (exhausted : Selected = .exhausted each failed) (listed : 0 < menu.length)
    (tested : ∀ width ≤ limit,
      Operational.Joint.Obstruction InputAt origin RawAt people menu Incumbent
        menu[(⟨0, listed⟩ : Fin menu.length)] width)
    (pending : Operational.Joint.search InputAt origin RawAt people menu Incumbent
      menu[(⟨0, listed⟩ : Fin menu.length)] limit =
      .pending tested) :
    ∃ paid : RetainedDue before menu home replies,
      chooseRefreshAt before menu home replies limit = .retained paid ∧
        paid.diagnostic.read = .searching each failed ⟨0, listed⟩ limit tested :=
  ⟨retainDue before menu home replies (.searching each failed ⟨0, listed⟩ limit tested),
    by simp only [chooseRefreshAt, dif_pos clock, exhausted, reconsider, dif_pos listed, pending], rfl⟩

theorem chooseRefresh_posts_the_first_joint_choice
    (clock : FitsClock) (each : Refusals)
    (failed : RejectedRecipes InputAt origin RawAt people (Edits each))
    (exhausted : Selected = .exhausted each failed) (listed : 0 < menu.length)
    (width : Nat) (inside : width ≤ refreshWidth before)
    (earlier : ∀ n < width, Operational.Joint.Obstruction InputAt origin RawAt people menu Incumbent
      menu[(⟨0, listed⟩ : Fin menu.length)] n)
    (plan : Operational.Joint.Plan InputAt origin RawAt people menu Incumbent
      menu[(⟨0, listed⟩ : Fin menu.length)] width)
    (found : Operational.Joint.search InputAt origin RawAt people menu Incumbent
      menu[(⟨0, listed⟩ : Fin menu.length)] (refreshWidth before) = .found width inside earlier plan) :
    chooseRefresh before menu home replies = .joint each failed ⟨0, listed⟩ width earlier
      ⟨plan, postRecipe before _ plan.selected clock, rfl⟩ := by
  simp only [chooseRefresh, chooseRefreshAt, dif_pos clock, exhausted, reconsider, dif_pos listed, found]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
