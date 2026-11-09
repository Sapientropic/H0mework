import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.ReadHistory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint.Search

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint (Recipe InReserve)
open TerminalPeace.Universal.Runtime.Viability (Move)
open FixedPoint.OpenPeace.Operational (RecipeMenu SelectedRecipe RejectedRecipes chooseRecipe chooseRecipe_finds_an_available_word)
open FixedPoint.OpenPeace.Operational.Repair (candidates)
open NoFreeProbe
open private Runtime.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
open private OpenPeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch
open private publishOn publishedRead from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.ReadHistory

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (before : Runtime.State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := reserveBase))

local notation "St" => Runtime.State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := reserveBase)
local notation "Raw" => Capitalism.Universal.Abolition.Root.Actual.Current.raw (FixedPoint.Current.physical (Runtime.State.current before))
local notation "Now" => Runtime.State.current before
local notation "NewState" => Runtime.State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := Raw)

private def rebaseRecipe (recipe : Recipe (Now).programme origin people Raw quantum) :
    FixedPoint.Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := Raw) :=
  ⟨(Now).ledger, (Now).physical, (Now).programme, recipe, ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩

variable (menu : RecipeMenu before.current.programme before.current.physical.raw)

local notation "Incumbent" => Move.word (Recipe.move (FixedPoint.Current.recipe Now))
local notation "Edits" => candidates (FixedPoint.Current.programme Now) origin Raw people menu Incumbent

structure Rebased where
  chosen : SelectedRecipe (Now).programme origin Raw people menu
  within : quantum ≤ (Now).programme.law.duration Raw
  actual : FixedPoint.Round (rebaseRecipe before (chosen.recipe.atMinimum (Now).recipe.law.positive within))
  firstWrite : actual = FixedPoint.productiveRound
    (rebaseRecipe before (chosen.recipe.atMinimum (Now).recipe.law.positive within)) .renew .renewed
    (Now).programme (chosen.recipe.atMinimum (Now).recipe.law.positive within)
  next : NewState
  actualNext : next.current = actual.next
  programme : next.current.programme = before.current.programme
  language : next.base.language = before.base.language
  guard : next.base.adaptive.covered = before.base.adaptive.covered
  reads : ReadPath (Now).ledger.resident next.current.ledger.resident
  keepsLanes : next.lanes = before.lanes.map reads.carry

private def postRecipe (chosen : SelectedRecipe (Now).programme origin Raw people menu)
    (within : quantum ≤ (Now).programme.law.duration Raw) : Rebased before menu := by
  let recipe := chosen.recipe.atMinimum (Now).recipe.law.positive within
  let atSource := rebaseRecipe before recipe
  let actual := FixedPoint.productiveRound atSource .renew .renewed atSource.programme recipe
  let readPath := roundReads actual
  have sameWorld : actual.next.ledger.world = (Now).ledger.world :=
    (congrArg AnyAuthoritativeRootCurrent.N actual.wholeNext).symm
  let next := Runtime.State.mk
    (OpenPeace.State.mk (AdaptivePeace.State.mk actual.next before.base.adaptive.amendment) before.base.expansion)
    (before.lanes.map readPath.carry) (sameWorld.symm ▸ before.u7)
  exact ⟨chosen, within, actual, rfl, next, rfl, rfl, rfl, rfl, readPath, rfl⟩

theorem Rebased.writes_its_chosen_word (paid : Rebased before menu) :
    paid.actual.visit.read.commands = paid.chosen.recipe.move.word ∧
      paid.next.current.recipe.move.word = paid.chosen.recipe.move.word ∧
      paid.next.current.physical.raw = (Now).programme.law.next Raw paid.chosen.recipe.move.word := by
  let recipe := paid.chosen.recipe.atMinimum (Now).recipe.law.positive paid.within
  let source := rebaseRecipe before recipe
  have word := recipe.moveAt_word source.physical.raw source.reserved
  obtain ⟨_, material, _, commands⟩ :=
    FixedPoint.productiveRound_reads_selected_production source .renew .renewed source.programme recipe
  rw [paid.actualNext, paid.firstWrite]
  exact ⟨commands.trans word, rfl,
    material.trans (congrArg (fun cmds => (Now).programme.law.next Raw cmds) word)⟩

variable [DecidableEq (Request Party Good Port Technology Instrument)]

inductive RebaseIssue
  | slow (missing : (Now).programme.law.duration Raw < quantum)
  | rejected (each : RejectedRecipes (Now).programme origin Raw people menu)
  | exhausted (each : RejectedRecipes (Now).programme origin Raw people menu)
      (edits : RejectedRecipes (Now).programme origin Raw people (Edits each))
  | searching (each : RejectedRecipes (Now).programme origin Raw people menu)
      (edits : RejectedRecipes (Now).programme origin Raw people (Edits each))
      (basis : Fin menu.length) (limit : Nat)
      (tested : ∀ width ≤ limit,
        Operational.Joint.Obstruction (Now).programme origin Raw people menu Incumbent menu[basis] width)

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)

private def dueInput : OpenPeace.Input Party Good Port Technology Instrument := .native ⟨none, []⟩

local notation "Due" => Runtime.advance home replies before (dueInput (Party := Party) (Good := Good)
  (Port := Port) (Technology := Technology) (Instrument := Instrument))

structure RetainedDue where
  issue : RebaseIssue before menu
  next : St
  diagnostic : ReadOn next.current.ledger.resident (RebaseIssue before menu)
  exactIssue : diagnostic.read = issue
  samePhysical : next.current.physical = (Due).next.current.physical
  sameStack : HEq next.current.ledger.stack (Due).next.current.ledger.stack
  rows : next.current.ledger.stack.balances = (Due).next.current.ledger.stack.balances
  programme : next.current.programme = (Due).next.current.programme
  language : next.base.language = (Due).next.base.language
  recipeWord : next.current.recipe.move.word = (Due).next.current.recipe.move.word
  reads : ReadPath (Now).ledger.resident next.current.ledger.resident
  tariff : next.lanes.tariff.read = before.lanes.tariff.read
  payment : next.lanes.payment.read = before.lanes.payment.read
  openPayment : next.lanes.openPayment.read = before.lanes.openPayment.read
  canonical : (⟨(Due).next.current.ledger.world,
    (Installation.Live.action (Due).next.current.ledger issue true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = next.current.ledger.resident.erase

private def retainDue (issue : RebaseIssue before menu) : RetainedDue before menu home replies := by
  let prior := (Due).next.current.ledger
  let first := stepReads home replies before (dueInput (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  let later := ReadPath.write prior.ready issue true
  have signed := next_keeps_original_signatures home replies before
    (dueInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  exact ⟨issue, publishOn (Due).next issue, publishedRead (Due).next issue, rfl, rfl, HEq.rfl, rfl, rfl, rfl, rfl,
    first.trans later, (later.keeps (Due).next.lanes.tariff).trans signed.1,
    (later.keeps (Due).next.lanes.payment).trans signed.2.1,
    (later.keeps (Due).next.lanes.openPayment).trans signed.2.2,
    Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _⟩

/-- Try every registered candidate at the reached reserve. A failed
replacement still pays the original due round. A successful trial
generates the new reserve index while carrying the installed reads. -/
def chooseReplacement : RetainedDue before menu home replies ⊕ Rebased before menu :=
  if within : quantum ≤ (Now).programme.law.duration Raw then
    match chooseRecipe (Now).programme origin Raw people menu with
    | .inl failed => .inl (retainDue before menu home replies (.rejected failed))
    | .inr chosen => .inr (postRecipe before menu chosen within)
  else .inl (retainDue before menu home replies (.slow (lt_of_not_ge within)))

theorem chooseReplacement_uses_an_available_registered_recipe
    (clock : quantum ≤ (Now).programme.law.duration Raw) (i : Fin menu.length)
    (paid : FixedPoint.OpenPeace.Operational.RecipeConditions (Now).programme origin Raw people menu[i]) :
    ∃ replacement, chooseReplacement before menu home replies = .inr replacement := by
  obtain ⟨chosen, selected⟩ := chooseRecipe_finds_an_available_word _ _ _ _ menu i paid
  exact ⟨postRecipe before menu chosen clock, by rw [chooseReplacement, dif_pos clock, selected]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
