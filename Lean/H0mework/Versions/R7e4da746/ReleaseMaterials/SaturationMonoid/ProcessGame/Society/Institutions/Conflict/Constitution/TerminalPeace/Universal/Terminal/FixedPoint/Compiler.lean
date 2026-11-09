import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Closure
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)
open Clearance

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (reserve : Party → Good → ℚ) (body : RawEvent Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "First" => Joint.firstProduction loss body

/-- The additional entrance condition is a finite productive recipe at
the very cut where the native writer has settled the original addresses. -/
structure OpeningAt (word : Word) where
  first : List.IsPrefix First word
  inventory : Joint.ProtectedThrough loss reserve word
  eligible : Occurrence.Eligible answers loss word
  ready : ReadyEntry loss word
  paid : WholeCleared loss answers word
  choice : ProductionChoice offers
  approved : ProductionApproved seed loss word choice
  quantum : ℚ
  recipe : Recipe (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
    (prefixRaw loss word) quantum
  starts : ProductionStartsWith choice recipe.move.word

variable {loss answers reserve body offers}
  {word : Script Party Good Port Technology Instrument}
  (entry : OpeningAt loss answers reserve body offers word)

def OpeningAt.realization : Realization loss answers (fun _ => True) word offers :=
  ⟨⟨Or.inr trivial, entry.eligible⟩, entry.ready, entry.choice, entry.approved,
    entry.recipe.move.accumulatingTrajectory entry.recipe.law, entry.starts⟩

include entry in
theorem OpeningAt.jointlyFeasible : Joint.Feasible loss answers reserve First offers word :=
  ⟨entry.first, entry.inventory, entry.paid, realization_has_an_exactly_viable_source entry.realization⟩

def OpeningAt.current :
    Current (cut := endAt seed (Occurrence.history loss ++ word)) (seed := seed) (community := community)
      (originalRaw loss) (productionRoster seed loss word entry.choice) entry.quantum :=
  ⟨Occurrence.reached answers loss word, _, productionInput seed loss word entry.choice, entry.recipe,
    ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩

theorem OpeningAt.every_old_address_is_retained :
    entry.current.ledger.stack.balances.map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst := by
  change (prefixRows loss answers word).map Prod.fst = _
  rw [Occurrence.reached_origins answers loss word,
    Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers (Occurrence.history loss)
      (Occurrence.history loss) word entry.eligible, Occurrence.originState_origins]

variable (loss answers reserve body offers) (replies : Replies Party Good Port Technology Instrument)

structure FixedOpening where
  word : Word
  entry : OpeningAt loss answers reserve body offers word
  earliest : ∀ other : Word, Nonempty (OpeningAt loss answers reserve body offers other) → word.length ≤ other.length
  fixed : PeaceFixedPoint replies entry.current

private def selectOpening (available : ∃ word : Word, Nonempty (OpeningAt loss answers reserve body offers word)) :
    FixedOpening loss answers reserve body offers replies :=
  let picked := shortestWord (fun word => Nonempty (OpeningAt loss answers reserve body offers word)) available
  let entry := Classical.choice picked.property.1
  ⟨picked.val, entry, picked.property.2, buildPeaceFixedPoint replies entry.current entry.paid⟩

inductive PeaceOutcome
  | jointFailure (diagnostic : Joint.JointOutcome loss answers reserve body offers)
  | noProductiveOpening (joint : Joint.PaidFrontier loss answers reserve First offers)
      (excluded : ∀ word : Word, ¬ Nonempty (OpeningAt loss answers reserve body offers word))
  | installed (original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body)
      (actualProduction : Joint.ProducesAtFirstWrite loss body)
      (peace : FixedOpening loss answers reserve body offers replies)

/-- Read the original first write, solve the joint ledger, then select a
productive fixed-point opening among all feasible continuations. -/
def compilePeace : PeaceOutcome loss answers reserve body offers replies := by
  classical
  let joint := Joint.compileJoint loss answers reserve body offers
  exact match joint with
  | .paid original production paid =>
    if available : ∃ word : Word, Nonempty (OpeningAt loss answers reserve body offers word) then
      .installed original production (selectOpening loss answers reserve body offers replies available)
    else
      .noProductiveOpening paid (fun word fits => available ⟨word, fits⟩)
  | other => .jointFailure other

theorem compilePeace_installs_exactly_when_the_original_source_can_pay_and_renew :
    (∃ original production peace,
      compilePeace loss answers reserve body offers replies = .installed original production peace) ↔
      Joint.ProductionWrite answers loss (Joint.openingDrain loss) body ∧
      Joint.ProducesAtFirstWrite loss body ∧
      ∃ word : Word, Nonempty (OpeningAt loss answers reserve body offers word) := by
  constructor
  · rintro ⟨original, production, peace, _⟩
    exact ⟨original, production, peace.word, ⟨peace.entry⟩⟩
  · intro available
    obtain ⟨original, production, word, ⟨entry⟩⟩ := available
    obtain ⟨first, grows, paid, actual⟩ := (Joint.compileJoint_pays_iff loss answers reserve body offers).mpr
      ⟨original, production, word, entry.jointlyFeasible⟩
    have canOpen : ∃ other : Word, Nonempty (OpeningAt loss answers reserve body offers other) := ⟨word, ⟨entry⟩⟩
    exact ⟨first, grows, selectOpening loss answers reserve body offers replies canOpen, by
      simp only [compilePeace, actual, dif_pos canOpen]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
