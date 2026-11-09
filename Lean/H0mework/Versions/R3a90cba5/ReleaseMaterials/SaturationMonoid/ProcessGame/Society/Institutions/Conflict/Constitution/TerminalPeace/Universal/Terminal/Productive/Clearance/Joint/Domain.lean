import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Inventory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Cycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Reparation.Actual (ReceiptAnswers Script)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (reserve : Party → Good → ℚ) (firstWrite : Script Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)

local notation "Word" => Script Party Good Port Technology Instrument

/-- Any finite continuation may follow the actual first write. All
original input positions are interpreted, including exchanges and receipts. -/
structure Feasible (word : Word) : Prop where
  first : firstWrite.IsPrefix word
  inventory : ProtectedThrough loss reserve word
  payable : WholeCleared loss answers word
  living : ViableEntry loss answers (fun _ => True) word offers

def FeasibleBy (visits : Nat) : Prop :=
  ∃ word : Word, Feasible loss answers reserve firstWrite offers word ∧ word.length ≤ visits

structure PaidFrontier where
  word : Word
  feasible : Feasible loss answers reserve firstWrite offers word
  run : Realization loss answers (fun _ => True) word offers
  earliest : ∀ other : Word, Feasible loss answers reserve firstWrite offers other → word.length ≤ other.length
  originalRows : (prefixRows loss answers word).map Prod.fst =
    (Occurrence.originState loss).stack.balances.map Prod.fst

/-- The least original ordinal is attained over all admitted words,
including arbitrary rational installments in their original order. -/
def selectFirstPaid (available : ∃ word, Feasible loss answers reserve firstWrite offers word) :
    PaidFrontier loss answers reserve firstWrite offers := by
  let selected := shortestWord (Feasible loss answers reserve firstWrite offers) available
  let paid := selected.property.1
  let run := realize paid.living
  have origins := Occurrence.reached_origins answers loss selected.val
  rw [Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers (Occurrence.history loss)
    (Occurrence.history loss) selected.val run.allowed.2, ← Occurrence.originState_origins] at origins
  exact ⟨selected.val, paid, run, selected.property.2, origins⟩

theorem PaidFrontier.feasible_by_iff (paid : PaidFrontier loss answers reserve firstWrite offers) (visits : Nat) :
    FeasibleBy loss answers reserve firstWrite offers visits ↔ paid.word.length ≤ visits :=
  ⟨fun ⟨other, fits, bound⟩ => (paid.earliest other fits).trans bound,
    fun bound => ⟨paid.word, paid.feasible, bound⟩⟩

theorem Feasible.iff_actual {word : Word} :
    Feasible loss answers reserve firstWrite offers word ↔
      firstWrite.IsPrefix word ∧ ProtectedThrough loss reserve word ∧ WholeCleared loss answers word ∧
        Nonempty (Realization loss answers (fun _ => True) word offers) :=
  ⟨fun paid => ⟨paid.first, paid.inventory, paid.payable, ⟨realize paid.living⟩⟩,
    fun ⟨first, inventory, payable, ⟨run⟩⟩ =>
      ⟨first, inventory, payable, realization_has_an_exactly_viable_source run⟩⟩

theorem PaidFrontier.the_same_root_writes_the_paid_living_successor
    (paid : PaidFrontier loss answers reserve firstWrite offers) :
    let prior := Occurrence.reached answers loss paid.word
    let first := Runtime.run prior paid.run.programme (originalRaw loss) paid.run.people paid.run.menus 0
    WholeCleared loss answers paid.word ∧
      first.state.stack.balances = prior.stack.balances ∧
      (⟨prior.world, (Installation.Core.action prior first.read true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = first.state.resident.erase ∧
      Runtime.ClockCofinal prior paid.run.programme (originalRaw loss) paid.run.people paid.run.menus :=
  ⟨paid.feasible.payable, paid.run.the_pilot_writes_the_whole_original_successor.1,
    paid.run.the_pilot_writes_the_whole_original_successor.2.1, paid.run.clock⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
