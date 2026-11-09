import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts.Offer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next endAt_append)
open Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}

local notation "History" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument

variable (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

local notation "AtTick" => StateAt seed community (next (endAt seed past) input)
local notation "Pos" => Position seed past input

/-- One use of the original allocation per material position, on the
canonical visit written by the previous position. -/
def consumePositions : List Pos → AtTick → AtTick
  | [], state => state
  | position :: later, state =>
    let plan := atPersonalItem answers past input position state.stack.balances
    consumePositions later (state.consume plan.changes)

theorem consumePositions_origins (positions : List Pos) (state : AtTick) :
    (consumePositions answers past input positions state).stack.balances.map Prod.fst =
      state.stack.balances.map Prod.fst := by
  induction positions generalizing state with
  | nil => rfl
  | cons position _ prior =>
    rw [consumePositions, prior, StateAt.consume_balances]
    exact Changes.result_origins _

variable {past}

/-- The original dispatcher writes material, registrations and damage first.
Only the ensuing receipt allocation reads the victims' personal lanes. -/
def writeTick (prior : State seed community past) (proposal : Proposal) : State seed community (past ++ [proposal]) :=
  (consumePositions answers past proposal (itemPositions past proposal) (posted prior proposal)).rebase
    (endAt_append seed past [proposal]).symm

theorem writeTick_balances (prior : State seed community past) :
    (writeTick answers prior input).stack.balances =
      (consumePositions answers past input (itemPositions past input) (posted prior input)).stack.balances :=
  StateAt.rebase_balances (cut := next (endAt seed past) input) _ _

theorem writeTick_origins (prior : State seed community past) :
    (writeTick answers prior input).stack.balances.map Prod.fst =
      prior.stack.balances.map Prod.fst ++ openings seed community past input := by
  rw [writeTick_balances, consumePositions_origins, posted_balances, List.map_append, List.map_map]
  rw [show (Prod.fst ∘ fun origin => (origin, opening origin)) = id from rfl, List.map_id]

def writeAfter (prior : State seed community past) (suffix : History) : State seed community (past ++ suffix) :=
  List.reverseRecOn (motive := fun tail => State seed community (past ++ tail)) suffix
    ((List.append_nil past).symm ▸ prior)
    (fun front proposal previous => List.append_assoc past front [proposal] ▸ writeTick answers previous proposal)

theorem writeAfter_snoc (prior : State seed community past) (suffix : History) (proposal : Proposal) :
    writeAfter answers prior (suffix ++ [proposal]) =
      (List.append_assoc past suffix [proposal] ▸
        writeTick answers (writeAfter answers prior suffix) proposal : State seed community (past ++ (suffix ++ [proposal]))) := by
  rw [writeAfter, List.reverseRecOn_concat]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts
