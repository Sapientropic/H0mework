import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Batch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Move

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Transport (sourceSupport)
open Quantities.Execution (endAt query)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

/-- The canonical live visit and all of its admitted liability coordinates
over the literal current of the original dispatcher. -/
structure StateAt (seed : C) (community : Party → Community) (cut : C) where
  world : WorldRelationNetwork
  stack : Stack seed community cut.native.frame.N world
  resident : Resident world
  exactSupport : resident.support = stack.support (sourceSupport cut.native)

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)

abbrev State (past : History) := StateAt seed community (endAt seed past)

def initialState : State seed community [] where
  world := seed.native.frame.N
  stack := .base _
  resident := nativeResident seed
  exactSupport := rfl

namespace StateAt

variable {seed cut other : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community} (state : StateAt seed community cut)

def rebase (same : cut = other) : StateAt seed community other := same ▸ state

theorem rebase_resident (same : cut = other) :
    (state.rebase same).resident.erase = state.resident.erase := by cases same; rfl

theorem rebase_balances (same : cut = other) :
    (state.rebase same).stack.balances = state.stack.balances := by cases same; rfl

def atQuery (input : Proposal) : StateAt seed community (query cut input) := by
  cases input with
  | none => exact state
  | some _ => exact ⟨state.world, state.stack, state.resident, state.exactSupport⟩

theorem query_resident (input : Proposal) :
    (state.atQuery input).resident.erase = state.resident.erase := by cases input <;> rfl

theorem query_balances (input : Proposal) :
    (state.atQuery input).stack.balances = state.stack.balances := by cases input <;> rfl

private theorem rebase_stack_support {N M J : WorldRelationNetwork}
    (same : M = N) (stack : Stack seed community N J) (support : M.Support) :
    (same.symm ▸ stack : Stack seed community M J).support support =
      stack.support (same ▸ support) := by cases same; rfl

private theorem rebase_stack_balances {N M J : WorldRelationNetwork}
    (same : M = N) (stack : Stack seed community N J) :
    (same.symm ▸ stack : Stack seed community M J).balances = stack.balances := by
  cases same
  rfl

def fromPrepared {N : WorldRelationNetwork} {atBase : N.Support}
    (prepared : Prepared seed community N atBase)
    (same : cut.native.frame.N = N) (literal : atBase = same ▸ sourceSupport cut.native) :
    StateAt seed community cut where
  world := prepared.world
  stack := same.symm ▸ prepared.stack
  resident := prepared.entered
  exactSupport := prepared.entered_support.trans ((congrArg prepared.stack.support literal).trans
    (rebase_stack_support same prepared.stack (sourceSupport cut.native)).symm)

theorem fromPrepared_balances {N : WorldRelationNetwork} {atBase : N.Support}
    (prepared : Prepared seed community N atBase)
    (same : cut.native.frame.N = N) (literal : atBase = same ▸ sourceSupport cut.native) :
    (fromPrepared (cut := cut) prepared same literal).stack.balances = prepared.stack.balances :=
  rebase_stack_balances same prepared.stack

def read (row : OpenResponsibilityAt state.world state.resident.support) :
    OpenResponsibilityAt cut.native.frame.N (sourceSupport cut.native) ⊕ (Occurrence seed community × Balance) :=
  state.stack.read _ (state.exactSupport ▸ row)

theorem every_balance_is_a_row_of_the_current (balance : Occurrence seed community × Balance)
    (present : balance ∈ state.stack.balances) :
    ∃ row : OpenResponsibilityAt state.world state.resident.support, state.read row = .inr balance := by
  obtain ⟨row, readRow⟩ := state.stack.every_balance_has_an_actual_open_row _ balance present
  refine ⟨state.exactSupport.symm ▸ row, ?_⟩
  unfold read
  rwa [cast_open_back]

end StateAt

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
