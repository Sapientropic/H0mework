import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Quantities.Execution (endAt query next)
open Transport (sourceSupport)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Script Party Good Port Technology Instrument}
  (state : State seed community past)
  (input : Input Party Good Port Technology Instrument)
  (safe : History.NoFinancialBirth (query (endAt seed past) input))

local notation "oldCut" => endAt seed past
local notation "newCut" => next (endAt seed past) input

private abbrev originalEdge := History.originalEdge oldCut input safe
private abbrev baseTarget := (originalEdge input safe).sameNetwork ▸ sourceSupport (newCut).native

def sameFirst : First state.world where
  before := state.stack.support (sourceSupport (oldCut).native)
  after := state.stack.support (baseTarget input safe)
  whole := (Stack.Move.wait state.stack).lift
    ⟨(originalEdge input safe).whole, (originalEdge input safe).keys⟩
    ((oldCut).native.frame.entry (oldCut).native.visit.current)
  beforeFinite := state.stack.finite _ ((oldCut).native.frame.entries_finite (oldCut).native.visit.current)
  afterFinite := state.stack.finite _ (reindex_finite (originalEdge input safe).sameNetwork _
    ((newCut).native.frame.entries_finite (newCut).native.visit.current))
  openFibres := state.stack.fibres (oldCut).native.frame.family.open_fibres
  writes := (originalEdge input safe).writes

def samePrepared :
    Prepared seed community (oldCut).native.frame.N (baseTarget input safe) :=
  let first := sameFirst state input safe
  let draft := first.prepare state.resident state.exactSupport.symm
  let initial : Prepared seed community (oldCut).native.frame.N (baseTarget input safe) :=
    ⟨state.world, state.stack, draft, first.first_support⟩
  initial.fileMany (openings seed community past input)

def sameNext : StateAt seed community newCut :=
  StateAt.fromPrepared (samePrepared state input safe) (originalEdge input safe).sameNetwork rfl

theorem same_next_keeps_the_original_balances_and_opens_every_loss :
    (sameNext state input safe).stack.balances = state.stack.balances ++
      (openings seed community past input).map (fun origin => (origin, opening origin)) := by
  unfold sameNext
  rw [StateAt.fromPrepared_balances]
  exact Prepared.fileMany_balances _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
