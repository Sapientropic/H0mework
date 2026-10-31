import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.ServiceRegression

/-! Actual signed inputs separate pending old snapshots, fresh-scope
maintenance, zero-exit-fund refusals, and literal old archives. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev authority := Handoff.Regression.authority

def signedWord := (Future.emit authority Future.Regression.inventory .admission).map fun action =>
  match action.operation with
  | .present => {action with signer := false}
  | _ => action
def admitted := Joint.submit authority Future.Regression.inventory signedWord
def proposal := request authority.scope (Pending.current authority admitted.inputs) false (.propose true)
def proposed := Joint.submit authority admitted [proposal]
def reviewed := Future.advance authority proposed .revision

theorem actual_new_proposal_keeps_the_old_signed_snapshot_pending_through_review :
    admitted.objections.map (fun record => record.history.isPending) = [true] ∧
    reviewed.objections.map (fun record => record.history.isPending) = [true] ∧
    (Handoff.choose (Pending.B authority) reviewed.inputs).isSome = true := by decide +kernel

def fresh := (Handoff.choose (Pending.B authority) reviewed.inputs).get
  actual_new_proposal_keeps_the_old_signed_snapshot_pending_through_review.2.2
def paidInventory := Challenge.inventory fresh reviewed.objections 4

theorem actual_paid_boundaries_maintain_the_old_challenge_when_replacement_is_blocked :
    (select fresh (start fresh)).isNone = true ∧
    (Challenge.receipts fresh 4).map (Mandate.Challenge.ScopeBoundary.Receipt.command (occurrence fresh)) = [.exit,.review] ∧
    (Challenge.receipts fresh 4).map (Mandate.Challenge.ScopeBoundary.Receipt.accepted (occurrence fresh)) = [true,true] ∧
    paidInventory.map (fun entry => (entry.continuation.state.current.history.drop
      entry.original.history.state.current.history.length).map LifecycleEvent.kind) = [[.maintained,.maintained]] := by decide +kernel

def dryWord : List Action :=
  [⟨false,[],.resource,[],.transfer false true [(.feedstock,1)]⟩,
   Exit.production true,
   ⟨false,[],.resource,[],.use false [(.feedstock,1)] .external⟩,
   ⟨false,[],.resource,[],.use false [(.service,2)] .external⟩]
def dry := Joint.submit authority proposed dryWord
def dryReviewed := Future.advance authority dry .revision

theorem actual_material_debit_still_generates_the_next_scope_with_an_old_pending_challenge :
    (Handoff.choose (Pending.B authority) dryReviewed.inputs).isSome = true ∧
    dryReviewed.objections.map (fun record => record.history.isPending) = [true] ∧
    (Pending.current authority dry.inputs).stock false .feedstock = 0 ∧
    (Pending.current authority dry.inputs).stock true .feedstock = 0 ∧
    (Pending.current authority dry.inputs).stock false .service = 0 ∧
    (Pending.current authority dry.inputs).stock true .service = 4 := by decide +kernel

def dryFresh := (Handoff.choose (Pending.B authority) dryReviewed.inputs).get
  actual_material_debit_still_generates_the_next_scope_with_an_old_pending_challenge.1
def dryInventory := Challenge.inventory dryFresh dryReviewed.objections 4

theorem actual_capture_with_zero_exit_funds_defers_without_discharging_the_old_challenge :
    (current dryFresh 3).technology.holder = some true ∧ (current dryFresh 3).stock true .service = 0 ∧
    (Challenge.receipts dryFresh 4).map (Mandate.Challenge.ScopeBoundary.Receipt.accepted (occurrence dryFresh)) = [false,false] ∧
    dryInventory.map (fun entry => (entry.continuation.state.current.history.drop
      entry.original.history.state.current.history.length).map LifecycleEvent.kind) = [[.deferred,.deferred]] := by decide +kernel

theorem all_archived_original_challenges_keep_their_complete_history :
    (Challenge.inventory Handoff.Regression.financedFresh Handoff.Regression.financedReview.objections 4).map
      (fun entry => entry.continuation.state.current.history.length - entry.original.history.state.current.history.length) = [0] := by decide +kernel

abbrev publicScopeCrossChallengePaidFacade := EpochRuntime.facade authority proposed fresh
abbrev publicScopeCrossChallengeCapturedFacade := EpochRuntime.facade authority dry dryFresh
abbrev publicScopeCrossChallengeArchivedFacade := Handoff.Regression.publicScopeReviewedFinanceFacade

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge.Regression
