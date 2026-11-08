import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderChecks
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveHeaderSource

theorem the_same_saved_endpoint_has_the_original_material_debt_and_fuel :
    (EventStep.seed start).current.stock false true = 3 ∧
    (EventStep.seed start).current.stock true true = 1 ∧
    (EventStep.seed start).current.claims () false true = 7 ∧
    (EventStep.seed start).current.technology.holder = none ∧
    start.cut = 41 ∧ (EventStep.seed start).remaining = 23 := by decide +kernel

theorem both_owned_paid_ballots_are_generated_by_actual_forward_requests :
    (StageBudget.ledger vocabulary start actual.stages).map (fun ballot => (ballot.actor,ballot.cut,ballot.fee)) =
      [(true,42,1),(false,44,1)] ∧
    (StageTrace.records start actual.stages).flatMap (fun row => row.submitted) =
      [ProductiveMandateSource.consume,ProductiveMandateSource.maintain] := by decide +kernel

theorem the_actual_headers_generate_four_owned_authenticated_sends :
    (HeaderTransport.wires vocabulary start actual.stages).map
      (fun wire => (wire.ballot.actor,wire.serial,wire.recipient.val,wire.signal.val,wire.sendCut)) =
      [(true,0,0,0,46),(false,1,0,0,48),(true,2,1,0,50),(false,3,1,0,52)] := by decide +kernel

theorem both_actual_receivers_generate_distinct_identity_quorums :
    (observed zero).receipts.length = 2 ∧ (observed one).receipts.length = 2 ∧
    ActorQuorum.support (observed zero) scope true = {false,true} ∧
    ActorQuorum.support (observed one) scope true = {false,true} ∧
    ActorStageEnvelope.budget start vocabulary actual.stages scope = 0 ∧
    decideAt zero = .decided true ∧ decideAt one = .decided true := by decide +kernel

theorem actual_quorum_preserves_the_old_debt_and_does_not_restore_the_revoked_holder :
    (EventStep.seed (actual.current model start)).current.claims () false true = 7 ∧
    (EventStep.seed (actual.current model start)).current.technology.holder = none ∧
    (EventStep.seed (actual.current model start)).current.stock false true = 2 ∧
    (EventStep.seed (actual.current model start)).current.stock true true = 0 ∧
    (EventStep.seed (actual.current model start)).remaining = 10 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderChecks
