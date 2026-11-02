import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenTrace

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenExecution
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource

theorem two_distinct_fresh_paid_messages_generate_two_different_actual_owned_replies :
    (actual .normal).state.past.length = 16 ∧
    ((FreshReception.poll vocabulary (encoding .normal) (law .normal) (start .normal 16)
      ((actual .normal).state.past.take 6) 1).map fun receipt =>
        (receipt.confirmation.index, receipt.statement.request, receipt.reading.val)) = [(5, yes, 1)] ∧
    ((FreshReception.poll vocabulary (encoding .normal) (law .normal) (start .normal 16)
      ((actual .normal).state.past.take 10) 1).map fun receipt =>
        (receipt.confirmation.index, receipt.statement.request, receipt.reading.val)) = [(9, ReceiptDrivenSource.phase, 2)] ∧
    ((StageTrace.records (start .normal 16) (actual .normal).state.past)[6]?).map
      (fun row => (StageTrace.activation row, row.submitted)) = some (some 1, [positive]) ∧
    ((StageTrace.records (start .normal 16) (actual .normal).state.past)[10]?).map
      (fun row => (StageTrace.activation row, row.submitted)) = some (some 1, [phaseReply]) := by
  simp only [ReceiptDrivenTrace.actual_history_is_the_verified_source_trace]
  decide +kernel

theorem the_two_original_source_statements_are_legal_different_phases :
    RequestAttestation.verify vocabulary (start .normal 16) (actual .normal).state.past
      ⟨firstBallot .normal, yes⟩ = true ∧
    RequestAttestation.verify vocabulary (start .normal 16) (actual .normal).state.past
      ⟨secondBallot .normal, ReceiptDrivenSource.phase⟩ = true ∧
    OwnedAttestation.conflicts (ReceiptDrivenSource.source .normal) (firstBallot .normal) (secondBallot .normal) = false := by
  simp only [ReceiptDrivenTrace.actual_history_is_the_verified_source_trace]
  decide +kernel

theorem both_actual_replies_have_their_own_paid_complete_statements :
    RequestAttestation.verify vocabulary (start .normal 16) (actual .normal).state.past
      ⟨⟨6, 0, 1, true, slot, true, 1⟩, positive⟩ = true ∧
    RequestAttestation.verify vocabulary (start .normal 16) (actual .normal).state.past
      ⟨⟨10, 0, 1, true, secondScope, true, 1⟩, phaseReply⟩ = true := by
  simp only [ReceiptDrivenTrace.actual_history_is_the_verified_source_trace]
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenExecution
