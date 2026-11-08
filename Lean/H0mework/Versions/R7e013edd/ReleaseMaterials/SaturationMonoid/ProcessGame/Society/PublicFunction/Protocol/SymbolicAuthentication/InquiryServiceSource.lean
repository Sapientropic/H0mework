import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceSource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (past : JointResponse.Stages model) (worker : Fin model.source.code.sites)
abbrev current := EventHistory.execute start past
abbrev signal := LocalWithdrawal.reading model (current model start past) worker
abbrev request := NativeReview.action model start past worker

-- Information separation is checked on the actual public-rule fibre, not on a supplied answer.
theorem primitive_local_information_generates_the_query
    (uniform : ∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (signal model start past worker),
      WithdrawalState.request model state worker = request model start past worker)
    (member : model.source.code.siteParty worker ∈ Delegation.members model.scope.task)
    (capacity : 1 ≤ model.source.code.actionLimit)
    (activation : Event.activate worker ∈ model.source.code.eventAlphabet)
    (memory : model.source.code.memoryReady (signal model start past worker) = true)
    (supported : request model start past worker ∈ model.source.code.actions) :
    WithdrawalState.produce model start (past.map Prod.fst) worker (signal model start past worker) =
      .ready (request model start past worker) := by
  have actual : EventStep.seed (current model start past) ∈
      WithdrawalState.fibre model start (past.map Prod.fst) worker (signal model start past worker) :=
    (WithdrawalState.mem_fibre model start _ _ _ _).mpr
      ⟨WithdrawalState.every_actual_prefix_is_in_the_generated_state_domain model start past, rfl⟩
  cases selected : WithdrawalState.query model start (past.map Prod.fst) worker (signal model start past worker) with
  | unseen empty => rw [empty] at actual; cases actual
  | ambiguous first second left right different =>
    exact False.elim (different ((uniform second right).trans (uniform first left).symm))
  | ready value first inside precise _ =>
    have same : value = request model start past worker := precise.symm.trans (uniform first inside)
    simp only [WithdrawalState.produce, selected, same, if_neg (not_not_intro member), if_neg (not_not_intro capacity),
      if_neg (not_not_intro activation), memory, ne_eq, not_true_eq_false, if_false,
      if_neg (not_not_intro supported)]

theorem primitive_conditions_generate_the_actual_local_pair
    (uniform : ∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (signal model start past worker),
      WithdrawalState.request model state worker = request model start past worker)
    (member : model.source.code.siteParty worker ∈ Delegation.members model.scope.task)
    (capacity : 2 ≤ model.source.code.actionLimit)
    (activation : Event.activate worker ∈ model.source.code.eventAlphabet)
    (memory : model.source.code.memoryReady (signal model start past worker) = true)
    (supported : request model start past worker ∈ model.source.code.actions)
    (reaffirm : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions)
    (live : 0 < (EventStep.seed (current model start past)).remaining)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start past).ownerStart
      (EventStep.seed (current model start past)).history.length = some worker)
    (external : Opponent model.source.code) :
    (StageTrace.material (current model start past)
      (WithdrawalInquiry.protocol model start (past.map Prod.fst) worker) external).submitted =
      [WithdrawalInquiry.reaffirm model worker, request model start past worker] := by
  have prepared := primitive_local_information_generates_the_query model start past worker uniform member
    (by omega) activation memory supported
  exact WithdrawalInquiry.the_ready_local_word_is_actually_submitted model start worker past _
    prepared reaffirm capacity live owned external

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceSource
