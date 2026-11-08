import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReconfirmationClosure

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryMaterial
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)

abbrev current := EventHistory.execute start past
abbrev reading (worker : Fin model.source.code.sites) := LocalWithdrawal.reading model (current model start past) worker
abbrev inquiry (worker : Fin model.source.code.sites) :=
  WithdrawalState.produce model start (past.map Prod.fst) worker (reading model start past worker)

inductive Obstruction where
  | environmentTurn | noFuel | unseen | ambiguous | local (reason : LocalWithdrawal.Obstruction)
  | unsupportedReaffirmation | noPairCapacity | unpaid
  deriving DecidableEq

structure Ready where
  private mk ::
  worker : Fin model.source.code.sites
  value : Request Party Good Port (Mandate.State Party Technology) Instrument
  prepared : inquiry model start past worker = .ready value
  supported : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions
  capacity : 2 ≤ model.source.code.actionLimit
  live : 0 < (EventStep.seed (current model start past)).remaining
  owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start past).ownerStart
    (EventStep.seed (current model start past)).history.length = some worker

abbrev protocol (answer : Ready model start past) := WithdrawalInquiry.protocol model start (past.map Prod.fst) answer.worker
abbrev full (answer : Ready model start past) := past ++ [(protocol model start past answer, OriginQueue.environment start)]
abbrev row (answer : Ready model start past) :=
  StageTrace.material (current model start past) (protocol model start past answer) (OriginQueue.environment start)

inductive Plan where
  | blocked (reason : Obstruction)
  | ready (answer : Ready model start past)

def produce : Plan model start past :=
  match owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start past).ownerStart
      (EventStep.seed (current model start past)).history.length with
  | none => .blocked .environmentTurn
  | some worker =>
    if live : 0 < (EventStep.seed (current model start past)).remaining then
    match prepared : inquiry model start past worker with
    | .unseen => .blocked .unseen
    | .ambiguous .. => .blocked .ambiguous
    | .blocked reason => .blocked (.local reason)
    | .ready value =>
      if supported : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions then
      if capacity : 2 ≤ model.source.code.actionLimit then
        .ready ⟨worker, value, prepared, supported, capacity, live, owned⟩
      else .blocked .noPairCapacity
      else .blocked .unsupportedReaffirmation
    else .blocked .noFuel

theorem the_generated_local_word_is_actually_submitted (answer : Ready model start past) :
    (row model start past answer).submitted =
      [WithdrawalInquiry.reaffirm model answer.worker, NativeReview.action model start past answer.worker] :=
  WithdrawalInquiry.the_ready_local_word_is_actually_submitted model start answer.worker past answer.value
    answer.prepared answer.supported answer.capacity answer.live answer.owned (OriginQueue.environment start)

theorem the_actual_row_has_exactly_two_items (answer : Ready model start past) :
    (StageTrace.items (row model start past answer)).length = 2 := by
  have count := congrArg List.length (StageTrace.audit_retains_every_request_and_its_actual_validity (row model start past answer)).1
  simpa only [StageTrace.audit, List.length_map, the_generated_local_word_is_actually_submitted,
    List.length_cons, List.length_nil] using count

theorem actual_recovery_preserves_the_complete_original_prefix (answer : Ready model start past) :
    past <+: full model start past answer := List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryMaterial
