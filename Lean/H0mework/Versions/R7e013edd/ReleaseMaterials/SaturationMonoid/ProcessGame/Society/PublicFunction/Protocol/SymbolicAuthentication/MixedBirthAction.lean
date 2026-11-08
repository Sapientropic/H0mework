import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBirthCost

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthAction
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

def tail (past : JointResponse.Stages model) :
    UnifiedRecoveryDispatch.Action model start vocabulary encoding law past → JointResponse.Stages model
  | .original (.communication (.conflict answer _)) =>
      [(IncidentResponse.protocol model start past vocabulary encoding law answer, OriginQueue.environment start)]
  | .original (.communication (.rejection answer _)) =>
      [(RejectionResponse.protocol model start past vocabulary encoding law answer, OriginQueue.environment start)]
  | .original (.communication (.retry answer _)) => RetryBirthCost.tail model start past vocabulary encoding law answer
  | .original (.communication (.wait _)) | .original (.wait _) => [(SilentWindow.quiet, OriginQueue.environment start)]
  | .original (.withdrawal answer ..) | .original (.refused answer ..) =>
      [(NativeReview.protocol model start past answer, OriginQueue.environment start)]
  | .recovery answer => [(NativeRecoveryMaterial.protocol model start past answer.material, OriginQueue.environment start)]

theorem tail_is_the_literal_actual_extension (past : JointResponse.Stages model)
    (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :
    past ++ tail model start vocabulary encoding law past action =
      UnifiedRecoveryDispatch.after model start vocabulary encoding law past action := by
  cases action with
  | recovery => rfl
  | original action =>
    cases action with
    | communication action =>
      cases action with
      | retry answer _ => exact RetryBirthCost.the_retry_tail_is_the_literal_actual_extension model start past vocabulary encoding law answer
      | conflict | rejection | wait => rfl
    | withdrawal | refused | wait => rfl

abbrev births (past : JointResponse.Stages model)
    (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :=
  BirthWindow.births model (EventHistory.execute start past) (tail model start vocabulary encoding law past action)

theorem every_native_withdrawal_or_refusal_has_no_new_births
    (past : JointResponse.Stages model) (ready : NativeReview.Ready model start past) :
    BirthWindow.births model (EventHistory.execute start past)
      [(NativeReview.protocol model start past ready, OriginQueue.environment start)] = 0 := by
  apply BirthWindow.an_actual_unsigned_visit_has_no_births
  intro item inside
  rw [NativeReviewHistory.items_are_original model start past ready (OriginQueue.environment start)] at inside
  have same := List.mem_singleton.mp inside
  subst item
  simp [NativeReview.action, Mandate.request, Mandate.Challenge.Submission]

theorem every_actual_recovery_has_no_open_births
    (past : JointResponse.Stages model) (answer : NativeRecovery.Ready model start past vocabulary encoding law) :
    births model start vocabulary encoding law past (.recovery answer) = 0 := by
  unfold births tail
  rw [BirthWindow.a_single_actual_visit_has_its_exact_birth_slice]
  have actual := RecoveryInventory.the_actual_recovery_does_not_refill_pending_with_its_own_newborn
    model start past vocabulary encoding law answer
  change CompletedInventory.openBorn (BirthWindow.family model)
    (BirthWindow.inputs model (EventHistory.execute start (past ++ [_])))
    (EventStep.boundary (EventHistory.execute start past)) = 0 at actual
  rw [OriginQueue.execute_append] at actual
  exact actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthAction
