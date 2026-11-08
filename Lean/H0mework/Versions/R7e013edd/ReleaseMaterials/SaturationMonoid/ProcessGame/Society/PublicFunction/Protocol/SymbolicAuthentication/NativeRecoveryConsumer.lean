import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecovery
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiryRuntime

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev reenter (answer : NativeRecovery.Ready model start past vocabulary encoding law) :=
  JointResponseRun.produce model start vocabulary encoding law (NativeRecovery.full model start past vocabulary encoding law answer)

theorem the_original_root_consumes_the_actual_recovery_and_preserves_it_for_joint_reentry
    (answer : NativeRecovery.Ready model start past vocabulary encoding law) :
    let recovered := NativeRecovery.full model start past vocabulary encoding law answer
    let final := EventHistory.execute start recovered
    let runtime := WithdrawalInquiryRuntime.runtime model final
    let authority := WithdrawalInquiryRuntime.authority model final
    (NativeRecoverySource.before model start past answer.material answer.original).isPending _ _ = true ∧
    NativeRecoverySource.stale model start past answer.material answer.original = true ∧
    (∃ row ∈ authority.current.challenges, row.1 = answer.original ∧ row.2.isPending _ _ = false) ∧
    (∀ item ∈ StageTrace.items (NativeRecoveryMaterial.row model start past answer.material),
      model.source.code.law.Valid item.before item.request) ∧
    recovered <+: (reenter model start past vocabulary encoding law answer).stages ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (EventHistory.execute start (NativeRecovery.full model start past vocabulary encoding law answer))
  refine ⟨answer.qualified.pending, answer.qualified.stale, ?_,
    NativeRecovery.the_recovery_word_has_actual_validity_for_every_original_item model start past vocabulary encoding law answer,
    JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law _ _,
    rooted.2.2.2.1, rooted.2.2.2.2⟩
  rw [(WithdrawalInquiryRuntime.authority model
    (EventHistory.execute start (NativeRecovery.full model start past vocabulary encoding law answer))).current_exact]
  exact NativeRecovery.the_original_terminal_row_is_in_the_actual_full_inventory model start past vocabulary encoding law answer

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryConsumer
