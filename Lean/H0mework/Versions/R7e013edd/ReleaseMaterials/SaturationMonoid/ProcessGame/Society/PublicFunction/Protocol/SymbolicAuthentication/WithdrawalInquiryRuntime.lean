import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquirySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiryRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (final : Cursor model.source.code)

abbrev native := LocalContentRuntime.native model final
abbrev family := Native.Authority.programme (native model final)
abbrev sourceIndex := Native.Authority.sourceIndex (native model final)
abbrev depth := final.source.history.length + 1 + final.cut
abbrev runtime := LocalContentRuntime.runtime model final
abbrev authority := LocalContentRuntime.authority model final
abbrev facade := Feedback.Authority.Runtime.facade (native model final) final.entry rfl rfl

theorem the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next :
    (authority model final).current = Native.Authority.fullGenerate (native model final) (depth model final) ∧
      (∀ original : Native.Authority.Challenge (native model final),
        let history := Mandate.Challenge.through (family model final) (sourceIndex model final) original (depth model final + 2)
        history.state.current.history = history.state.generated.events) ∧
      HEq ((facade model final).readoutAt (runtime model final) .responsibilities)
        ((runtime model final).tick.generated.projectionOutcome (.component ())) ∧
      HEq (runtime model final).tick.generated.wholeLedgerWriteBack
        ((runtime model final).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime model final).current.visit.current) ∧
      (runtime model final).tick.nextCurrent = (facade model final).process.stateAt
        ((facade model final).process.successor (runtime model final).state) := by
  have rooted := (facade model final).readoutAt_factorizes (runtime model final) .responsibilities
  exact ⟨(authority model final).current_exact,
    fun original => Native.Authority.every_challenge_history_is_its_own_actual_native_run (native model final) original _,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiryRuntime
