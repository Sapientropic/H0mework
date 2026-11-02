import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRequestAuthentication

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (rival : Opponent model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code) (scope : Scope) (threshold : Nat)

abbrev stages := LocalRequestAuthentication.produce vocabulary law start past rival
abbrev root := RequestReadbackRuntime.root model start (stages model start past rival vocabulary law) vocabulary encoding law scope threshold
abbrev runtime := RequestReadbackRuntime.runtime model start (stages model start past rival vocabulary law) vocabulary encoding law scope threshold
abbrev facade := RequestReadbackRuntime.facade model start (stages model start past rival vocabulary law) vocabulary encoding law scope threshold
abbrev requests := RequestReadbackRuntime.inheritedRequests model start (stages model start past rival vocabulary law) vocabulary encoding law scope threshold
abbrev authority := RequestReadbackRuntime.authority model start (stages model start past rival vocabulary law) vocabulary encoding law scope threshold
abbrev actualBound := RequestReadbackRuntime.actualBound model start (stages model start past rival vocabulary law) vocabulary encoding law
abbrev final := RequestReadbackRuntime.final model start (stages model start past rival vocabulary law) vocabulary encoding law

theorem every_local_authentication_run_is_in_the_same_final_source :
    past <+: RequestReadbackRuntime.full model start (stages model start past rival vocabulary law) vocabulary encoding law :=
  (LocalRequestAuthentication.the_actual_local_authentication_run_preserves_every_original_stage vocabulary law start rival _ past).trans
    (LocalJointRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law _ _)

theorem locally_known_source_statements_reach_independent_verify_the_original_root_ledger_and_next
    (site : Fin model.source.code.sites) (body : RequestAttestation.Statement (code := model.source.code))
    (known : body ∈ (LocalRequestAuthentication.generate vocabulary law start (past.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site)).statements) :
    RequestAttestation.verify vocabulary start past body = true ∧
    body ∈ requests model start past rival vocabulary encoding law scope threshold ∧
    RequestReadback.localRead (code := model.source.code) ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = some body.request ∧
    body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start past)).current ∧
    (authority model start past rival vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
      (actualBound model start past rival vocabulary encoding law)
      ((final model start past rival vocabulary encoding law).source.history.length + 1 +
        (final model start past rival vocabulary encoding law).cut) ∧
    HEq (runtime model start past rival vocabulary encoding law scope threshold).tick.generated.wholeLedgerWriteBack
      ((runtime model start past rival vocabulary encoding law scope threshold).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime model start past rival vocabulary encoding law scope threshold).current.visit.current) ∧
    (runtime model start past rival vocabulary encoding law scope threshold).tick.nextCurrent =
      (facade model start past rival vocabulary encoding law scope threshold).process.stateAt
        ((facade model start past rival vocabulary encoding law scope threshold).process.successor
          (runtime model start past rival vocabulary encoding law scope threshold).state) := by
  obtain ⟨source, read, fresh⟩ := LocalRequestAuthentication.local_authentication_recovers_the_complete_actual_source_statement
    vocabulary law start past site body known
  obtain ⟨more, same⟩ := every_local_authentication_run_is_in_the_same_final_source model start past rival vocabulary encoding law
  have member : body ∈ requests model start past rival vocabulary encoding law scope threshold := by
    change body ∈ RequestAttestation.ledger vocabulary start
      (RequestReadbackRuntime.full model start (stages model start past rival vocabulary law) vocabulary encoding law)
    change past ++ more = _ at same
    rw [← same]
    unfold RequestAttestation.ledger at *
    rw [StageQueue.records_append, List.flatMap_append]
    exact List.mem_append_left _ source
  have factor := (facade model start past rival vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past rival vocabulary encoding law scope threshold) .readback
  exact ⟨(RequestAttestation.independently_verified_iff vocabulary start past body).mpr source, member, read, fresh,
    (authority model start past rival vocabulary encoding law scope threshold).current_exact, factor.2.2.1, factor.2.2.2.2⟩

theorem the_new_local_policy_is_installed_in_the_actual_source
    (site : Fin model.source.code.sites)
    (owned : StageTrace.activation (StageTrace.material (EventHistory.execute start past)
      (LocalRequestAuthentication.protocol vocabulary law start (past.map Prod.fst)) rival) = some site) :
    ((EventHistory.execute start past).after
      (LocalRequestAuthentication.protocol vocabulary law start (past.map Prod.fst)) rival).source.feedbackPolicy
      (EventHistory.execute start past).cut = some (LocalRequestAuthentication.policy vocabulary law start (past.map Prod.fst)) :=
  StageTrace.the_live_work_policy_is_installed_in_the_actual_source _ _ rival
    (StageTrace.an_owned_activation_submits_its_selected_work _ _ rival site owned).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationRuntime
