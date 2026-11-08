import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open FinancedRoundSource

structure Result (old : Bound) (count : Nat) : Type where
  private mk ::
  previousDisposition : Native.Authority.FullDisposition old (depth old count)
  previous_exact : previousDisposition = Native.Authority.fullGenerate old (depth old count)
  arrivalDisposition : Native.Authority.FullDisposition (attempted old count) (depth old count)
  arrival_exact : arrivalDisposition = nativeAttempt old count
  nextRound : Option (Sigma fun entry : Ready old count => SubjectQuorum.Result (emitter old count entry))

def produce (old : Bound) (count : Nat) : Result old count :=
  ⟨Native.Authority.fullGenerate old (depth old count),rfl,nativeAttempt old count,rfl,
    (ready old count).map fun entry => ⟨entry,outcome old count entry⟩⟩

inductive Status where
  | historyRefused | protocolBlocked (reason : SubjectQuorum.Obstruction) | decided (value : Bool)
  deriving DecidableEq

def status (old : Bound) (count : Nat) : Status :=
  match (produce old count).nextRound with
  | none => .historyRefused
  | some result => match result.2 with
    | .blocked reason => .protocolBlocked reason
    | .decided value _ => .decided value

variable (old : Bound) (count : Nat) (entry : Ready old count)

theorem the_new_round_starts_without_a_paid_vote_and_retains_the_source_genesis :
    OwnedAttestation.ledger (emitter old count entry) (input old count entry) 0 (protocol old count entry)
      (environment old count entry) (vocabulary old count entry) 0 = [] ∧
      (emitter old count entry).code.initial = old.source.code.initial ∧
      (emitter old count entry).history = RoundArchive.snapshot old.source count ++ [arrival old count] :=
  ⟨rfl,rfl,RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival old.source count _⟩

theorem every_old_actual_occurrence_is_kept_before_the_new_round
    (ordinal : Nat) (earlier : ordinal < depth old count+1) :
    (ProgrammeHistory.visitAt (emitter old count entry).input ordinal).current =
        (ProgrammeHistory.visitAt old.source.input ordinal).current ∧
      ProgrammeSource.rawEvent (emitter old count entry).input (ProgrammeHistory.visitAt (emitter old count entry).input ordinal).current =
        ProgrammeSource.rawEvent old.source.input (ProgrammeHistory.visitAt old.source.input ordinal).current :=
  RoundArchive.every_original_raw_occurrence_is_preserved old.source count _ payment fee entry ordinal earlier

theorem actual_new_execution_keeps_every_old_financial_account
    (ordinal : Nat) (earlier : ordinal ≤ depth old count+1) :
    Native.Coupling.Match old.source.code old.source.input (actual old count entry).source.input
      (Financial.accountAt old.source.input ordinal) (Financial.accountAt (actual old count entry).source.input ordinal) := by
  have size : (emitter old count entry).history.length = depth old count+1 := by
    change (RoundArchive.history old.source count (arrival old count)).length = _
    rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length];rfl
  have prior : ∀ n, n < depth old count+1 →
      ProgrammeSource.rawEvent (actual old count entry).source.input (ProgrammeHistory.visitAt old.source.input n).current =
        ProgrammeSource.rawEvent old.source.input (ProgrammeHistory.visitAt old.source.input n).current := by
    intro n inside
    have raw := RoundArchive.prior_events old.source count (arrival old count) payment fee entry n inside
    cases view : (ProgrammeHistory.visitAt old.source.input n).current with
    | bootstrap => rfl
    | running current past =>
      have rounds := ProgrammeHistory.visit_round old.source.input n
      rw [view] at rounds
      have bounded : current.round - old.source.code.initial.round - 1 < (emitter old count entry).history.length := by
        change current.round = old.source.code.initial.round + n at rounds
        rw [size];omega
      have same : (actual old count entry).source.body current = (emitter old count entry).body current := by
        have sameHistory : (actual old count entry).source.history = (emitter old count entry).history := rfl
        have sameInitial : (actual old count entry).source.code.initial = old.source.code.initial := rfl
        unfold Machine.body
        rw [sameHistory,sameInitial,show (emitter old count entry).code.initial = old.source.code.initial from rfl]
        rw [List.getElem?_eq_getElem bounded]
      change (actual old count entry).source.body current = _
      rw [view] at raw
      exact same.trans raw
  exact Native.Coupling.History.complete_accounts old.source.code old.source.input (actual old count entry).source.input
    rfl rfl (depth old count+1) prior old.source.body (actual old count entry).source.body rfl rfl ordinal earlier

theorem every_completed_new_round_consumes_its_entire_payment_responsibility_and_next
    (value : Bool) (subject : ApplicationSubject.Subject (emitter old count entry))
    (done : outcome old count entry = .decided value subject) :
    let consumed := ControlResponsibility.produce (bound entry) (input old count entry) 0 (protocol old count entry)
      (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry) rfl 0
    let runtime := ControlResponsibility.runtime (bound entry) (input old count entry) 0 (protocol old count entry)
      (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry) rfl 0
    (∃ item, (item,true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
      flowAt ((code old count entry).law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt ((code old count entry).law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      ((code old count entry).law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade (bound entry) (input old count entry) 0 (protocol old count entry)
        (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry) rfl).process.stateAt
          ((CommunicationRuntime.facade (bound entry) (input old count entry) 0 (protocol old count entry)
            (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry) rfl).process.successor runtime.state) := by
  have paid := SubjectQuorum.decision_consumes_the_original_subject_payment_responsibility_and_next (vocabulary old count entry)
    (bound entry) (input old count entry) 0 (protocol old count entry) (environment old count entry) (encoding old count entry)
    (reception old count entry) rfl 0 (window old count entry) (window old count entry) (slot old count entry) 1 value subject done
  have address : ApplicationSubject.originCut (emitter old count entry) 0 (slot old count entry) = 0 := by
    simp [ApplicationSubject.originCut,ApplicationSubject.baseRound]
  rw [address] at paid
  exact ⟨paid.2.1,paid.2.2.2⟩

theorem an_actual_refused_arrival_retains_all_prior_accounts_and_a_literal_native_successor (ordinal : Nat)
    (earlier : ordinal ≤ depth old count+1) :
    Native.Coupling.Match old.source.code old.source.input (attempted old count).source.input
      (Financial.accountAt old.source.input ordinal) (Financial.accountAt (attempted old count).source.input ordinal) ∧
      prepared old count = old.source.code.law.next (current old count) (arrival old count) :=
  ⟨Machine.Continuation.complete_financial_prefix old.source count _ ordinal earlier,
    (the_actual_input_preserves_the_old_endpoint_and_executes_its_own_word old count).2.2⟩

theorem every_arrival_disposition_has_its_original_whole_ledger_and_generated_next :
    let facade := Native.Runtime.facade (attempted old count).source
    let runtime := facade.seed.advance (depth old count+1)
    (produce old count).previousDisposition = Native.Authority.fullGenerate old (depth old count) ∧
      (produce old count).arrivalDisposition = Native.Authority.fullGenerate (attempted old count) (depth old count) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = facade.process.stateAt (facade.process.successor runtime.state) := by
  have rooted := (Native.Runtime.facade (attempted old count).source).readoutAt_factorizes
    ((Native.Runtime.facade (attempted old count).source).seed.advance (depth old count+1)) .responsibilities
  exact ⟨rfl,rfl,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundConsumer
