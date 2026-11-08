import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open MaterialRoundSource
open RecycledQuorumMaterial (Action)

structure Result (old : Bound) (count : Nat) (incoming : List Action) : Type where
  private mk ::
  incomingDisposition : Native.Authority.FullDisposition (supplied old count incoming) (depth old count)
  incoming_exact : incomingDisposition = Native.Authority.fullGenerate (supplied old count incoming) (depth old count)
  recoveryDisposition : Native.Authority.FullDisposition (attempted old count incoming) (depth old count+1)
  recovery_exact : recoveryDisposition = Native.Authority.fullGenerate (attempted old count incoming) (depth old count+1)
  nextRound : Option (Sigma fun entry : Ready old count incoming => SubjectQuorum.Result (emitter old count incoming entry))

def produce (old : Bound) (count : Nat) (incoming : List Action) : Result old count incoming :=
  ⟨Native.Authority.fullGenerate (supplied old count incoming) (depth old count),rfl,
    Native.Authority.fullGenerate (attempted old count incoming) (depth old count+1),rfl,
    (inspect old count incoming).map fun entry => ⟨entry,outcome old count incoming entry⟩⟩

inductive Status where
  | historyRefused | phaseRefused | blocked (reason : SubjectQuorum.Obstruction) | decided (value : Bool)
  deriving DecidableEq

def status (old : Bound) (count : Nat) (incoming : List Action) : Status :=
  match (produce old count incoming).nextRound with
  | none => match preparation old count incoming with
      | .historyRefused => .historyRefused
      | _ => .phaseRefused
  | some next => match next.2 with
      | .blocked reason => .blocked reason
      | .decided value _ => .decided value

variable (old : Bound) (count : Nat) (incoming : List Action)

theorem every_raw_input_and_recovery_retains_original_accounts_even_when_refused
    (ordinal : Nat) (earlier : ordinal ≤ depth old count+1) :
    Native.Coupling.Match old.source.code old.source.input (attempted old count incoming).source.input
      (Financial.accountAt old.source.input ordinal) (Financial.accountAt (attempted old count incoming).source.input ordinal) := by
  have one := Machine.Continuation.complete_financial_prefix old.source count incoming ordinal earlier
  have two := Machine.Continuation.complete_financial_prefix (supplied old count incoming).source
    (suppliedCount count) (recovery old count incoming) ordinal (by change ordinal ≤ depth old count+2;omega)
  exact ⟨two.slots.trans one.slots,two.events.trans one.events⟩

theorem both_actual_preparation_occurrences_have_their_own_whole_ledger_and_next :
    let first := Native.Runtime.facade (supplied old count incoming).source
    let firstTick := first.seed.advance (depth old count+1)
    let second := Native.Runtime.facade (attempted old count incoming).source
    let secondTick := second.seed.advance (depth old count+2)
    (produce old count incoming).incomingDisposition = Native.Authority.fullGenerate (supplied old count incoming) (depth old count) ∧
      (produce old count incoming).recoveryDisposition = Native.Authority.fullGenerate (attempted old count incoming) (depth old count+1) ∧
      HEq firstTick.tick.generated.wholeLedgerWriteBack
        (firstTick.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt firstTick.current.visit.current) ∧
      firstTick.tick.nextCurrent = first.process.stateAt (first.process.successor firstTick.state) ∧
      HEq secondTick.tick.generated.wholeLedgerWriteBack
        (secondTick.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt secondTick.current.visit.current) ∧
      secondTick.tick.nextCurrent = second.process.stateAt (second.process.successor secondTick.state) := by
  have one := (Native.Runtime.facade (supplied old count incoming).source).readoutAt_factorizes
    ((Native.Runtime.facade (supplied old count incoming).source).seed.advance (depth old count+1)) .responsibilities
  have two := (Native.Runtime.facade (attempted old count incoming).source).readoutAt_factorizes
    ((Native.Runtime.facade (attempted old count incoming).source).seed.advance (depth old count+2)) .responsibilities
  exact ⟨rfl,rfl,one.2.2.1,one.2.2.2.2,two.2.2.1,two.2.2.2.2⟩

variable (entry : Ready old count incoming)

theorem readiness_is_generated_from_actual_history_and_three_request_admission_checks :
    (emitter old count incoming entry).code.initial = old.source.code.initial ∧
      (emitter old count incoming entry).code.law = old.source.code.law ∧
      (emitter old count incoming entry).history = RoundArchive.snapshot (supplied old count incoming).source
        (suppliedCount count) ++ [recovery old count incoming] ∧
      old.source.code.law.Valid (prepared old count incoming) payment ∧
      old.source.code.law.Valid (old.source.code.law.step (prepared old count incoming) payment) fee ∧
      old.source.code.law.Valid (old.source.code.law.step (old.source.code.law.step (prepared old count incoming) payment) fee) fee := by
  exact ⟨rfl,rfl,RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival _ _ _,of_decide_eq_true entry.admitted⟩

theorem actual_new_execution_keeps_every_supplied_financial_account
    (ordinal : Nat) (earlier : ordinal ≤ depth old count+1+1) :
    Native.Coupling.Match (supplied old count incoming).source.code (supplied old count incoming).source.input (actual old count incoming entry).source.input
      (Financial.accountAt (supplied old count incoming).source.input ordinal) (Financial.accountAt (actual old count incoming entry).source.input ordinal) := by
  have size : (emitter old count incoming entry).history.length = depth old count+1+1 := by
    change (RoundArchive.history (supplied old count incoming).source (suppliedCount count) (recovery old count incoming)).length = _
    rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length];rfl
  have prior : ∀ n, n < depth old count+1+1 →
      ProgrammeSource.rawEvent (actual old count incoming entry).source.input (ProgrammeHistory.visitAt (supplied old count incoming).source.input n).current =
        ProgrammeSource.rawEvent (supplied old count incoming).source.input (ProgrammeHistory.visitAt (supplied old count incoming).source.input n).current := by
    intro n inside
    have raw := RoundArchive.prior_events (supplied old count incoming).source (suppliedCount count) (recovery old count incoming) payment fee entry.history n inside
    cases view : (ProgrammeHistory.visitAt (supplied old count incoming).source.input n).current with
    | bootstrap => rfl
    | running current past =>
      have rounds := ProgrammeHistory.visit_round (supplied old count incoming).source.input n
      rw [view] at rounds
      have bounded : current.round - (supplied old count incoming).source.code.initial.round - 1 < (emitter old count incoming entry).history.length := by
        change current.round = (supplied old count incoming).source.code.initial.round + n at rounds
        rw [size];omega
      have same : (actual old count incoming entry).source.body current = (emitter old count incoming entry).body current := by
        have sameHistory : (actual old count incoming entry).source.history = (emitter old count incoming entry).history := rfl
        have sameInitial : (actual old count incoming entry).source.code.initial = (supplied old count incoming).source.code.initial := rfl
        unfold Machine.body
        rw [sameHistory,sameInitial,show (emitter old count incoming entry).code.initial = (supplied old count incoming).source.code.initial from rfl]
        rw [List.getElem?_eq_getElem bounded]
      change (actual old count incoming entry).source.body current = _
      rw [view] at raw
      exact same.trans raw
  exact Native.Coupling.History.complete_accounts (supplied old count incoming).source.code (supplied old count incoming).source.input (actual old count incoming entry).source.input
    rfl rfl (depth old count+1+1) prior (supplied old count incoming).source.body (actual old count incoming entry).source.body rfl rfl ordinal earlier

theorem actual_new_execution_keeps_every_original_financial_account
    (ordinal : Nat) (earlier : ordinal ≤ depth old count+1) :
    Native.Coupling.Match old.source.code old.source.input (actual old count incoming entry).source.input
      (Financial.accountAt old.source.input ordinal) (Financial.accountAt (actual old count incoming entry).source.input ordinal) := by
  have one := Machine.Continuation.complete_financial_prefix old.source count incoming ordinal earlier
  have two := actual_new_execution_keeps_every_supplied_financial_account old count incoming entry ordinal (by omega)
  exact ⟨two.slots.trans one.slots,two.events.trans one.events⟩

theorem every_completed_new_round_consumes_its_entire_payment_responsibility_and_next
    (value : Bool) (subject : ApplicationSubject.Subject (emitter old count incoming entry))
    (done : outcome old count incoming entry = .decided value subject) :
    let consumed := ControlResponsibility.produce entry.bound (input old count incoming entry) 0 (protocol old count incoming entry)
      (environment old count incoming entry) (vocabulary old count incoming entry) (encoding old count incoming entry) (reception old count incoming entry) rfl 0
    let runtime := ControlResponsibility.runtime entry.bound (input old count incoming entry) 0 (protocol old count incoming entry)
      (environment old count incoming entry) (vocabulary old count incoming entry) (encoding old count incoming entry) (reception old count incoming entry) rfl 0
    (∃ item, (item,true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
      flowAt ((code old count incoming entry).law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt ((code old count incoming entry).law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      ((code old count incoming entry).law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade entry.bound (input old count incoming entry) 0 (protocol old count incoming entry)
        (environment old count incoming entry) (vocabulary old count incoming entry) (encoding old count incoming entry) (reception old count incoming entry) rfl).process.stateAt
          ((CommunicationRuntime.facade entry.bound (input old count incoming entry) 0 (protocol old count incoming entry)
            (environment old count incoming entry) (vocabulary old count incoming entry) (encoding old count incoming entry) (reception old count incoming entry) rfl).process.successor runtime.state) := by
  have paid := SubjectQuorum.decision_consumes_the_original_subject_payment_responsibility_and_next (vocabulary old count incoming entry)
    entry.bound (input old count incoming entry) 0 (protocol old count incoming entry) (environment old count incoming entry) (encoding old count incoming entry)
    (reception old count incoming entry) rfl 0 6 6 (slot old count incoming entry) 1 value subject done
  have address : ApplicationSubject.originCut (emitter old count incoming entry) 0 (slot old count incoming entry) = 0 := by
    simp [ApplicationSubject.originCut,ApplicationSubject.baseRound]
  rw [address] at paid
  exact ⟨paid.2.1,paid.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundConsumer
