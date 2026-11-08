import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodePrefix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RoundEpisodeSource RoundEpisodePrefix
open MaterialRoundSource (Bound)

theorem any_number_of_actual_rounds_advances_its_own_boundary (initial : State) (control : Controller) (n : Nat) :
    boundary initial+4*n ≤ boundary (RoundEpisodeSource.run initial control n) := by
  induction n with
  | zero => change boundary initial+4*0 ≤ boundary initial;omega
  | succ n prior =>
    have step := every_episode_advances_the_real_native_boundary (RoundEpisodeSource.run initial control n) (control (RoundEpisodeSource.run initial control n))
    change boundary initial+4*(n+1) ≤ boundary (next (RoundEpisodeSource.run initial control n) (control (RoundEpisodeSource.run initial control n)))
    omega

theorem any_number_of_actual_rounds_keeps_the_entire_original_prefix
    (initial : State) (control : Controller) (n : Nat) :
    Prefix initial.model.source.input (RoundEpisodeSource.run initial control n).model.source.input (boundary initial) := by
  induction n with
  | zero => exact ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n prior =>
    have step := every_episode_keeps_the_complete_original_prefix (RoundEpisodeSource.run initial control n) (control (RoundEpisodeSource.run initial control n))
    have growing := any_number_of_actual_rounds_advances_its_own_boundary initial control n
    exact prior.trans (step.weaken (by omega))

theorem original_financial_accounts_survive_arbitrary_later_controls
    (initial : State) (control : Controller) (n ordinal : Nat) (earlier : ordinal ≤ boundary initial) :
    Native.Coupling.Match initial.model.source.code initial.model.source.input (RoundEpisodeSource.run initial control n).model.source.input
      (Financial.accountAt initial.model.source.input ordinal)
      (Financial.accountAt (RoundEpisodeSource.run initial control n).model.source.input ordinal) := by
  have prior := any_number_of_actual_rounds_keeps_the_entire_original_prefix initial control n
  have events : ∀ cut, cut < boundary initial →
      ProgrammeSource.rawEvent (RoundEpisodeSource.run initial control n).model.source.input
        (ProgrammeHistory.visitAt initial.model.source.input cut).current =
      ProgrammeSource.rawEvent initial.model.source.input (ProgrammeHistory.visitAt initial.model.source.input cut).current := by
    intro cut inside
    calc
      _ = ProgrammeSource.rawEvent (RoundEpisodeSource.run initial control n).model.source.input
          (ProgrammeHistory.visitAt (RoundEpisodeSource.run initial control n).model.source.input cut).current :=
        congrArg (ProgrammeSource.rawEvent (RoundEpisodeSource.run initial control n).model.source.input) (prior.currents cut (by omega)).symm
      _ = _ := prior.words cut inside
  exact Native.Coupling.History.complete_accounts initial.model.source.code initial.model.source.input
    (RoundEpisodeSource.run initial control n).model.source.input prior.law prior.initial (boundary initial) events
    initial.model.source.body (RoundEpisodeSource.run initial control n).model.source.body rfl rfl ordinal earlier

theorem each_actual_next_retains_every_old_archive_record (state : State) (command : Command state) :
    ∃ added, (next state command).archive = state.archive ++ added := by
  cases generated : inspect state command.raw with
  | none => exact ⟨nativeArchive state command,by simp only [next,generated]⟩
  | some entry => exact ⟨nativeArchive state command ++ [.communication (communicationArchive state command entry)],
      by simp only [next,generated,List.append_assoc]⟩

theorem every_later_controller_receives_the_original_archive (initial : State) (control : Controller) (n : Nat) :
    ∃ added, (RoundEpisodeSource.run initial control n).archive = initial.archive ++ added := by
  induction n with
  | zero => exact ⟨[],(List.append_nil initial.archive).symm⟩
  | succ n prior =>
    obtain ⟨old,prior⟩ := prior
    obtain ⟨new,step⟩ := each_actual_next_retains_every_old_archive_record (RoundEpisodeSource.run initial control n) (control (RoundEpisodeSource.run initial control n))
    refine ⟨old ++ new,?_⟩
    calc
      _ = (RoundEpisodeSource.run initial control n).archive ++ new := step
      _ = (initial.archive ++ old) ++ new := congrArg (fun records => records ++ new) prior
      _ = _ := List.append_assoc _ _ _

def NativeConsumed (model : Bound) (ordinal : Nat) (disposition : Native.Authority.FullDisposition model ordinal) : Prop :=
  let runtime := (Native.Runtime.facade model.source).seed.advance (ordinal+1)
  disposition = Native.Authority.fullGenerate model ordinal ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (Native.Runtime.facade model.source).process.stateAt
      ((Native.Runtime.facade model.source).process.successor runtime.state)

theorem native_generated_consumed (model : Bound) (ordinal : Nat) :
    NativeConsumed model ordinal (Native.Authority.fullGenerate model ordinal) := by
  have rooted := (Native.Runtime.facade model.source).readoutAt_factorizes
    ((Native.Runtime.facade model.source).seed.advance (ordinal+1)) .responsibilities
  exact ⟨rfl,rooted.2.2.1,rooted.2.2.2.2⟩

theorem all_four_real_preparation_occurrences_consume_their_own_ledger_and_next
    (state : State) (command : Command state) :
    NativeConsumed (rawSource state command.raw) (MaterialRoundSource.depth state.model state.cut) (produce state command).rawDisposition ∧
    NativeConsumed (supplied state command.raw) (MaterialRoundSource.depth (rawSource state command.raw) (state.cut+1)) (produce state command).upstreamDisposition ∧
    NativeConsumed (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw))
      (MaterialRoundSource.depth (supplied state command.raw) (count state)) (produce state command).fuelDisposition ∧
    NativeConsumed (residual state command.raw) (MaterialRoundSource.depth (supplied state command.raw) (count state)+1) (produce state command).recoveryDisposition :=
  ⟨native_generated_consumed _ _,native_generated_consumed _ _,native_generated_consumed _ _,native_generated_consumed _ _⟩

theorem every_communication_attempt_consumes_native_responsibility_even_when_blocked
    (state : State) (command : Command state) (entry : RoundEpisodeSource.Entry state command.raw) (n : Nat) :
    let consumed := ControlResponsibility.produce entry.bound (input state command.raw entry) 0 (command.localRule entry)
      (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl n
    let runtime := ControlResponsibility.runtime entry.bound (input state command.raw entry) 0 (command.localRule entry)
      (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl n
    consumed.responsibility.current = Native.Authority.fullGenerate (actual state command entry)
      (ControlResponsibility.depth entry.bound 0 n) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (CommunicationRuntime.facade entry.bound (input state command.raw entry) 0 (command.localRule entry)
      (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl).process.stateAt
        ((CommunicationRuntime.facade entry.bound (input state command.raw entry) 0 (command.localRule entry)
          (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl).process.successor runtime.state) := by
  have rooted := ControlResponsibility.original_native_histories_and_root_next_are_consumed_together entry.bound
    (input state command.raw entry) 0 (command.localRule entry) (command.network entry) (vocabulary state command.raw entry)
    (encoding state command.raw entry) (reception state command.raw entry) rfl n
  exact ⟨rooted.1,rooted.2.2.2.1,rooted.2.2.2.2⟩

theorem every_completed_round_consumes_its_actual_payment_whole_ledger_and_next
    (state : State) (command : Command state) (entry : RoundEpisodeSource.Entry state command.raw)
    (value : Bool) (subject : ApplicationSubject.Subject (emitter state command.raw entry))
    (done : outcome state command entry = .decided value subject) :
    let consumed := ControlResponsibility.produce entry.bound (input state command.raw entry) 0 (command.localRule entry)
      (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl 0
    let runtime := ControlResponsibility.runtime entry.bound (input state command.raw entry) 0 (command.localRule entry)
      (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl 0
    (∃ item, (item,true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
      flowAt ((emitter state command.raw entry).code.law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt ((emitter state command.raw entry).code.law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      ((emitter state command.raw entry).code.law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade entry.bound (input state command.raw entry) 0 (command.localRule entry)
        (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl).process.stateAt
          ((CommunicationRuntime.facade entry.bound (input state command.raw entry) 0 (command.localRule entry)
            (command.network entry) (vocabulary state command.raw entry) (encoding state command.raw entry) (reception state command.raw entry) rfl).process.successor runtime.state) := by
  have paid := SubjectQuorum.decision_consumes_the_original_subject_payment_responsibility_and_next (vocabulary state command.raw entry)
    entry.bound (input state command.raw entry) 0 (command.localRule entry) (command.network entry) (encoding state command.raw entry)
    (reception state command.raw entry) rfl 0 6 6 (slot state command.raw entry) 1 value subject done
  have address : ApplicationSubject.originCut (emitter state command.raw entry) 0 (slot state command.raw entry) = 0 := by
    simp [ApplicationSubject.originCut,ApplicationSubject.baseRound]
  rw [address] at paid
  exact ⟨paid.2.1,paid.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeConsumer
