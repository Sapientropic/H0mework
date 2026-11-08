import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action)
abbrev Bound := FinancedRoundSource.Bound

variable (old : Bound) (count : Nat) (incoming : List Action)
abbrev depth := Machine.Continuation.depth old.source count
abbrev before := old.source.currentAt (depth old count+1)
abbrev supplied : Bound :=
  ⟨old.base,old.scope,Machine.Continuation.extend old.source count incoming,old.law_exact,old.task_exact⟩
abbrev suppliedCount := count+1
abbrev afterInput := (supplied old count incoming).source.currentAt (depth old count+2)
def recovery : List Action := if RenewedQuorumMaterial.Inputs (afterInput old count incoming) then RenewedQuorumMaterial.word else []
abbrev attempted : Bound :=
  ⟨old.base,old.scope,Machine.Continuation.extend (supplied old count incoming).source (suppliedCount count)
    (recovery old count incoming),old.law_exact,old.task_exact⟩
abbrev prepared := (attempted old count incoming).source.currentAt (depth old count+3)
abbrev payment := FinancedRoundSource.payment
abbrev fee := FinancedRoundSource.fee
abbrev archive := RoundArchive.inspect (supplied old count incoming).source (suppliedCount count)
  (recovery old count incoming) payment fee
abbrev Archive := RoundArchive.Ready (supplied old count incoming).source (suppliedCount count)
  (recovery old count incoming) payment fee

def phasesAdmitted : Bool := decide (old.source.code.law.Valid (prepared old count incoming) payment ∧
  old.source.code.law.Valid (old.source.code.law.step (prepared old count incoming) payment) fee ∧
  old.source.code.law.Valid (old.source.code.law.step (old.source.code.law.step (prepared old count incoming) payment) fee) fee)

structure Ready : Type where
  private mk ::
  history : Archive old count incoming
  admitted : phasesAdmitted old count incoming = true

def inspect : Option (Ready old count incoming) := match archive old count incoming with
  | none => none
  | some history => if admitted : phasesAdmitted old count incoming then some ⟨history,admitted⟩ else none

inductive Preparation where | historyRefused | phaseRefused | ready
  deriving DecidableEq

def preparation : Preparation := match archive old count incoming with
  | none => .historyRefused
  | some _ => if phasesAdmitted old count incoming then .ready else .phaseRefused

theorem the_incoming_and_recovery_are_literal_successive_actual_occurrences :
    ((supplied old count incoming).source.actualExecution (depth old count)).submitted = incoming ∧
      ((supplied old count incoming).source.actualExecution (depth old count)).before = before old count ∧
      afterInput old count incoming = old.source.code.law.next (before old count) incoming ∧
      ((attempted old count incoming).source.actualExecution (depth old count+1)).submitted = recovery old count incoming ∧
      ((attempted old count incoming).source.actualExecution (depth old count+1)).before = afterInput old count incoming ∧
      prepared old count incoming = old.source.code.law.next (afterInput old count incoming) (recovery old count incoming) := by
  have one := Machine.Continuation.actual_next old.source count incoming
  have two := Machine.Continuation.actual_next (supplied old count incoming).source (suppliedCount count) (recovery old count incoming)
  exact ⟨Machine.Continuation.submitted old.source count incoming,Machine.Continuation.before old.source count incoming,
    one,Machine.Continuation.submitted (supplied old count incoming).source (suppliedCount count) _,
    Machine.Continuation.before (supplied old count incoming).source (suppliedCount count) _,two⟩

theorem primitive_material_inputs_generate_the_actual_recovery
    (same : old.source.code.law = RenewedQuorumMaterial.law)
    (inputs : RenewedQuorumMaterial.Inputs (afterInput old count incoming)) :
    prepared old count incoming = RenewedQuorumMaterial.successor (afterInput old count incoming) ∧
      (∀ item ∈ old.source.code.law.rawItems (afterInput old count incoming) (recovery old count incoming),
        old.source.code.law.Valid item.before item.request) := by
  have actual := (the_incoming_and_recovery_are_literal_successive_actual_occurrences old count incoming).2.2.2.2.2
  rw [recovery,if_pos inputs,same,RenewedQuorumMaterial.actual_next _ inputs] at actual
  refine ⟨actual,?_⟩
  rw [recovery,if_pos inputs,same]
  exact RenewedQuorumMaterial.actual_items _ inputs

variable {old count incoming}
abbrev Ready.bound (entry : Ready old count incoming) : Bound := ⟨old.base,old.scope,entry.history.source,old.law_exact,old.task_exact⟩
variable (old count incoming) (entry : Ready old count incoming)
abbrev emitter := entry.bound.source
abbrev code := (emitter old count incoming entry).code
abbrev input : Input (code old count incoming entry) := ⟨fun _ _ _ => none,6⟩
def protocol : Rule (code old count incoming entry) :=
  ⟨⟨(emitter old count incoming entry).reference,(emitter old count incoming entry).reference_generated⟩,fun key _ =>
    if key.2 = 0 then ⟨some ⟨.activate 0,by simp [code,RoundArchive.code]⟩,
      by simp [ownMoves,code,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else if key.2 = 1 then ⟨some ⟨.send 0 0,by simp [code,RoundArchive.code]⟩,
      by simp [ownMoves,code,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else ⟨none,List.mem_cons_self⟩⟩
abbrev slot : Scope := ⟨(emitter old count incoming entry).code.initial.round+(emitter old count incoming entry).history.length+2,0,0⟩
abbrev vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => if port = .reserve 1 then some (slot old count incoming entry,true) else none,fun current => current.round,.service⟩
abbrev ballot : OwnedAttestation.Ballot (emitter old count incoming entry) := ⟨0,0,0,1,slot old count incoming entry,true,1⟩
def encoding : AttestationTransport.Encoding (emitter old count incoming entry) := fun signal =>
  if signal = 1 then some (ballot old count incoming entry) else none
abbrev reception : AttestationReception.ReceptionLaw (emitter old count incoming entry) := ⟨fun _ _ => slot old count incoming entry,1⟩
abbrev environment := QueueScheduler.environment (emitter old count incoming entry) (input old count incoming entry) 0
abbrev outcome := SubjectQuorum.produce (emitter old count incoming entry) (input old count incoming entry) 0
  (protocol old count incoming entry) (environment old count incoming entry) (vocabulary old count incoming entry)
  (encoding old count incoming entry) (reception old count incoming entry) 0 6 6 (slot old count incoming entry) 1
abbrev actual := CommunicationRuntime.actualBound entry.bound (input old count incoming entry) 0
  (protocol old count incoming entry) (environment old count incoming entry)

theorem new_birth_inherits_the_exact_material_successor :
    (emitter old count incoming entry).code.historyCurrent (emitter old count incoming entry).history = prepared old count incoming := by
  have actual := RoundArchive.arrival_is_an_actual_new_raw_occurrence (supplied old count incoming).source
    (suppliedCount count) (recovery old count incoming) payment fee entry.history
  have after := (emitter old count incoming entry).next_is_actual (depth old count+1)
  have size : (emitter old count incoming entry).history.length = depth old count+2 := by
    change (RoundArchive.history (supplied old count incoming).source (suppliedCount count) (recovery old count incoming)).length = _
    rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length];rfl
  change ((emitter old count incoming entry).actualExecution (depth old count+1)).submitted = _ ∧
    ((emitter old count incoming entry).actualExecution (depth old count+1)).before = _ ∧ _ at actual
  rw [actual.1] at after
  change (emitter old count incoming entry).currentAt (depth old count+3) = _ at after
  have before := actual.2.1
  change (emitter old count incoming entry).currentAt (depth old count+2) = _ at before
  rw [before] at after
  rw [← (emitter old count incoming entry).original_history_current_is_actual,size]
  exact after.trans (the_incoming_and_recovery_are_literal_successive_actual_occurrences old count incoming).2.2.2.2.2.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundSource
