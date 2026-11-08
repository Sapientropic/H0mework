import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundArchive
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumConsumer
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Continuation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action)

abbrev Bound := Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Bool) (Instrument := Unit)
variable (old : Bound) (count : Nat)

abbrev depth := RoundArchive.depth old.source count
abbrev current := old.source.currentAt (depth old count+1)
def payment : Action := ⟨1,[],.reserve 1,[],.settle () 1 2 1⟩
abbrev fee := RenewedQuorumSource.fee false
def bill : ℚ := flowAt (old.source.code.law.debit (current old count) payment) 1 .service +
  2 * flowAt (old.source.code.law.debit (current old count) fee) 1 .service
def gap : ℚ := max 0 (bill old count - (current old count).stock 1 .service)
def arrival : List Action := if gap old count = 0 then [] else
  [⟨1,[],.reserve 1,[],.issue () 1 2 (gap old count)⟩,
   ⟨2,[],.reserve 2,[],.transfer 2 1 [(.service,gap old count)]⟩]

-- The native input executes even when refused. No new protocol clock or interface exists yet.
abbrev attempted : Bound :=
  ⟨old.base,old.scope,Machine.Continuation.extend old.source count (arrival old count),old.law_exact,old.task_exact⟩
abbrev nativeAttempt := Native.Authority.fullGenerate (attempted old count) (depth old count)
abbrev prepared := (attempted old count).source.currentAt (depth old count+2)
abbrev ready := RoundArchive.inspect old.source count (arrival old count) payment fee
abbrev Ready := RoundArchive.Ready old.source count (arrival old count) payment fee

theorem the_actual_input_preserves_the_old_endpoint_and_executes_its_own_word :
    ((attempted old count).source.actualExecution (depth old count)).submitted = arrival old count ∧
      ((attempted old count).source.actualExecution (depth old count)).before = current old count ∧
      prepared old count = old.source.code.law.next (current old count) (arrival old count) :=
  ⟨Machine.Continuation.submitted old.source count _,Machine.Continuation.before old.source count _,
    Machine.Continuation.actual_next old.source count _⟩

variable {old count}

abbrev bound (entry : Ready old count) : Bound :=
  ⟨old.base,old.scope,entry.source,old.law_exact,old.task_exact⟩

variable (old count) (entry : Ready old count)
abbrev code := (bound entry).source.code
abbrev emitter := (bound entry).source

-- Two owned actions and one reception are emitted from the new atomic payment task.
abbrev phases : List (List Action) := [[payment],[fee],[fee]]
abbrev window : Nat := 2 * (code old count entry).sites * phases.length
abbrev input : Input (code old count entry) := ⟨fun _ _ _ => none,window old count entry⟩

def protocol : Rule (code old count entry) :=
  ⟨⟨(emitter old count entry).reference,(emitter old count entry).reference_generated⟩,fun key _ =>
    if key.2 = 0 then ⟨some ⟨.activate 0,by simp [code,RoundArchive.code]⟩,
      by simp [ownMoves,code,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else if key.2 = 1 then ⟨some ⟨.send 0 0,by simp [code,RoundArchive.code]⟩,
      by simp [ownMoves,code,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else ⟨none,List.mem_cons_self⟩⟩

abbrev slot : Scope := ⟨(emitter old count entry).code.initial.round + (emitter old count entry).history.length+2,0,0⟩
abbrev vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => if port = .reserve 1 then some (slot old count entry,true) else none,fun current => current.round,.service⟩
abbrev ballot : OwnedAttestation.Ballot (emitter old count entry) := ⟨0,0,0,1,slot old count entry,true,1⟩
def encoding : AttestationTransport.Encoding (emitter old count entry) := fun signal =>
  if signal = 1 then some (ballot old count entry) else none
abbrev reception : AttestationReception.ReceptionLaw (emitter old count entry) := ⟨fun _ _ => slot old count entry,1⟩
abbrev environment := QueueScheduler.environment (emitter old count entry) (input old count entry) 0
abbrev observed := AttestationReception.run (emitter old count entry) (input old count entry) 0 (protocol old count entry)
  (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry) 0 (window old count entry)
abbrev outcome := SubjectQuorum.produce (emitter old count entry) (input old count entry) 0 (protocol old count entry)
  (environment old count entry) (vocabulary old count entry) (encoding old count entry) (reception old count entry)
  0 (window old count entry) (window old count entry) (slot old count entry) 1
abbrev actual := CommunicationRuntime.actualBound (bound entry) (input old count entry) 0 (protocol old count entry) (environment old count entry)

theorem source_birth_inherits_the_literal_arrival_successor :
    (emitter old count entry).code.historyCurrent (emitter old count entry).history = prepared old count := by
  have actual := RoundArchive.arrival_is_an_actual_new_raw_occurrence old.source count (arrival old count) payment fee entry
  have after := (emitter old count entry).next_is_actual (depth old count)
  have size : (emitter old count entry).history.length = depth old count+1 := by
    change (RoundArchive.history old.source count (arrival old count)).length = _
    rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length];rfl
  rw [actual.1] at after
  change (emitter old count entry).currentAt (depth old count+2) = _ at after
  have before := actual.2.1
  change (emitter old count entry).currentAt (depth old count+1) = _ at before
  rw [before] at after
  rw [← (emitter old count entry).original_history_current_is_actual,size]
  exact after.trans (the_actual_input_preserves_the_old_endpoint_and_executes_its_own_word old count).2.2.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundSource
