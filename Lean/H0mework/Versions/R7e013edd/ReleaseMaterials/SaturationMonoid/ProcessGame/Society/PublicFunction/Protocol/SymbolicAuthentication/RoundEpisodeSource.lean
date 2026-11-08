import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Action)
open MaterialRoundSource (Bound)

structure CommunicationArchive where
  private mk ::
  model : Bound
  input : Input model.source.code
  protocol : Rule model.source.code
  rival : Opponent model.source.code
  vocabulary : OwnedAttestation.Vocabulary (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)
  encoding : AttestationTransport.Encoding model.source
  reception : AttestationReception.ReceptionLaw model.source
  scope : Scope
  receiver : Fin model.source.code.sites

-- The immutable actual parameters determine all three readouts, including rejected raw calls.
abbrev CommunicationArchive.trace (record : CommunicationArchive) :=
  ControlExecution.run record.model.source record.input 0 record.protocol record.rival 6
abbrev CommunicationArchive.census (record : CommunicationArchive) :=
  CommunicationRuntime.generate record.model record.input 0 record.protocol record.rival
    record.vocabulary record.encoding record.reception 6
abbrev CommunicationArchive.decision (record : CommunicationArchive) :=
  SubjectQuorum.produce record.model.source record.input 0 record.protocol record.rival
    record.vocabulary record.encoding record.reception record.receiver 6 6 record.scope 1

inductive Archive where
  | native (model : Bound) (ordinal : Nat) (disposition : Native.Authority.FullDisposition model ordinal)
  | preparation (model : Bound) (count : Nat) (raw : List Action) (view : MaterialRoundSource.Preparation)
      (same : view = MaterialRoundSource.preparation model count raw)
  | communication (record : CommunicationArchive)

structure State where
  model : Bound
  cut : Nat
  archive : List Archive := []
abbrev boundary (state : State) := state.model.source.history.length+2+state.cut
abbrev current (state : State) := MaterialRoundSource.before state.model state.cut
abbrev rawSource (state : State) (raw : List Action) : Bound :=
  ⟨state.model.base,state.model.scope,Machine.Continuation.extend state.model.source state.cut raw,
    state.model.law_exact,state.model.task_exact⟩
abbrev supplied (state : State) (raw : List Action) := WorkerInputSource.arrived (rawSource state raw) (state.cut+1)
abbrev count (state : State) := state.cut+2
abbrev arrival (state : State) (raw : List Action) := FuelMaterialSource.incoming (supplied state raw) (count state)
abbrev residual (state : State) (raw : List Action) := MaterialRoundSource.attempted (supplied state raw) (count state) (arrival state raw)
abbrev Entry (state : State) (raw : List Action) := MaterialRoundSource.Ready (supplied state raw) (count state) (arrival state raw)
abbrev inspect (state : State) (raw : List Action) := MaterialRoundSource.inspect (supplied state raw) (count state) (arrival state raw)
abbrev emitter (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.emitter (supplied state raw) (count state) (arrival state raw) entry
abbrev input (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.input (supplied state raw) (count state) (arrival state raw) entry
abbrev vocabulary (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.vocabulary (supplied state raw) (count state) (arrival state raw) entry
abbrev encoding (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.encoding (supplied state raw) (count state) (arrival state raw) entry
abbrev reception (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.reception (supplied state raw) (count state) (arrival state raw) entry
abbrev slot (state : State) (raw : List Action) (entry : Entry state raw) := MaterialRoundSource.slot (supplied state raw) (count state) (arrival state raw) entry

-- These fields supply attempts and local programs, never a certificate or a future endpoint.
structure Command (state : State) where
  raw : List Action
  localRule : (entry : Entry state raw) → Rule (emitter state raw entry).code
  network : (entry : Entry state raw) → Opponent (emitter state raw entry).code

def normal (state : State) (raw : List Action := []) : Command state :=
  ⟨raw,fun entry => MaterialRoundSource.protocol (supplied state raw) (count state) (arrival state raw) entry,
    fun entry => QueueScheduler.environment (emitter state raw entry) (input state raw entry) 0⟩

abbrev actual (state : State) (command : Command state) (entry : Entry state command.raw) :=
  CommunicationRuntime.actualBound entry.bound (input state command.raw entry) 0
    (command.localRule entry) (command.network entry)
abbrev outcome (state : State) (command : Command state) (entry : Entry state command.raw) :=
  SubjectQuorum.produce (emitter state command.raw entry) (input state command.raw entry) 0
    (command.localRule entry) (command.network entry) (vocabulary state command.raw entry)
    (encoding state command.raw entry) (reception state command.raw entry) 0 6 6 (slot state command.raw entry) 1

structure Started (state : State) (command : Command state) (entry : Entry state command.raw) : Type where
  private mk ::
  trace : ControlExecution.State (emitter state command.raw entry)
  trace_exact : trace = ControlExecution.run (emitter state command.raw entry) (input state command.raw entry) 0
    (command.localRule entry) (command.network entry) 6
  census : CommunicationRuntime.Census entry.bound (input state command.raw entry) 0
    (command.localRule entry) (command.network entry) (vocabulary state command.raw entry)
    (encoding state command.raw entry) (reception state command.raw entry) 6
  census_exact : census = CommunicationRuntime.generate entry.bound (input state command.raw entry) 0
    (command.localRule entry) (command.network entry) (vocabulary state command.raw entry)
    (encoding state command.raw entry) (reception state command.raw entry) 6
  decision : SubjectQuorum.Result (emitter state command.raw entry)
  decision_exact : decision = outcome state command entry

def start (state : State) (command : Command state) (entry : Entry state command.raw) : Started state command entry :=
  ⟨ControlExecution.run (emitter state command.raw entry) (input state command.raw entry) 0
    (command.localRule entry) (command.network entry) 6,rfl,
    CommunicationRuntime.generate entry.bound (input state command.raw entry) 0
      (command.localRule entry) (command.network entry) (vocabulary state command.raw entry)
      (encoding state command.raw entry) (reception state command.raw entry) 6,rfl,outcome state command entry,rfl⟩

structure Result (state : State) (command : Command state) : Type where
  private mk ::
  rawDisposition : Native.Authority.FullDisposition (rawSource state command.raw) (MaterialRoundSource.depth state.model state.cut)
  raw_exact : rawDisposition = Native.Authority.fullGenerate (rawSource state command.raw) (MaterialRoundSource.depth state.model state.cut)
  upstreamDisposition : Native.Authority.FullDisposition (supplied state command.raw) (MaterialRoundSource.depth (rawSource state command.raw) (state.cut+1))
  upstream_exact : upstreamDisposition = Native.Authority.fullGenerate (supplied state command.raw) (MaterialRoundSource.depth (rawSource state command.raw) (state.cut+1))
  fuelDisposition : Native.Authority.FullDisposition
    (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw))
    (MaterialRoundSource.depth (supplied state command.raw) (count state))
  fuel_exact : fuelDisposition = Native.Authority.fullGenerate
    (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw))
    (MaterialRoundSource.depth (supplied state command.raw) (count state))
  recoveryDisposition : Native.Authority.FullDisposition (residual state command.raw)
    (MaterialRoundSource.depth (supplied state command.raw) (count state)+1)
  recovery_exact : recoveryDisposition = Native.Authority.fullGenerate (residual state command.raw)
    (MaterialRoundSource.depth (supplied state command.raw) (count state)+1)
  started : Option (Sigma fun entry : Entry state command.raw => Started state command entry)
  started_exact : started = (inspect state command.raw).map fun entry => ⟨entry,start state command entry⟩

def produce (state : State) (command : Command state) : Result state command :=
  ⟨Native.Authority.fullGenerate _ _,rfl,Native.Authority.fullGenerate _ _,rfl,
    Native.Authority.fullGenerate _ _,rfl,Native.Authority.fullGenerate _ _,rfl,
    (inspect state command.raw).map fun entry => ⟨entry,start state command entry⟩,rfl⟩

def status (state : State) (command : Command state) : MaterialRoundConsumer.Status :=
  match (produce state command).started with
  | none => match MaterialRoundSource.preparation (supplied state command.raw) (count state) (arrival state command.raw) with
    | .historyRefused => .historyRefused
    | _ => .phaseRefused
  | some next => match next.2.decision with
    | .blocked reason => .blocked reason
    | .decided value _ => .decided value

def nativeArchive (state : State) (command : Command state) : List Archive :=
  [.native (rawSource state command.raw) (MaterialRoundSource.depth state.model state.cut) (produce state command).rawDisposition,
   .native (supplied state command.raw) (MaterialRoundSource.depth (rawSource state command.raw) (state.cut+1)) (produce state command).upstreamDisposition,
   .native (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw))
     (MaterialRoundSource.depth (supplied state command.raw) (count state)) (produce state command).fuelDisposition,
   .native (residual state command.raw) (MaterialRoundSource.depth (supplied state command.raw) (count state)+1) (produce state command).recoveryDisposition,
   .preparation (supplied state command.raw) (count state) (arrival state command.raw)
     (MaterialRoundSource.preparation (supplied state command.raw) (count state) (arrival state command.raw)) rfl]

def communicationArchive (state : State) (command : Command state) (entry : Entry state command.raw) : CommunicationArchive :=
  ⟨entry.bound,input state command.raw entry,command.localRule entry,command.network entry,
    vocabulary state command.raw entry,encoding state command.raw entry,reception state command.raw entry,slot state command.raw entry,0⟩

def next (state : State) (command : Command state) : State :=
  match (inspect state command.raw) with
  | none => ⟨residual state command.raw,state.cut+4,state.archive ++ nativeArchive state command⟩
  | some entry => ⟨actual state command entry,6,state.archive ++ nativeArchive state command ++ [.communication (communicationArchive state command entry)]⟩

abbrev Controller := (state : State) → Command state
def run (initial : State) (control : Controller) : Nat → State :=
  Nat.rec initial fun _ state => next state (control state)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeSource
