import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}

structure State (root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) where
 private mk ::
 actual : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
 lineage : Lineage root actual.model.source.code
 rows : List (RenewableCodeLineage.Row root)

def initial (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (genesis : Cursor bound.source.code)
 (parent : RecursiveSigningSource.State bound genesis) : State bound.source.code :=
 ⟨RenewableArchiveSource.initial bound genesis parent,Lineage.original,
  (parent.rows bound genesis).map (pack Lineage.original)⟩

def row (state : State root) (input : LocalCommandSource.Input) : RenewableCodeLineage.Row root :=
 pack state.lineage ((LocalCommandSource.observe state.actual.model state.actual.point input).row state.actual.model)

def additions (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root) :
 RenewableArchiveSource.Command → List (RenewableCodeLineage.Row root)
 | .execute inputs => ((RenewableArchiveSource.fresh state.actual inputs).rows state.actual.model).map (pack state.lineage)
 | .renew enabled accept =>
   (StageTrace.records (PaidInvocationSource.start state.actual.model.source.code contract state.actual.point)
    (PaidInvocationSource.stages state.actual.model.source.code contract enabled accept)).map
     (pack (.extended state.lineage (PaidInvocationSource.catalogue state.actual.model.source.code contract)))

def advance (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root)
 (command : RenewableArchiveSource.Command) : State root :=
 match command with
 | .execute inputs => ⟨RenewableArchiveSource.execute state.actual inputs,state.lineage,
    state.rows++additions contract state command⟩
 | .renew enabled accept => ⟨RenewableArchiveSource.renew contract state.actual enabled accept,
    .extended state.lineage (PaidInvocationSource.catalogue state.actual.model.source.code contract),
    state.rows++additions contract state command⟩

theorem advance_is_the_original_actual_command
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root) (command : RenewableArchiveSource.Command) :
 (advance contract state command).actual=RenewableArchiveSource.next contract state.actual command := by cases command <;> rfl

theorem advance_appends_only_actual_rows
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root) (command : RenewableArchiveSource.Command) :
 (advance contract state command).rows=state.rows++additions contract state command := by cases command <;> rfl

theorem executing_one_input_is_the_exact_checked_row
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root) (input : LocalCommandSource.Input) :
 (advance contract state (.execute [input])).rows=state.rows++[row state input] := rfl

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (scope : Scope) (value : Bool)

def observed (state : State root) (recipient : Fin root.sites) :=
 RenewableHistoryReception.scan vocabulary law origin past recipient state.rows 0 ⟨[],[]⟩

-- Targets come from actual original sends; aliases of one owner count once per recipient.
def targets : Finset (Fin root.sites × Party) :=
 (((HeaderTransport.wires vocabulary origin past).filter fun wire => decide
  (wire.ballot.scope=scope ∧ wire.ballot.choice=value)).map fun wire =>
   (wire.recipient,root.siteParty wire.ballot.key)).toFinset

def pending (state : State root) : Finset (Fin root.sites × Party) :=
 (targets vocabulary origin past scope value).filter fun task =>
  task.2∉ActorQuorum.support (observed vocabulary law origin past state task.1) scope value

def offer (state : State root) (task : Fin root.sites × LocalCommandSource.Input) : Bool :=
 match RenewableHistoryReception.incoming vocabulary origin past (row state task.2) with
 | none => false
 | some wire => match RenewableHistoryReception.check vocabulary law origin past task.1 (row state task.2)
    ((observed vocabulary law origin past state task.1).receipts.map fun receipt =>
     (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire with
   | .rejected _ => false
   | .accepted _ => decide ((task.1,root.siteParty wire.ballot.key)∈pending vocabulary law origin past scope value state ∧
      wire.ballot.scope=scope ∧ wire.ballot.choice=value)

def menu (state : State root) : List (Fin root.sites × LocalCommandSource.Input) :=
 (List.finRange root.sites).flatMap fun recipient =>
  (CommandWindowSource.menu state.actual.model).map fun input => (recipient,input)

def selected (state : State root) :=
 (menu state).find? (offer vocabulary law origin past scope value state)

def command (state : State root) (external : RenewableArchiveSource.Command) : RenewableArchiveSource.Command :=
 match selected vocabulary law origin past scope value state with
 | some task => .execute [task.2]
 | none => external

def step (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (state : State root)
 (external : RenewableArchiveSource.Command) : State root :=
 advance contract state (command vocabulary law origin past scope value state external)

def run (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (start : State root)
 (external : Nat → State root → RenewableArchiveSource.Command) : Nat → State root :=
 Nat.rec start fun index state => step vocabulary law origin past scope value contract state (external index state)

theorem an_actual_menu_opportunity_forces_a_selected_service
 (state : State root) (task : Fin root.sites × LocalCommandSource.Input)
 (registered : task∈menu state) (available : offer vocabulary law origin past scope value state task=true) :
 ∃ chosen, selected vocabulary law origin past scope value state=some chosen := by
 cases found : selected vocabulary law origin past scope value state with
 | some chosen => exact ⟨chosen,rfl⟩
 | none =>
   have absent := (List.find?_eq_none.mp found) task registered
   rw [available] at absent
   contradiction

theorem selected_service_is_registered_and_computed
 (state : State root) (task : Fin root.sites × LocalCommandSource.Input)
 (chosen : selected vocabulary law origin past scope value state=some task) :
 task∈menu state ∧ offer vocabulary law origin past scope value state task=true :=
 ⟨List.mem_of_find?_eq_some chosen,List.find?_some chosen⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionSource
