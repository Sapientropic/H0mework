import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginHeader

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]

abbrev Bound := Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)
abbrev Contract := PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)

-- Contexts keep their original Code; a vocabulary extension cannot relabel old signatures.
structure Context where
 private mk ::
 model : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 origin : Cursor model.source.code
 stages : List (EventHistory.Stage (code := model.source.code))

def Context.ofSegment (model : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (segment : RecursiveSigningSource.Segment model) :
 Context (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨model,segment.origin,segment.stages⟩

variable (contract : Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

structure Window where
 private mk ::
 model : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 before : Cursor model.source.code
 terms : Contract (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 enabled : Bool
 accept : Bool

inductive Status where
 | opened
 | blocked (reason : PaidInvocationSource.Refusal)
 deriving DecidableEq

def Window.result (window : Window (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) :=
 PaidInvocationSource.produce window.model.source.code window.terms window.before window.enabled window.accept

def Window.point (window : Window (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) :
 Cursor (PaidInvocationSource.code window.model.source.code window.terms) :=
 match window.result with
 | .opened account => account.point
 | .blocked _ account => account.point

def Window.status (window : Window (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) : Status :=
 match window.result with
 | .opened _ => .opened
 | .blocked reason _ => .blocked reason

def Window.modelAfter (window : Window (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨window.model.base,window.model.scope,(window.point).source,
  window.model.law_exact,window.model.task_exact⟩

structure State where
 private mk ::
 model : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 point : Cursor model.source.code
 archive : List (Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 windows : List (Window (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def initial (model : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (genesis : Cursor model.source.code)
 (previous : RecursiveSigningSource.State model genesis) : State (Party := Party) (Good := Good)
 (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨model,previous.current model genesis,previous.archive.map (Context.ofSegment model),[]⟩

def fresh (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (inputs : List LocalCommandSource.Input) :=
 RecursiveSigningSource.segment state.model state.point (RecursiveSigningSource.initial state.model state.point) inputs

def execute (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (inputs : List LocalCommandSource.Input) : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨state.model,(fresh state inputs).final state.model,
  state.archive++[Context.ofSegment state.model (fresh state inputs)],state.windows⟩

def window (terms : Contract (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool) : Window (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨state.model,state.point,terms,enabled,accept⟩

def renew (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool) : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 let attempt := window contract state enabled accept
 ⟨attempt.modelAfter,attempt.point,
  state.archive++[⟨attempt.modelAfter,
   PaidInvocationSource.start state.model.source.code contract state.point,
   PaidInvocationSource.stages state.model.source.code contract enabled accept⟩],
  state.windows++[attempt]⟩

inductive Command where
 | execute (inputs : List LocalCommandSource.Input)
 | renew (enabled accept : Bool)

def next (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (command : Command) : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 match command with
 | .execute inputs => execute state inputs
 | .renew enabled accept => renew contract state enabled accept

def run (state : State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (control : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) → Command) : Nat → State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 Nat.rec state fun _ current => next contract current (control current)

theorem every_actual_command_keeps_all_original_issuing_contexts
 (state : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (command : Command) :
 state.archive <+: (next contract state command).archive ∧
 state.windows <+: (next contract state command).windows := by
 cases command with
 | execute inputs => exact ⟨List.prefix_append _ _,List.prefix_refl _⟩
 | renew enabled accept => exact ⟨List.prefix_append _ _,List.prefix_append _ _⟩

theorem arbitrary_later_control_keeps_the_original_archive_and_payment_history
 (state : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (control : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) → Command) (count : Nat) :
 state.archive <+: (RenewableArchiveSource.run contract state control count).archive ∧
 state.windows <+: (RenewableArchiveSource.run contract state control count).windows := by
 induction count with
 | zero => exact ⟨List.prefix_refl _,List.prefix_refl _⟩
 | succ count ih =>
   have step := every_actual_command_keeps_all_original_issuing_contexts contract
    (RenewableArchiveSource.run contract state control count) (control (RenewableArchiveSource.run contract state control count))
   exact ⟨ih.1.trans step.1,ih.2.trans step.2⟩

theorem admitted_payment_generates_the_exact_next_window
 (state : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool)
 (paid : PaidInvocationSource.admitted state.model.source.code contract state.point enabled accept=true) :
 (window contract state enabled accept).status=.opened ∧
 (renew contract state enabled accept).point=
  PaidInvocationRebase.cursor (PaidInvocationSource.paid state.model.source.code contract state.point enabled accept) contract.steps := by
 have generated := PaidInvocationSource.actual_admission_generates_the_paid_window
  state.model.source.code contract state.point enabled accept paid
 simp only [renew,window,Window.status,Window.point,Window.result,generated,PaidInvocationSource.opened]
 exact ⟨trivial,rfl⟩

theorem refused_payment_keeps_the_actual_attempt_endpoint_without_credit
 (state : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool)
 (unpaid : PaidInvocationSource.admitted state.model.source.code contract state.point enabled accept=false) :
 (window contract state enabled accept).status=.blocked .unpaid ∧
 (renew contract state enabled accept).point=
  PaidInvocationSource.paid state.model.source.code contract state.point enabled accept := by
 have refused := PaidInvocationSource.absent_payment_or_acceptance_cannot_open_the_window
  state.model.source.code contract state.point enabled accept unpaid
 simp only [renew,window,Window.status,Window.point,Window.result,refused,PaidInvocationSource.initial]
 exact ⟨trivial,rfl⟩

theorem every_new_ballot_uses_its_actual_funded_or_unfunded_execution_phase
 (state : State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (inputs : List LocalCommandSource.Input)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (ballot : StageBudget.Ballot (code := state.model.source.code))
 (issued : ballot ∈ StageBudget.ledger ((fresh state inputs).vocabulary state.model base)
  (fresh state inputs).origin (fresh state inputs).stages) :
 state.point.cut≤ballot.cut ∧ ballot.scope.phase=state.point.cut :=
 RecursiveSigningSource.each_new_ballot_is_born_in_its_own_actual_phase state.model base (fresh state inputs) ballot issued

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveSource
