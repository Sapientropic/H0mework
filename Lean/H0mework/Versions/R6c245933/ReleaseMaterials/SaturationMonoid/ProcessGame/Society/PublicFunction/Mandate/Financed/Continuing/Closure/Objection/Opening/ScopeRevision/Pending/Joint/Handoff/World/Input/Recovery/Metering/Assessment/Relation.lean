import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Admission
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Runtime.Readback
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Event.Future.Expiry.Progress
namespace Full
abbrev Tensor := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.Tensor
end Full
noncomputable section

/-- A common earlier cut indexes both actual paths. Endpoints and their native
rows remain distinct, including debts born on only one branch. -/
structure Window (first : Packet) where
  packet : Packet
  native : Event.Evolution first packet

namespace Window
variable {first : Packet} (window : Window first)
def rows := Responsibility.census window.packet
def original (row : Responsibility.Row first) := Responsibility.transport window.native row

def terminal (row : Responsibility.Row first) (index : Nat) : Bool :=
  ((window.original row).state.slots[index]?).any Responsibility.isTerminal

def cost (actor : Bool) := Event.Costs.cost window.native actor
def account (side actor : Bool) (good : Good) := Event.Funding.account window.native side actor good
def stock (actor : Bool) (good : Good) := (current window.packet.1 window.packet.2.inputs).stock actor good

def actors : List Bool := [false,true]
def goods : List Good := [.feedstock,.service]

def EconomicNoWorse (new previous : Window first) (actor : Bool) (good : Good) : Prop :=
  new.cost actor (.operating good) ≤ previous.cost actor (.operating good) ∧
  new.cost actor (.debtPayment good) ≤ previous.cost actor (.debtPayment good) ∧
  new.cost actor .elapsed ≤ previous.cost actor .elapsed ∧
  new.account true actor good ≤ previous.account true actor good ∧
  new.account false actor good ≤ previous.account false actor good ∧
  previous.stock actor good ≤ new.stock actor good

instance (new previous : Window first) (actor : Bool) (good : Good) :
    Decidable (EconomicNoWorse new previous actor good) := by unfold EconomicNoWorse;infer_instance

/-- Original slots are aligned by their actual native transport, not by the
index of a final census. New births stay in each endpoint's complete census. -/
def NoWorse (new previous : Window first) : Prop :=
  (∀ row ∈ Responsibility.census first,∀ index ∈ List.range row.state.slots.length,
    previous.terminal row index = true → new.terminal row index = true) ∧
  ∀ actor ∈ actors,∀ good ∈ goods,EconomicNoWorse new previous actor good

instance (new previous : Window first) : Decidable (NoWorse new previous) := by unfold NoWorse;infer_instance

theorem noWorse_refl : NoWorse window window := by
  refine ⟨fun _ _ _ _ yes => yes,?_⟩
  intro actor _ good _
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem noWorse_trans {new middle previous : Window first}
    (left : NoWorse new middle) (right : NoWorse middle previous) : NoWorse new previous := by
  refine ⟨fun row member index inside yes => left.1 row member index inside (right.1 row member index inside yes),?_⟩
  intro actor member good inside
  rcases left.2 actor member good inside with ⟨a,b,c,d,e,f⟩
  rcases right.2 actor member good inside with ⟨g,h,i,j,k,l⟩
  exact ⟨a.trans g,b.trans h,c.trans i,d.trans j,e.trans k,l.trans f⟩

theorem all_native_rows_are_present (row : Responsibility.Row window.packet) : row ∈ window.rows :=
  Responsibility.every_original_row_is_in_the_census row

theorem original_admission_history_and_complete_run (row : Responsibility.Row first) :
    (window.original row).row.origin = row.origin ∧
    row.state.history <+: (window.original row).state.history ∧
    Nonempty ((window.original row).native.Run row.origin.initial (window.original row).state) :=
  ⟨(Responsibility.every_actual_step_retains_its_original_admission_and_history window.native row).1,
    (Responsibility.every_actual_step_retains_its_original_admission_and_history window.native row).2,
    ⟨(window.original row).complete⟩⟩

theorem a_reported_terminal_has_its_actual_archive (row : Responsibility.Row first) (index : Nat)
    (reported : window.terminal row index = true) :
    ∃ archive,(window.original row).state.slots[index]? = some (.terminal archive) := by
  unfold terminal at reported
  cases present : (window.original row).state.slots[index]? with
  | none => simp only [present,Option.any_none,Bool.false_eq_true] at reported
  | some value =>
      cases value with
      | live obligation => simp only [present,Option.any_some,Responsibility.isTerminal,Bool.false_eq_true] at reported
      | terminal archive => exact ⟨archive,rfl⟩

theorem all_original_financial_slots_share_the_same_net_window (actor : Bool) (good : Good) :
    window.account true actor good + window.account false actor good =
      Event.FinancialBalance.quotedNet first actor good - Event.FinancialBalance.quotedNet window.packet actor good :=
  Event.Funding.actual_net_position_change window.native actor good
end Window

variable {first : Packet}
def reportWindow (seed : Window first) (word : List Action) (report : Report seed.packet.2 word) : Window first :=
  ⟨report.packet,report.native seed.native⟩

def jointWindowWith (seed : Window first) (word : List Action) (report : Report seed.packet.2 word)
    (disposition : Challenge.Redress.Shared.Iteration.Step report.packet.2) : Window first :=
  ⟨disposition.packet,.append (report.native seed.native) disposition.native⟩

/-- The comparison reaches this report's original joint source and its own next,
including all costs and new responsibilities of that actual disposition. -/
def jointWindow (seed : Window first) (word : List Action) (report : Report seed.packet.2 word) : Window first :=
  jointWindowWith seed word report (Challenge.Redress.Shared.Iteration.produce report.packet.2)

theorem joint_endpoint_is_the_original_received_source (seed : Window first) (word : List Action) :
    (jointWindow seed word (Runtime.read seed.packet.2 word)).packet =
      (Challenge.Redress.Shared.Iteration.Requests.produce
        (Challenge.Redress.Shared.Iteration.Requests.initial seed.packet) word).next.saved := by
  simp only [jointWindow,jointWindowWith,Challenge.Redress.Shared.Iteration.Requests.produce,
    Challenge.Redress.Shared.Iteration.Requests.initial,Challenge.Redress.Shared.Iteration.Requests.submitted,
    Challenge.Redress.Shared.Iteration.Requests.Result.next,List.nil_append]

def JointNoWorse (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) : Prop :=
  Window.NoWorse (jointWindow new word current) (jointWindow previous word old)

instance (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) :
    Decidable (JointNoWorse new previous word current old) := by unfold JointNoWorse;infer_instance

namespace ScopeForecast
abbrev Cursor := Challenge.Redress.Shared.Iteration.Requests.Cursor
abbrev Result := Challenge.Redress.Shared.Iteration.Requests.Result

def intents : List Input.Intent := TaskSource.ports

theorem every_native_port_is_included (intent : Input.Intent) : intent ∈ intents := by
  exact TaskSource.every_port_is_included intent

def cursor (seed : Window first) (pending : List Action) : Cursor := ⟨seed.packet,pending⟩
def word (seed : Window first) (intent : Input.Intent) := Input.emit seed.packet.2 intent
abbrev Port (seed : Window first) (pending : List Action) (intent : Input.Intent) :=
  Result (cursor seed pending) (word seed intent)

private def readPorts {seed : Window first} {pending : List Action}
    (admission : Port seed pending .admission) (challenge : Port seed pending .challenge)
    (exit : Port seed pending .exit) (renewal : Port seed pending .renewal)
    (revision : Port seed pending .revision) : (intent : Input.Intent) → Port seed pending intent
  | .admission => admission
  | .challenge => challenge
  | .exit => exit
  | .renewal => renewal
  | .revision => revision

/-- The five original source ports are evaluated separately and retained once.
They are actual request results, not supplied success or future certificates. -/
structure Forecast (seed : Window first) (pending : List Action) where
  private mk ::
  admission : Port seed pending .admission
  challenge : Port seed pending .challenge
  exit : Port seed pending .exit
  renewal : Port seed pending .renewal
  revision : Port seed pending .revision
  admissions : (intent : Input.Intent) →
    TaskSource.Admission (readPorts admission challenge exit renewal revision intent).next.saved.2
      (readPorts admission challenge exit renewal revision intent).next.pending

def generate (seed : Window first) (pending : List Action) : Forecast seed pending :=
  let admission := Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (word seed .admission)
  let challenge := Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (word seed .challenge)
  let exit := Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (word seed .exit)
  let renewal := Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (word seed .renewal)
  let revision := Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (word seed .revision)
  ⟨admission,challenge,exit,renewal,revision,fun intent =>
    let actual := readPorts admission challenge exit renewal revision intent
    TaskSource.admit actual.next.saved.2 actual.next.pending⟩

def Forecast.read {seed : Window first} {pending : List Action} (made : Forecast seed pending) :
    (intent : Input.Intent) → Port seed pending intent :=
  readPorts made.admission made.challenge made.exit made.renewal made.revision

def Forecast.taskAdmission {seed : Window first} {pending : List Action}
    (made : Forecast seed pending) (intent : Input.Intent) :
    TaskSource.Admission (made.read intent).next.saved.2 (made.read intent).next.pending :=
  made.admissions intent

theorem every_task_admission_is_the_original_new_scope_source {seed : Window first} {pending : List Action}
    (made : Forecast seed pending) (intent : Input.Intent) :
    (made.taskAdmission intent).result = Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source.seed
      (TaskSource.task (made.read intent).next.saved.2 (made.read intent).next.pending) :=
  (made.taskAdmission intent).generated

theorem each_port_is_generated_at_its_actual_scope (seed : Window first) (pending : List Action)
    (intent : Input.Intent) : (generate seed pending).read intent =
      Challenge.Redress.Shared.Iteration.Requests.produce (cursor seed pending) (Input.emit seed.packet.2 intent) := by
  cases intent <;> rfl

theorem the_original_residual_precedes_each_new_source_port (seed : Window first) (pending : List Action)
    (intent : Input.Intent) :
    Challenge.Redress.Shared.Iteration.Requests.submitted (cursor seed pending) (word seed intent) =
      pending ++ Input.emit seed.packet.2 intent := rfl

def after {seed : Window first} {pending : List Action} {intent : Input.Intent}
    (made : Port seed pending intent) : Window first :=
  ⟨made.next.saved,.append seed.native made.native⟩

/-- Task compilation may submit its source word at a fresh empty epoch. That
same preparation must enter the cost and whole-responsibility comparison. -/
def taskWindow {seed : Window first} {pending : List Action} {intent : Input.Intent}
    (made : Port seed pending intent) : Window first :=
  ⟨⟨made.next.saved.1,TaskSource.prepared made.next.saved.2⟩,
    .append (.append seed.native made.native) (TaskSource.preparation made.next.saved.2)⟩

theorem task_window_is_the_exact_prepared_packet {seed : Window first} {pending : List Action}
    {intent : Input.Intent} (made : Port seed pending intent) :
    (taskWindow made).packet = ⟨made.next.saved.1,TaskSource.prepared made.next.saved.2⟩ := rfl

def PortNoWorse {new previous : Window first} {pending oldPending : List Action}
    {intent : Input.Intent} (made : Port new pending intent) (old : Port previous oldPending intent) : Prop :=
  (old.report.residual = [] → made.report.residual = []) ∧
    Window.NoWorse (after made) (after old) ∧
    Distributed.Reaction.Native.Future.Recovery.Funding.NoWorse made.report.funding old.report.funding

instance {new previous : Window first} {pending oldPending : List Action}
    {intent : Input.Intent} (made : Port new pending intent) (old : Port previous oldPending intent) :
    Decidable (PortNoWorse made old) := by
  unfold PortNoWorse Distributed.Reaction.Native.Future.Recovery.Funding.NoWorse
  infer_instance

def NoWorse {new previous : Window first} {pending oldPending : List Action}
    (made : Forecast new pending) (old : Forecast previous oldPending) : Prop :=
  ∀ intent ∈ intents, PortNoWorse (made.read intent) (old.read intent) ∧
    Window.NoWorse (taskWindow (made.read intent)) (taskWindow (old.read intent)) ∧
    TaskSource.Admission.NoWorse (made.taskAdmission intent) (old.taskAdmission intent)

instance {new previous : Window first} {pending oldPending : List Action}
    (made : Forecast new pending) (old : Forecast previous oldPending) : Decidable (NoWorse made old) := by
  unfold NoWorse;infer_instance

/-- Each port reserves its Report, joint disposition, actual Task compilation
and original source admission. These are declared service units. -/
def services : Nat := 4 * intents.length

theorem exact_services : services = 20 := rfl
end ScopeForecast

def scopeForecast (seed : Window first) (word : List Action) (report : Report seed.packet.2 word) :=
  ScopeForecast.generate (jointWindow seed word report) report.residual

def ScopeNoWorse (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) : Prop :=
  ScopeForecast.NoWorse (scopeForecast new word current) (scopeForecast previous word old)

instance (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) :
    Decidable (ScopeNoWorse new previous word current old) := by unfold ScopeNoWorse;infer_instance

def ReportNoWorse (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) : Prop :=
  current.residual.length ≤ old.residual.length ∧
    Window.NoWorse (reportWindow new word current) (reportWindow previous word old)

instance (new previous : Window first) (word : List Action)
    (current : Report new.packet.2 word) (old : Report previous.packet.2 word) :
    Decidable (ReportNoWorse new previous word current old) := by unfold ReportNoWorse;infer_instance

abbrev Reports (first : Packet) := Full.Tensor (Window first) (List Action)
  (fun seed word => Report seed.packet.2 word)
  (fun seed word => Funding.Failure (Recovery.begin seed.packet.2 word))

/-- Both the full report and its refusal are read from one original Stage. -/
def tensor (seed : Window first) : Reports first :=
  ⟨seed,fun word => let actual := Runtime.read seed.packet.2 word
    some (actual,actual.funding)⟩

abbrev Accepts (required : List (List Action)) (new previous : Window first) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.Accepts
    Window.NoWorse ReportNoWorse required (tensor new) (tensor previous)

def inspect (required : List (List Action)) (new previous : Window first) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.inspect
    Window.NoWorse ReportNoWorse required (tensor new) (tensor previous)

theorem every_source_is_self_accepted (required : List (List Action)) (seed : Window first) :
    Accepts required seed seed := by
  refine ⟨Window.noWorse_refl seed,?_,fun _ _ yes => yes⟩
  intro word _
  exact ⟨le_rfl,Window.noWorse_refl _⟩

theorem accepted_preserves_complete_original_requests (required : List (List Action)) (new previous : Window first)
    (accepted : Accepts required new previous) (word : List Action) (member : word ∈ required)
    (finished : (Runtime.read previous.packet.2 word).residual = []) :
    (Runtime.read new.packet.2 word).residual = [] := by
  have smaller := (accepted.2.1 word member).1
  rw [finished,List.length_nil] at smaller
  cases pending : (Runtime.read new.packet.2 word).residual with
  | nil => rfl
  | cons head tail => rw [pending,List.length_cons] at smaller;omega

theorem each_future_keeps_every_original_row_and_its_original_response
    (required : List (List Action)) (new previous : Window first) (word : List Action) (_member : word ∈ required) :
    (∀ row : Responsibility.Row first,
      Nonempty (((reportWindow new word (Runtime.read new.packet.2 word)).original row).native.Run
        row.origin.initial ((reportWindow new word (Runtime.read new.packet.2 word)).original row).state) ∧
      Nonempty (((reportWindow previous word (Runtime.read previous.packet.2 word)).original row).native.Run
        row.origin.initial ((reportWindow previous word (Runtime.read previous.packet.2 word)).original row).state)) ∧
    (Runtime.read new.packet.2 word).packet = Metering.Runtime.packet new.packet.2 word ∧
    (Runtime.read previous.packet.2 word).packet = Metering.Runtime.packet previous.packet.2 word := by
  exact ⟨fun row => ⟨⟨((reportWindow new word (Runtime.read new.packet.2 word)).original row).complete⟩,
      ⟨((reportWindow previous word (Runtime.read previous.packet.2 word)).original row).complete⟩⟩,
    (Runtime.read new.packet.2 word).is_the_original_billed_response,
    (Runtime.read previous.packet.2 word).is_the_original_billed_response⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation
