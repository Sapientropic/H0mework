import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.Native
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.Reservation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

inductive BudgetChoice (prepared : Prepared input) where
  | source (original : SourceQuota.Generated prepared) (generated : original = SourceQuota.generate prepared)
  | explicit (units : Nat)
-- This public bootstrap split retains a share for dispatch; it is not a cross-fee optimum.
def BudgetChoice.units : BudgetChoice prepared → Nat
  | .explicit units => units
  | .source original _ => match original.result with
    | .domain catalogue => catalogue.bound/2
    | _ => 0

def budgetFor (prepared : Prepared input) : Option Nat → BudgetChoice prepared
  | none => .source (SourceQuota.generate prepared) rfl
  | some units => .explicit units

inductive Event (prepared : Prepared input) where
  | captured (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
  | operation (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (domain : source.result = .domain catalogue) (event : Incremental.Event catalogue)
inductive Program (prepared : Prepared input) (capacity : Nat) where
  | unavailable (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (outside : match source.result with | .domain _ => False | _ => True)
  | quoted (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (run : Incremental.Calculation catalogue (Incremental.initial catalogue) capacity)
      (actual : run = Incremental.execute catalogue capacity (Incremental.initial catalogue))

def Program.generate (prepared : Prepared input) (capacity : Nat) : Program prepared capacity :=
  let source := SourceQuota.generate prepared
  match domain : source.result with
  | .empty .. | .blocked .. => .unavailable source rfl (by rw [domain];trivial)
  | .domain catalogue => .quoted source rfl catalogue domain (Incremental.execute catalogue capacity (Incremental.initial catalogue)) rfl

def Program.events {capacity : Nat} : Program prepared capacity → List (Event prepared)
  | .unavailable source generated _ => [.captured source generated]
  | .quoted source generated catalogue domain run _ => .captured source generated::run.work.map (Event.operation source catalogue domain)
def Program.nativeLength {capacity : Nat} : Program prepared capacity → Nat
  | .unavailable .. => 0
  | .quoted _ _ _ _ run _ => run.work.length

theorem Program.event_count {capacity : Nat} (program : Program prepared capacity) : program.events.length = 1+program.nativeLength := by
  cases program <;> simp [events,nativeLength,List.length_map,Nat.add_comm]
theorem Program.native_fits {capacity : Nat} (program : Program prepared capacity) : program.nativeLength ≤ capacity := by
  cases program with
  | unavailable => exact Nat.zero_le _
  | quoted _ _ _ _ run _ => exact run.fits

def Program.finished {capacity : Nat} : Program prepared capacity → Bool
  | .unavailable .. => true
  | .quoted _ _ catalogue _ run _ => run.endpoint.finished catalogue

theorem Program.pending_spends_all {capacity : Nat} (program : Program prepared capacity) (pending : program.finished = false) : program.nativeLength = capacity := by
  cases program with
  | unavailable => cases pending
  | quoted source generated catalogue domain run actual =>
    dsimp only [finished] at pending
    dsimp only [nativeLength]
    rw [actual] at pending ⊢
    exact Incremental.unfinished_uses_all catalogue capacity _ pending

structure Started (prepared : Prepared input) where
  private mk ::
  budget : BudgetChoice prepared
  funding : EscrowBudget.Funding prepared budget.units
  funding_generated : funding = EscrowBudget.reserve prepared budget.units
  positive : budget.units ≠ 0
  paid : ∀ index : Index prepared,(funding.resultAt index).funded
  program : Program funding.installed (budget.units-1)
  generated : program = Program.generate funding.installed (budget.units-1)

namespace Started
variable (made : Started prepared)
def spent := made.program.events.length
def unused := made.budget.units-made.spent
theorem covered : made.spent ≤ made.budget.units := by
  have count := made.program.event_count
  have bound := made.program.native_fits
  have positive := made.positive
  dsimp only [spent]
  omega
theorem consumed_or_retained : made.spent+made.unused = made.budget.units := by
  have bound := made.covered
  dsimp only [unused];omega

def slot (index : Index prepared) (event : Fin made.spent) : Fin (((made.funding.resultAt index).invoice (made.paid index)).bill.units) :=
  ⟨event.val,by rw [((made.funding.resultAt index).invoice (made.paid index)).size];exact event.isLt.trans_le made.covered⟩
theorem slots_are_distinct (index : Index prepared) : Function.Injective (made.slot index) := by
  intro left right same
  have values := congrArg (fun slot : Fin (((made.funding.resultAt index).invoice (made.paid index)).bill.units) => slot.val) same
  exact Fin.ext values
theorem every_quote_event_uses_the_original_successful_invoice (index : Index prepared) (event : Fin made.spent) :
    ((made.funding.resultAt index).invoice (made.paid index)).bill.payment.succeeded = true ∧ (made.slot index event).val = event.val :=
  ⟨((made.funding.resultAt index).invoice (made.paid index)).paid,rfl⟩
theorem pending_has_no_unused_quote_credit (pending : made.program.finished = false) : made.spent = made.budget.units ∧ made.unused = 0 := by
  have full := made.program.pending_spends_all pending
  have count := made.program.event_count
  have positive := made.positive
  dsimp only [spent,unused]
  omega

def captureEvent : Fin made.spent := ⟨0,by have count := made.program.event_count;dsimp only [spent];omega⟩
def nativeEvent (event : Fin made.program.nativeLength) : Fin made.spent :=
  ⟨event.val+1,by have count := made.program.event_count;have inside := event.isLt;dsimp only [spent];omega⟩
theorem capture_and_native_never_reuse_a_slot (index : Index prepared) (event : Fin made.program.nativeLength) :
    made.slot index made.captureEvent ≠ made.slot index (made.nativeEvent event) := by
  intro same
  have values := congrArg Fin.val same
  change 0 = event.val+1 at values
  omega

theorem actual_quote_source_keeps_order_and_multiplicity : made.funding.installed.saved.map Cell.point = prepared.saved.map Cell.point := made.funding.source_order_and_multiplicity
end Started

variable {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
structure Dispatch (chosen : Incremental.Chosen catalogue) (position : Nat) where
  private mk ::
  payment : Reference.Payment.Funded prepared chosen.quota.val position
  generated : Reference.Payment.generate prepared chosen.quota.val position = .ready payment
  parent_finished : payment.parent.finished = true
  tail_finished : Allowance.finishedFor payment.parent.body.menu payment.parent.body.reports payment.tail = true

def dispatch (chosen : Incremental.Chosen catalogue) (position : Nat) : Dispatch catalogue chosen position :=
  match actual : Reference.Payment.generate prepared chosen.quota.val position with
  | .empty absent => False.elim (original_catalogue_is_nonempty catalogue absent)
  | .unpaid _funding generated index failed =>
      let same := chosen.approval.shape.funding_generated.trans generated.symm
      False.elim (failed (same ▸ chosen.approval.paid index))
  | .ready payment =>
      let finished := Allowance.quoted_source_bound_finishes_the_actual_execution chosen.approval.shape chosen.approval.enough payment
      ⟨payment,actual,finished.1,finished.2⟩

inductive Service (prepared : Prepared input) (position : Nat) where
  | retained
  | execution (source : SourceQuota.Generated prepared) (source_generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (chosen : Incremental.Chosen catalogue) (actual : Dispatch catalogue chosen position)

def deliver {capacity : Nat} (program : Program prepared capacity) (position : Nat) : Service prepared position :=
  match program with
  | .unavailable .. => .retained
  | .quoted source generated catalogue domain run _ => match run.endpoint.selection catalogue with
    | none => .retained
    | some chosen => .execution source generated catalogue domain chosen (dispatch catalogue chosen position)

def Service.after {position : Nat} : Service prepared position → Prepared input
  | .retained => prepared
  | .execution _ _ _ _ _ actual => actual.payment.parent.funding.installed
def Service.cursor {position : Nat} (service : Service prepared position) : (index : Index service.after) → Binding.NativeCursor service.after.saved[index].point := by
  cases service with
  | retained => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | execution source generated catalogue domain chosen actual =>
      exact Reference.Payment.endpointFor actual.payment.parent.body.menu actual.payment.parent.body.reports actual.payment.parent.run actual.payment.tail

inductive Result (prepared : Prepared input) (position : Nat) where
  | empty (budget : BudgetChoice prepared) (absent : prepared.saved = [])
  | unpaid (budget : BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (index : Index prepared) (failed : ¬ (funding.resultAt index).funded)
  | zero (budget : BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (paid : ∀ index : Index prepared,(funding.resultAt index).funded) (none : budget.units = 0)
  | started (made : Started prepared) (service : Service made.funding.installed position) (generated : service = deliver made.program position)

def generateFor (prepared : Prepared input) (budget : BudgetChoice prepared) (position : Nat) : Result prepared position :=
  if absent : prepared.saved = [] then .empty budget absent else
    let funding := EscrowBudget.reserve prepared budget.units
    match Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ failed => .unpaid budget funding rfl index failed
    | .accepted paid =>
      let all := fun index => paid index (List.mem_finRange _)
      if zero : budget.units = 0 then .zero budget funding rfl all zero else
        let program := Program.generate funding.installed (budget.units-1)
        let made : Started prepared := ⟨budget,funding,rfl,zero,all,program,rfl⟩
        .started made (deliver program position) rfl

def generate (prepared : Prepared input) (position : Nat) := generateFor prepared (budgetFor prepared none) position

def Result.after {position : Nat} : Result prepared position → Prepared input
  | .empty .. => prepared
  | .unpaid _ funding .. | .zero _ funding .. => funding.installed
  | .started _ service _ => service.after
def Result.cursor {position : Nat} (result : Result prepared position) : (index : Index result.after) → Binding.NativeCursor result.after.saved[index].point := by
  cases result with
  | empty => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | unpaid budget funding generated index failed => exact fun actual => Policy.Protocol.retained funding.installed.saved[actual].stage
  | zero budget funding generated paid none => exact fun index => Policy.Protocol.retained funding.installed.saved[index].stage
  | started made service generated => exact service.cursor

def Result.auditLaw {position : Nat} (result : Result prepared position) (index : Index result.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (result.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result prepared position
  project := fun _ {_} _ _ => result
namespace Attachment
noncomputable section
variable {original : Prepared input} {position : Nat} (audit : Result original position)
  {activeSource : SourceQuota.Generated audit.after} {activeCatalogue : SourceQuota.Catalogue activeSource.snapshot}
  {activeAll : Candidates activeSource activeCatalogue} {activeItems : List (Report activeAll)} (chosen : Selected activeItems) (index : Index audit.after)
  (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot chosen.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source)

def auditLaw : SourceNativeProjectionLaw
    (Responsibility.Canonical.Payment.Runtime.root chosen.policy.report.2 index chosen.policy.first (chosen.policy.paid index) component).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result original position
  project := fun _ {_} _ _ => audit

def root :=
  (Responsibility.Canonical.Payment.Runtime.root chosen.policy.report.2 index chosen.policy.first (chosen.policy.paid index) component).withProjectionCoface
    (auditLaw audit chosen index component)

def visitAt : (tick : Nat) → RootVisit (root audit chosen index component).toAuthoritativeRoot.toRoot
  | 0 => (root audit chosen index component).toAuthoritativeRoot.toRoot.initialVisit
  | tick+1 => (visitAt tick).next rfl
theorem visit_current (tick : Nat) : (visitAt audit chosen index component tick).current = tick := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg Nat.succ ih
def stateAt (tick : Nat) : SourceNativeLivingRootCurrentAt (Responsibility.Canonical.N chosen.policy.report.2 index) :=
  ⟨Responsibility.Canonical.V chosen.policy.report.2 index,root audit chosen index component,.finite (visitAt audit chosen index component tick)⟩
def process : SourceNativeLivingRootProcess (Responsibility.Canonical.N chosen.policy.report.2 index) where
  State := Nat
  stateAt := stateAt audit chosen index component
  stateAt_injective := by
    intro left right same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (Responsibility.Canonical.N chosen.policy.report.2 index) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents := eq_of_heq (Sigma.mk.inj labels).2
    change (visitAt audit chosen index component left).current = (visitAt audit chosen index component right).current at currents
    simpa only [visit_current] using currents
  initial := 0
  successorAt := fun tick => ⟨tick+1,rfl,HEq.rfl⟩
def facade : SourceNativeLivingRuntimeFacade (Responsibility.Canonical.N chosen.policy.report.2 index) where
  process := process audit chosen index component
  FaceAt := fun _ => (root audit chosen index component).toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun _ _ => (root audit chosen index component).toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => SourceNativeProjectionLaw.InstallationAt.refl _
  projectionAt := fun _ face => face
abbrev active := (facade audit chosen index component).seed
def read : Result original position :=
  match (facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()) with
  | .inl value => value.2
  | .inr impossible => impossible.elim
theorem the_actual_paid_quote_is_active_with_whole_ledger_and_next :
    read audit chosen index component = audit ∧
    HEq ((facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()))
      ((active audit chosen index component).tick.generated.projectionOutcome (.component ())) ∧
    HEq (active audit chosen index component).tick.generated.wholeLedgerWriteBack
      ((root audit chosen index component).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt 0) ∧
    (active audit chosen index component).tick.nextCurrent = stateAt audit chosen index component 1 := by
  have rooted := (facade audit chosen index component).readoutAt_factorizes (active audit chosen index component) (.component ())
  exact ⟨rfl,rooted.2.2.2.1,HEq.rfl,rooted.2.2.2.2⟩
def next : AuthorityCurrent :=
  ⟨Responsibility.Canonical.N chosen.policy.report.2 index,(active audit chosen index component).tick.nextCurrent⟩
end
end Attachment

private noncomputable def nextFor {original : Prepared input} {position : Nat} (audit : Result original position)
    (menu : DomainResult audit.after) (items : ReportsFor menu) {oldUnits : Nat}
    (parent : Prepayment.WorkFor menu items oldUnits) {capacity : Nat} (tail : Reference.Payment.WorkFor menu items parent position capacity) (index : Index audit.after)
    (component : SourceNativeProjectionLaw (Online.Runtime.root (Reference.Payment.endpointFor menu items parent tail index)).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent := by
  cases menu with
  | empty => exact originalNext (Reference.Payment.endpointFor _ items parent tail index) component
  | blocked => exact originalNext (Reference.Payment.endpointFor _ items parent tail index) component
  | ready source catalogue generated all =>
    cases chosen : tail.endpoint.selection items position with
    | none => exact originalNext (Reference.Payment.endpointFor _ items parent tail index) component
    | some answer =>
      have same : Reference.Payment.endpointFor (.ready source catalogue generated all) items parent tail index = answer.selected.policy.report.2.endpoint index := by
        dsimp only [Reference.Payment.endpointFor]
        rw [chosen]
      let original : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot answer.selected.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source :=
        Eq.mp (congrArg (fun value : Binding.NativeCursor audit.after.saved[index].point =>
          SourceNativeProjectionLaw (Online.Runtime.root value).toAuthoritativeRoot.toLedgerRoot.source) same) component
      exact Attachment.next audit answer.selected index original

noncomputable def Result.next {prepared : Prepared input} {position : Nat} (result : Result prepared position) (index : Index result.after) : AuthorityCurrent := by
  cases result with
  | empty budget absent => exact originalNext ((Result.empty budget absent).cursor index) ((Result.empty budget absent).auditLaw index)
  | unpaid budget funding generated failedAt failed =>
      exact originalNext ((Result.unpaid budget funding generated failedAt failed).cursor index) ((Result.unpaid budget funding generated failedAt failed).auditLaw index)
  | zero budget funding generated paid none =>
      exact originalNext ((Result.zero budget funding generated paid none).cursor index) ((Result.zero budget funding generated paid none).auditLaw index)
  | started made service generated =>
    cases service with
    | retained => exact originalNext ((Result.started made .retained generated).cursor index) ((Result.started made .retained generated).auditLaw index)
    | execution source sourceGenerated catalogue domain chosen actual =>
      let audit := Result.started made (.execution source sourceGenerated catalogue domain chosen actual) generated
      exact nextFor audit actual.payment.parent.body.menu actual.payment.parent.body.reports actual.payment.parent.run actual.payment.tail index (audit.auditLaw index)

structure Activation (input : Input seed) (override : Option Nat) (requested : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  budget : BudgetChoice preparation
  budget_generated : budget = budgetFor preparation override
  execution : Result preparation requested
  generated : execution = generateFor preparation budget requested
  bound : Binding.Linked execution.after point
  binding_generated : Binding.locate execution.after point = .linked bound
inductive Invocation (input : Input seed) (override : Option Nat) (requested : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input override requested point)
def invokeWith (input : Input seed) (override : Option Nat) (requested : Nat) (point : NativePoint input) : Invocation input override requested point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let budget := budgetFor preparation override
    let execution := generateFor preparation budget requested
    match linked : Binding.locate execution.after point with
    | .linked bound => .activated ⟨preparation,rfl,budget,rfl,execution,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed

def invoke (input : Input seed) (requested : Nat) (point : NativePoint input) : Invocation input none requested point :=
  invokeWith input none requested point
noncomputable def Activation.next {override : Option Nat} {requested : Nat} {point : NativePoint input} (made : Activation input override requested point) : AuthorityCurrent :=
  made.execution.next made.bound.index
theorem every_matching_actual_point_is_activated (input : Input seed) (override : Option Nat) (requested : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input override requested point,invokeWith input override requested point = .activated made := by
  unfold invokeWith
  rw [dif_pos observed]
  dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken exact_broken;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (override : Option Nat) (requested : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invokeWith input override requested point = .mismatch broken := by simp only [invokeWith,dif_neg broken]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.Reservation
