import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.Acquisition
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.Candidate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateRuntime
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


private def quotaList {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
    (limit : Nat) (bound : limit = catalogue.bound) : List catalogue.Quota :=
  (List.finRange (limit+1)).map fun quota => ⟨quota.val,by rw [← bound];exact quota.isLt⟩
private theorem quotaList_exact {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
    (limit : Nat) (bound : limit = catalogue.bound) : quotaList catalogue limit bound = catalogue.quotas := by
  subst limit
  simp only [quotaList,SourceQuota.Catalogue.quotas]
  exact List.map_id _
def initialCached {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
    (limit : Nat) (bound : limit = catalogue.bound) : CandidateDetailed.State catalogue :=
  .waiting [] (quotaList catalogue limit bound) (quotaList_exact catalogue limit bound) (by simp)

theorem initialCached_is_original {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
    (limit : Nat) (bound : limit = catalogue.bound) : initialCached catalogue limit bound = CandidateDetailed.initial catalogue := by
  unfold initialCached CandidateDetailed.initial
  congr 1
  exact quotaList_exact catalogue limit bound

inductive Event (prepared : Prepared input) where
  | opened
  | acquisition (event : SourceQuota.Acquisition.Event prepared)
  | enumerated (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (limit : Nat) (bound : limit = catalogue.bound)
  | operation (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (domain : source.result = .domain catalogue) (event : CandidateDetailed.Event catalogue)

inductive Tail : SourceQuota.Acquisition.State prepared → Nat → Type where
  | pending (state : SourceQuota.Acquisition.State prepared) (unfinished : state.done = false) (capacity : Nat) : Tail state capacity
  | unavailable (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (outside : match source.result with | .domain _ => False | _ => True) (capacity : Nat) :
      Tail (.finished (.unavailable source generated outside)) capacity
  | queued (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (limit : Nat) (bound : limit = catalogue.bound) (capacity : Nat) (zero : capacity = 0) :
      Tail (.finished (.domain source generated catalogue domain limit bound)) capacity
  | quoted (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (limit : Nat) (bound : limit = catalogue.bound) (capacity : Nat) (positive : capacity ≠ 0)
      (run : CandidateDetailed.Calculation catalogue (initialCached catalogue limit bound) (capacity-1))
      (actual : run = CandidateDetailed.execute catalogue (capacity-1) (initialCached catalogue limit bound)) :
      Tail (.finished (.domain source generated catalogue domain limit bound)) capacity

def Tail.generate (state : SourceQuota.Acquisition.State prepared) (capacity : Nat) : Tail state capacity :=
  match state with
  | .finished (.unavailable source generated outside) => .unavailable source generated outside capacity
  | .finished (.domain source generated catalogue domain limit bound) =>
      if zero : capacity = 0 then .queued source generated catalogue domain limit bound capacity zero
      else .quoted source generated catalogue domain limit bound capacity zero
        (CandidateDetailed.execute catalogue (capacity-1) (initialCached catalogue limit bound)) rfl
  | .observing .. | .validating .. | .seeding .. | .folding .. | .reducing .. => .pending _ rfl capacity

def Tail.events {state : SourceQuota.Acquisition.State prepared} {capacity : Nat} : Tail state capacity → List (Event prepared)
  | .pending .. | .unavailable .. | .queued .. => []
  | .quoted source _ catalogue domain limit bound _ _ run _ =>
      .enumerated source catalogue limit bound::run.work.map (Event.operation source catalogue domain)
def Tail.finished {state : SourceQuota.Acquisition.State prepared} {capacity : Nat} : Tail state capacity → Bool
  | .pending .. | .queued .. => false
  | .unavailable .. => true
  | .quoted _ _ catalogue _ _ _ _ _ run _ => run.endpoint.finished catalogue

theorem Tail.fits {state : SourceQuota.Acquisition.State prepared} {capacity : Nat} (tail : Tail state capacity) : tail.events.length ≤ capacity := by
  cases tail with
  | quoted source generated catalogue domain limit bound capacity positive run actual =>
      have fits := run.fits
      simp only [events,List.length_cons,List.length_map];omega
  | _ => exact Nat.zero_le _

structure Program (prepared : Prepared input) (capacity : Nat) where
  private mk ::
  acquisition : SourceQuota.Acquisition.Calculation (SourceQuota.Acquisition.initial prepared) capacity
  actual : acquisition = SourceQuota.Acquisition.execute capacity (SourceQuota.Acquisition.initial prepared)
  tail : Tail acquisition.endpoint (capacity-acquisition.work.length)
  generated : tail = Tail.generate acquisition.endpoint (capacity-acquisition.work.length)

def Program.generate (prepared : Prepared input) (capacity : Nat) : Program prepared capacity :=
  let acquisition := SourceQuota.Acquisition.execute capacity (SourceQuota.Acquisition.initial prepared)
  ⟨acquisition,rfl,Tail.generate acquisition.endpoint (capacity-acquisition.work.length),rfl⟩
def Program.events {capacity : Nat} (program : Program prepared capacity) : List (Event prepared) :=
  .opened::program.acquisition.work.map Event.acquisition ++ program.tail.events
def Program.nativeLength {capacity : Nat} (program : Program prepared capacity) :=
  program.acquisition.work.length+program.tail.events.length

theorem Program.event_count {capacity : Nat} (program : Program prepared capacity) : program.events.length = 1+program.nativeLength := by
  simp only [events,nativeLength,List.length_cons,List.length_append,List.length_map];omega
theorem Program.native_fits {capacity : Nat} (program : Program prepared capacity) : program.nativeLength ≤ capacity := by
  have a := program.acquisition.fits
  have b := program.tail.fits
  dsimp only [nativeLength];omega

def Program.finished {capacity : Nat} (program : Program prepared capacity) := program.tail.finished

theorem Tail.pending_account {state : SourceQuota.Acquisition.State prepared} {capacity : Nat}
    (tail : Tail state capacity) (pending : tail.finished = false) :
    (state.done = false ∧ tail.events = []) ∨ tail.events.length = capacity := by
  cases tail with
  | pending state unfinished left => exact .inl ⟨unfinished,rfl⟩
  | unavailable => cases pending
  | queued source same catalogue domain limit bound left zero => exact .inr zero.symm
  | quoted source same catalogue domain limit bound left positive run actual =>
      have used := CandidateDetailed.unfinished_uses_all catalogue (capacity-1) _ (by rw [← actual];exact pending)
      rw [← actual] at used
      apply Or.inr
      simp only [Tail.events,List.length_cons,List.length_map];omega

theorem Program.pending_spends_all {capacity : Nat} (program : Program prepared capacity)
    (pending : program.finished = false) : program.nativeLength = capacity := by
  rcases program.tail.pending_account pending with ⟨unfinished,empty⟩ | full
  · have used := SourceQuota.Acquisition.unfinished_uses_all capacity (SourceQuota.Acquisition.initial prepared) (by rw [← program.actual];exact unfinished)
    rw [← program.actual] at used
    simp only [nativeLength,empty,List.length_nil,Nat.add_zero];exact used
  · have fits := program.acquisition.fits
    dsimp only [nativeLength];omega

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

def openingEvent : Fin made.spent := ⟨0,by have count := made.program.event_count;dsimp only [spent];omega⟩
def nativeEvent (event : Fin made.program.nativeLength) : Fin made.spent :=
  ⟨event.val+1,by have count := made.program.event_count;have inside := event.isLt;dsimp only [spent];omega⟩
theorem opening_and_native_never_reuse_a_slot (index : Index prepared) (event : Fin made.program.nativeLength) :
    made.slot index made.openingEvent ≠ made.slot index (made.nativeEvent event) := by
  intro same
  have values := congrArg Fin.val same
  change 0 = event.val+1 at values
  omega

def acquisitionEvent (event : Fin made.program.acquisition.work.length) : Fin made.spent :=
  ⟨event.val+1,by have count := made.program.event_count;have inside := event.isLt;dsimp only [spent,Program.nativeLength] at *;omega⟩
def quotationEvent (event : Fin made.program.tail.events.length) : Fin made.spent :=
  ⟨event.val+1+made.program.acquisition.work.length,by have count := made.program.event_count;have inside := event.isLt;dsimp only [spent,Program.nativeLength] at *;omega⟩
theorem acquisition_and_quotation_never_reuse_a_slot (index : Index prepared)
    (first : Fin made.program.acquisition.work.length) (later : Fin made.program.tail.events.length) :
    made.slot index (made.acquisitionEvent first) ≠ made.slot index (made.quotationEvent later) := by
  intro same
  have values := congrArg Fin.val same
  change first.val+1 = later.val+1+made.program.acquisition.work.length at values
  have inside := first.isLt
  omega

theorem actual_quote_source_keeps_order_and_multiplicity : made.funding.installed.saved.map Cell.point = prepared.saved.map Cell.point := made.funding.source_order_and_multiplicity
end Started

variable {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
structure Dispatch (chosen : CandidateDetailed.Chosen catalogue) (position : Nat) where
  private mk ::
  payment : Reference.Payment.Funded prepared chosen.quota.val position
  generated : Reference.Payment.generate prepared chosen.quota.val position = .ready payment
  parent_finished : payment.parent.finished = true
  tail_finished : Allowance.finishedFor payment.parent.body.menu payment.parent.body.reports payment.tail = true

def dispatch (chosen : CandidateDetailed.Chosen catalogue) (position : Nat) : Dispatch catalogue chosen position :=
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
      (chosen : CandidateDetailed.Chosen catalogue) (actual : Dispatch catalogue chosen position)

def Tail.deliver {state : SourceQuota.Acquisition.State prepared} {capacity : Nat}
    (tail : Tail state capacity) (position : Nat) : Service prepared position :=
  match tail with
  | .pending .. | .unavailable .. | .queued .. => .retained
  | .quoted source generated catalogue domain _ _ _ _ run _ => match run.endpoint.selection catalogue with
    | none => .retained
    | some chosen => .execution source generated catalogue domain chosen (dispatch catalogue chosen position)
def deliver {capacity : Nat} (program : Program prepared capacity) (position : Nat) : Service prepared position :=
  program.tail.deliver position

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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateRuntime

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateRuntime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

/-- Paid quotation stops before dispatch; alternatives share this exact postouter source. -/
inductive Opening (prepared : Prepared input) where
  | empty (budget : BudgetChoice prepared) (absent : prepared.saved = [])
  | unpaid (budget : BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (index : Index prepared) (failed : ¬(funding.resultAt index).funded)
  | zero (budget : BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (paid : ∀ index : Index prepared,(funding.resultAt index).funded) (none : budget.units = 0)
  | started (outer : Started prepared)
def openFor (prepared : Prepared input) (budget : BudgetChoice prepared) : Opening prepared :=
  if absent : prepared.saved = [] then .empty budget absent else
    let funding := EscrowBudget.reserve prepared budget.units
    match Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ failed => .unpaid budget funding rfl index failed
    | .accepted paid =>
      let all := fun index => paid index (List.mem_finRange _)
      if zero : budget.units = 0 then .zero budget funding rfl all zero else
        let program := Program.generate funding.installed (budget.units-1)
        .started ⟨budget,funding,rfl,zero,all,program,rfl⟩
def Opening.deliver (opening : Opening prepared) (position : Nat) : Result prepared position :=
  match opening with
  | .empty budget absent => .empty budget absent
  | .unpaid budget funding generated index failed => .unpaid budget funding generated index failed
  | .zero budget funding generated paid zeroProof => .zero budget funding generated paid zeroProof
  | .started outer => .started outer (CandidateRuntime.deliver outer.program position) rfl
theorem opening_then_dispatch_is_the_original (prepared : Prepared input) (budget : BudgetChoice prepared) (position : Nat) :
    (openFor prepared budget).deliver position = generateFor prepared budget position := by
  unfold openFor generateFor
  split
  · rfl
  · dsimp only;split
    · rfl
    · split <;> rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateRuntime
