import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Refinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Reference
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}

structure Cache (items : List (Report all)) where
  private mk ::
  rows : List (Row all)
  complete : rows = directory items
  pool : List (Candidate all)
  pooled : pool = candidates items
def fromCursor {items : List (Report all)} : Machine.State items → Option (Cache items)
  | .reading .. => none
  | .searching rows complete pool pooled _ => some ⟨rows,complete,pool,pooled⟩
def Cache.anchor {items : List (Report all)} (cache : Cache items) (position : Nat) : Option (Candidate all) :=
  cache.rows[position]?.bind fun row => row.2.accept?
theorem Cache.anchor_is_listed {items : List (Report all)} (cache : Cache items) (position : Nat) (reference : Candidate all)
    (actual : cache.anchor position = some reference) : reference ∈ cache.pool := by
  cases found : cache.rows[position]? with
  | none => simp only [Cache.anchor,found,Option.bind_none] at actual;cases actual
  | some row =>
      have inside : row ∈ cache.rows := List.mem_of_getElem? found
      have accepted : row.2.accept? = some reference := by simpa only [Cache.anchor,found,Option.bind_some] using actual
      rw [cache.pooled]
      apply every_ready_entry_is_in_the_pool items row
      · rw [←cache.complete];exact inside
      · exact accepted

structure Choice (items : List (Report all)) (position : Nat) where
  private mk ::
  cache : Cache items
  reference : Candidate all
  source_position : cache.anchor position = some reference
  selected : Selected items
  no_worse : Distributed.NoWorse (axes all) cost selected.policy reference

theorem Choice.actual_strict_improvement {items : List (Report all)} {position : Nat} (answer : Choice items position)
    (available : ∃ other ∈ candidates items,Distributed.Improves (axes all) cost answer.reference other) :
    Distributed.Improves (axes all) cost answer.reference answer.selected.policy := by
  refine ⟨answer.no_worse,?_⟩
  intro backwards
  obtain ⟨other,inside,strict⟩ := available
  apply answer.selected.maximal other inside
  exact ⟨Distributed.noWorse_trans strict.1 backwards,fun reverse => strict.2 (Distributed.noWorse_trans backwards reverse)⟩
theorem Choice.full_responsibility {items : List (Report all)} {position : Nat} (answer : Choice items position) :
    ResponsibilityLe answer.selected.policy answer.reference := (vector_iff _ _).mp answer.no_worse

variable (items : List (Report all)) (position : Nat)
inductive State where
  | locating (cache : Cache items)
  | comparing (cache : Cache items) (reference : Candidate all) (actual : cache.anchor position = some reference)
      (current : Refinement.State cache.pool reference)
  | invalid (cache : Cache items) (absent : cache.anchor position = none)
  | parentPending (parent : Machine.State items) (incomplete : fromCursor parent = none)

def initial (parent : Machine.State items) : State items position :=
  match actual : fromCursor parent with
  | none => .parentPending parent actual
  | some cache => .locating cache
inductive Event where
  | referenceReady (cache : Cache items) (reference : Candidate all) (actual : cache.anchor position = some reference)
  | referenceInvalid (cache : Cache items) (actual : cache.anchor position = none)
  | native (pool : List (Candidate all)) (reference : Candidate all) (operation : Refinement.Event reference)
def move : State items position → Option (State items position × Event items position)
  | .invalid .. | .parentPending .. => none
  | .locating cache => match actual : cache.anchor position with
    | none => some (.invalid cache actual,.referenceInvalid cache actual)
    | some reference => some (.comparing cache reference actual (Refinement.initial cache.pool reference),.referenceReady cache reference actual)
  | .comparing cache reference actual current => match _looked : Refinement.move cache.pool reference current with
    | none => none
    | some (after,event) => some (.comparing cache reference actual after,.native cache.pool reference event)
def State.stopped : State items position → Bool
  | .invalid .. | .parentPending .. => true
  | .locating .. => false
  | .comparing cache reference _ current => current.finished cache.pool reference
def State.rank : State items position → Nat
  | .invalid .. | .parentPending .. => 0
  | .locating cache => cache.pool.length*((axes all).length+2)+Refinement.searchBound cache.pool+3
  | .comparing cache reference _ current => current.rank cache.pool reference
theorem step_progresses {before after : State items position} {event : Event items position}
    (actual : move items position before = some (after,event)) : after.rank items position < before.rank items position := by
  cases before with
  | invalid | parentPending => cases actual
  | locating cache =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual
      all_goals simp only [State.rank,Refinement.initial,Refinement.State.rank]
      all_goals omega
  | comparing cache reference source_position current =>
      dsimp only [move] at actual;split at actual
      · cases actual
      · rename_i after event looked
        cases Option.some.inj actual
        exact Refinement.step_progresses cache.pool reference looked
theorem stopped_iff_no_move (state : State items position) : move items position state = none ↔ state.stopped items position = true := by
  cases state with
  | invalid | parentPending => simp [move,State.stopped]
  | locating cache => dsimp only [move,State.stopped];split <;> simp
  | comparing cache reference actual current =>
    dsimp only [move,State.stopped];split
    · rename_i stopped;simp only [true_iff];exact (Refinement.stopped_iff_finished cache.pool reference current).mp stopped
    · rename_i after event looked
      simp only [reduceCtorEq,false_iff]
      intro finished
      have stopped := (Refinement.stopped_iff_finished cache.pool reference current).mpr finished
      rw [stopped] at looked;cases looked

def State.selection : State items position → Option (Choice items position)
  | .locating .. | .invalid .. | .parentPending .. => none
  | .comparing cache reference actual current => match current.resolution cache.pool reference with
    | none => none
    | some answer => some ⟨cache,reference,actual,⟨answer.selected.policy,(by rw [←cache.pooled];exact answer.selected.original),by
        intro other inside strict
        exact answer.selected.maximal other (by rw [cache.pooled];exact inside) strict⟩,answer.no_worse⟩

theorem stopped_valid_reference_has_a_choice (cache : Cache items) (reference : Candidate all) (actual : cache.anchor position = some reference)
    (current : Refinement.State cache.pool reference) (finished : current.finished cache.pool reference = true) :
    (State.selection items position (.comparing cache reference actual current)).isSome = true := by
  have found := Refinement.finished_with_listed_reference_has_a_resolution cache.pool reference
    (cache.anchor_is_listed position reference actual) current finished
  cases picked : current.resolution cache.pool reference with
  | none => rw [picked] at found;cases found
  | some answer => simp only [State.selection,picked,Option.isSome_some]

inductive Trace (items : List (Report all)) (position : Nat) : State items position → State items position → List (Event items position) → Prop
  | nil (before) : Trace items position before before []
  | step {before middle after event work} (actual : move items position before = some (middle,event))
      (later : Trace items position middle after work) : Trace items position before after (event::work)
structure Calculation (items : List (Report all)) (position : Nat) (before : State items position) (capacity : Nat) where
  private mk ::
  endpoint : State items position
  work : List (Event items position)
  history : Trace items position before endpoint work
  fits : work.length ≤ capacity
def execute : (capacity : Nat) → (before : State items position) → Calculation items position before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move items position before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩
theorem sufficient_source_rank_stops (capacity : Nat) (before : State items position) (enough : before.rank items position ≤ capacity) :
    (execute items position capacity before).endpoint.stopped items position = true := by
  induction capacity generalizing before with
  | zero =>
    cases before with
    | invalid | parentPending => rfl
    | locating => simp only [State.rank] at enough;omega
    | comparing cache reference actual current => exact Refinement.sufficient_source_rank_finishes cache.pool reference 0 current enough
  | succ capacity ih =>
    unfold execute;split
    · rename_i stopped;exact (stopped_iff_no_move items position before).mp stopped
    · rename_i after event actual
      exact ih after (by have smaller := step_progresses items position actual;omega)
theorem unfinished_uses_all (capacity : Nat) (before : State items position)
    (unfinished : (execute items position capacity before).endpoint.stopped items position = false) :
    (execute items position capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
    unfold execute at unfinished ⊢;split at unfinished
    · rename_i stopped;rw [(stopped_iff_no_move items position before).mp stopped] at unfinished;cases unfinished
    · rename_i after event actual;exact congrArg Nat.succ (ih after unfinished)


namespace Payment
def WorkFor {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {oldUnits : Nat} →
    Prepayment.WorkFor menu items oldUnits → (position capacity : Nat) → Type
  | .empty ..,_ ,_,_,_,_ | .blocked ..,_ ,_,_,_,_ => Unit
  | .ready ..,items,_,parent,position,capacity => Calculation items position (initial items position parent.endpoint) capacity
def runFor {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {oldUnits : Nat} →
    (parent : Prepayment.WorkFor menu items oldUnits) → (position capacity : Nat) → WorkFor menu items parent position capacity
  | .empty ..,_ ,_,_,_,_ | .blocked ..,_ ,_,_,_,_ => ()
  | .ready ..,items,_,parent,position,capacity => execute items position capacity (initial items position parent.endpoint)
def workLength {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {oldUnits : Nat} →
    {parent : Prepayment.WorkFor menu items oldUnits} → {position capacity : Nat} → WorkFor menu items parent position capacity → Nat
  | .empty ..,_ ,_,_,_,_,_ | .blocked ..,_ ,_,_,_,_,_ => 0
  | .ready ..,_ ,_,_,_,_,run => run.work.length
theorem fits {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) {oldUnits : Nat}
    (parent : Prepayment.WorkFor menu items oldUnits) (position capacity : Nat) (tail : WorkFor menu items parent position capacity) :
    workLength menu items tail ≤ capacity := by cases menu with
  | empty | blocked => exact Nat.zero_le _
  | ready => exact tail.fits

structure Funded (prepared : Prepared input) (units position : Nat) where
  private mk ::
  parent : Prepayment.Started prepared units
  parent_generated : Prepayment.generate prepared units = .started parent
  tail : WorkFor parent.body.menu parent.body.reports parent.run position parent.unused
  tail_generated : tail = runFor parent.body.menu parent.body.reports parent.run position parent.unused

inductive Result (prepared : Prepared input) (units position : Nat) where
  | empty (absent : prepared.saved = [])
  | unpaid (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (index : Index prepared) (failed : ¬ (funding.resultAt index).funded)
  | ready (made : Funded prepared units position)

def generate (prepared : Prepared input) (units position : Nat) : Result prepared units position :=
  match actual : Prepayment.generate prepared units with
  | .empty absent => .empty absent
  | .unpaid funding generated index failed => .unpaid funding generated index failed
  | .started parent => .ready ⟨parent,actual,runFor parent.body.menu parent.body.reports parent.run position parent.unused,rfl⟩
def Result.after {prepared : Prepared input} {units position : Nat} : Result prepared units position → Prepared input
  | .empty _ => prepared
  | .unpaid funding .. => funding.installed
  | .ready made => made.parent.funding.installed

namespace Funded
variable {prepared : Prepared input} {units position : Nat} (made : Funded prepared units position)
def spent := workLength made.parent.body.menu made.parent.body.reports made.tail
def unused := made.parent.unused-made.spent
theorem entire_invoice_is_consumed_or_retained : made.parent.spent+made.spent+made.unused = units := by
  have bound := fits made.parent.body.menu made.parent.body.reports made.parent.run position made.parent.unused made.tail
  have total := made.parent.consumed_or_retained
  dsimp only [spent,unused] at *
  omega
def slot (index : Index prepared) (event : Fin made.spent) :
    Fin (((made.parent.funding.resultAt index).invoice (made.parent.paid index)).bill.units) :=
  ⟨made.parent.spent+event.val,by
    rw [((made.parent.funding.resultAt index).invoice (made.parent.paid index)).size]
    have total := made.parent.consumed_or_retained
    have bound := fits made.parent.body.menu made.parent.body.reports made.parent.run position made.parent.unused made.tail
    have inside := event.isLt
    change event.val < workLength made.parent.body.menu made.parent.body.reports made.tail at inside
    omega⟩
theorem distinct_slots (index : Index prepared) : Function.Injective (made.slot index) := by
  intro left right same
  have values := congrArg Fin.val same
  dsimp only [slot] at values
  exact Fin.ext (by omega)
theorem no_tail_event_reuses_a_parent_slot (index : Index prepared) (old : Fin made.parent.spent) (event : Fin made.spent) :
    made.slot index event ≠ made.parent.slot index old := by
  intro same
  have values := congrArg Fin.val same
  change made.parent.spent+event.val = old.val at values
  have inside := old.isLt
  omega
theorem every_tail_event_has_the_same_successful_source_invoice (index : Index prepared) (event : Fin made.spent) :
    ((made.parent.funding.resultAt index).invoice (made.parent.paid index)).bill.payment.succeeded = true ∧
      (made.slot index event).val = made.parent.spent+event.val :=
  ⟨((made.parent.funding.resultAt index).invoice (made.parent.paid index)).paid,rfl⟩
end Funded

def endpointFor {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) {units : Nat}
    (parent : Prepayment.WorkFor menu items units) {position capacity : Nat} (tail : WorkFor menu items parent position capacity)
    (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point :=
  match menu with
  | .empty .. | .blocked .. => Policy.Protocol.retained prepared.saved[index].stage
  | .ready .. => match tail.endpoint.selection items position with
    | none => Policy.Protocol.retained prepared.saved[index].stage
    | some answer => answer.selected.policy.report.2.endpoint index

def Result.cursor {prepared : Prepared input} {units position : Nat} (result : Result prepared units position) :
    (index : Index result.after) → Binding.NativeCursor result.after.saved[index].point := by
  cases result with
  | empty absent => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | unpaid funding generated failedAt failed => exact fun index => Policy.Protocol.retained funding.installed.saved[index].stage
  | ready made => exact endpointFor made.parent.body.menu made.parent.body.reports made.parent.run made.tail

def Result.auditLaw {prepared : Prepared input} {units position : Nat} (result : Result prepared units position) (index : Index result.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (result.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result prepared units position
  project := fun _ {_} _ _ => result

namespace Attachment
noncomputable section
variable {original : Prepared input} {units position : Nat} (audit : Result original units position)
  {activeSource : SourceQuota.Generated audit.after} {activeCatalogue : SourceQuota.Catalogue activeSource.snapshot}
  {activeAll : Candidates activeSource activeCatalogue} {activeItems : List (Report activeAll)} (chosen : Selected activeItems) (index : Index audit.after)
  (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot chosen.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source)

def auditLaw : SourceNativeProjectionLaw
    (Responsibility.Canonical.Payment.Runtime.root chosen.policy.report.2 index chosen.policy.first (chosen.policy.paid index) component).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result original units position
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
def read : Result original units position :=
  match (facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()) with
  | .inl value => value.2
  | .inr impossible => impossible.elim
theorem the_actual_refinement_is_active_with_whole_ledger_and_next :
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

private noncomputable def nextFor {original : Prepared input} {units position : Nat} (audit : Result original units position)
    (menu : DomainResult audit.after) (items : ReportsFor menu) {oldUnits : Nat}
    (parent : Prepayment.WorkFor menu items oldUnits) {capacity : Nat} (tail : WorkFor menu items parent position capacity) (index : Index audit.after)
    (component : SourceNativeProjectionLaw (Online.Runtime.root (endpointFor menu items parent tail index)).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent := by
  cases menu with
  | empty => exact originalNext (endpointFor _ items parent tail index) component
  | blocked => exact originalNext (endpointFor _ items parent tail index) component
  | ready source catalogue generated all =>
    cases chosen : tail.endpoint.selection items position with
    | none => exact originalNext (endpointFor _ items parent tail index) component
    | some answer =>
      have same : endpointFor (.ready source catalogue generated all) items parent tail index = answer.selected.policy.report.2.endpoint index := by
        dsimp only [endpointFor]
        rw [chosen]
      let original : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot answer.selected.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source :=
        Eq.mp (congrArg (fun value : Binding.NativeCursor audit.after.saved[index].point =>
          SourceNativeProjectionLaw (Online.Runtime.root value).toAuthoritativeRoot.toLedgerRoot.source) same) component
      exact Attachment.next audit answer.selected index original

noncomputable def Result.next {prepared : Prepared input} {units position : Nat} (result : Result prepared units position) (index : Index result.after) : AuthorityCurrent := by
  cases result with
  | empty absent => exact originalNext ((Result.empty absent).cursor index) ((Result.empty absent).auditLaw index)
  | unpaid funding generated failedAt failed =>
      exact originalNext ((Result.unpaid funding generated failedAt failed).cursor index) ((Result.unpaid funding generated failedAt failed).auditLaw index)
  | ready made => exact nextFor (Result.ready made) made.parent.body.menu made.parent.body.reports made.parent.run made.tail index ((Result.ready made).auditLaw index)

structure Activation (input : Input seed) (units requested : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  execution : Result preparation units requested
  generated : execution = generate preparation units requested
  bound : Binding.Linked execution.after point
  binding_generated : Binding.locate execution.after point = .linked bound
inductive Invocation (input : Input seed) (units requested : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input units requested point)
def invoke (input : Input seed) (units requested : Nat) (point : NativePoint input) : Invocation input units requested point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let execution := generate preparation units requested
    match linked : Binding.locate execution.after point with
    | .linked bound => .activated ⟨preparation,rfl,execution,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed
noncomputable def Activation.next {units requested : Nat} {point : NativePoint input} (made : Activation input units requested point) : AuthorityCurrent :=
  made.execution.next made.bound.index
theorem every_matching_actual_point_is_activated (input : Input seed) (units requested : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input units requested point,invoke input units requested point = .activated made := by
  unfold invoke
  rw [dif_pos observed]
  dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken exact_broken;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (units requested : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invoke input units requested point = .mismatch broken := by simp only [invoke,dif_neg broken]

end Payment

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Reference
