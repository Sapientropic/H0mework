import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateRuntime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Reference.Audit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}


/-- Independent branches start at the same actual postouter source. -/
structure Case (prepared : Prepared input) (units position : Nat) where
  private mk ::
  payment : Reference.Payment.Result prepared units position
  generated : payment = Reference.Payment.generate prepared units position
def materialize (prepared : Prepared input) (units position : Nat) : Case prepared units position :=
  ⟨Reference.Payment.generate prepared units position,rfl⟩
def Case.after {units position : Nat} (branch : Case prepared units position) := branch.payment.after
def Case.cursor {units position : Nat} (branch : Case prepared units position) (index : Index branch.after) := branch.payment.cursor index

variable {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot) (position : Nat)
abbrev Row := Sigma fun quota : catalogue.Quota => Case prepared quota.val position
inductive State where
  | walking (cached : List (Row catalogue position)) (remaining : List catalogue.Quota)
      (conserved : cached.map Sigma.fst++remaining = catalogue.quotas)
  | finished (cached : List (Row catalogue position)) (complete : cached.map Sigma.fst = catalogue.quotas)
def initial : State catalogue position := .walking [] catalogue.quotas rfl
inductive Event where
  | materialized (quota : catalogue.Quota) (branch : Case prepared quota.val position)
      (generated : branch = materialize prepared quota.val position)
  | complete
def move : State catalogue position → Option (State catalogue position × Event catalogue position)
  | .walking cached [] conserved => some (.finished cached (by simpa only [List.append_nil] using conserved),.complete)
  | .walking cached (quota::rest) conserved =>
      let branch := materialize prepared quota.val position
      some (.walking (cached++[⟨quota,branch⟩]) rest (by
        simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using conserved),.materialized quota branch rfl)
  | .finished .. => none
def State.rank : State catalogue position → Nat | .walking _ remaining _ => remaining.length+1 | .finished .. => 0
def State.done : State catalogue position → Bool | .finished .. => true | _ => false
def State.rows : State catalogue position → List (Row catalogue position) | .walking cached .. | .finished cached .. => cached
def State.remaining : State catalogue position → List catalogue.Quota | .walking _ remaining _ => remaining | .finished .. => []
theorem State.coverage (state : State catalogue position) : (state.rows catalogue position).map Sigma.fst ++ state.remaining catalogue position = catalogue.quotas := by
  cases state with
  | walking => assumption
  | finished cached complete => simpa only [rows,remaining,List.append_nil] using complete
theorem progress {before after : State catalogue position} {event : Event catalogue position}
    (actual : move catalogue position before = some (after,event)) : after.rank catalogue position < before.rank catalogue position := by
  cases before with
  | walking cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons];omega
  | finished => cases actual
theorem no_move_iff_done (before : State catalogue position) : move catalogue position before = none ↔ before.done catalogue position = true := by
  cases before with
  | walking cached remaining conserved => cases remaining <;> simp [move,State.done]
  | finished => simp [move,State.done]
inductive Trace : State catalogue position → State catalogue position → List (Event catalogue position) → Prop
  | nil (before) : Trace before before []
  | step {before middle after event work} (actual : move catalogue position before = some (middle,event))
      (later : Trace middle after work) : Trace before after (event::work)
structure Calculation (before : State catalogue position) (capacity : Nat) where
  private mk ::
  endpoint : State catalogue position
  work : List (Event catalogue position)
  history : Trace catalogue position before endpoint work
  fits : work.length ≤ capacity
def execute : (capacity : Nat) → (before : State catalogue position) → Calculation catalogue position before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move catalogue position before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩
theorem sufficient_source_rank_finishes (capacity : Nat) (before : State catalogue position) (enough : before.rank catalogue position ≤ capacity) :
    (execute catalogue position capacity before).endpoint.done catalogue position = true := by
  induction capacity generalizing before with
  | zero => cases before <;> simp_all [State.rank,State.done,execute]
  | succ capacity ih =>
      unfold execute;split
      · rename_i stopped;exact (no_move_iff_done catalogue position before).mp stopped
      · rename_i after event actual;exact ih after (by have less := progress catalogue position actual;omega)
theorem unfinished_uses_all (capacity : Nat) (before : State catalogue position)
    (pending : (execute catalogue position capacity before).endpoint.done catalogue position = false) :
    (execute catalogue position capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
      unfold execute at pending ⊢;split at pending
      · rename_i stopped;rw [(no_move_iff_done catalogue position before).mp stopped] at pending;cases pending
      · rename_i after event actual;exact congrArg Nat.succ (ih after pending)
theorem completed_keeps_every_original_quota (state : State catalogue position) (done : state.done catalogue position = true)
    (quota : catalogue.Quota) : ∃ row ∈ state.rows catalogue position,row.1 = quota := by
  cases state with
  | walking => cases done
  | finished cached complete =>
      have inside : quota ∈ cached.map Sigma.fst := by rw [complete];exact List.mem_finRange _
      obtain ⟨row,listed,same⟩ := List.mem_map.mp inside;exact ⟨row,listed,same⟩

variable {catalogue position}
inductive Exploration {original : Prepared input} (outer : CandidateRuntime.Started original) (position : Nat) where
  | pending (unfinished : outer.program.acquisition.endpoint.done = false)
  | unavailable (source : SourceQuota.Generated outer.funding.installed) (generated : source = SourceQuota.generate outer.funding.installed)
      (outside : match source.result with | .domain _ => False | _ => True)
      (same : outer.program.acquisition.endpoint = .finished (.unavailable source generated (by cases observed : source.result <;> first | trivial | (simp only [observed] at outside))))
  | enumerated (source : SourceQuota.Generated outer.funding.installed) (generated : source = SourceQuota.generate outer.funding.installed)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (limit : Nat) (bound : limit = catalogue.bound)
      (same : outer.program.acquisition.endpoint = .finished (.domain source generated catalogue domain limit bound))
      (run : Calculation catalogue position (initial catalogue position) outer.unused)
      (actual : run = execute catalogue position outer.unused (initial catalogue position))
def Exploration.generate {original : Prepared input} (outer : CandidateRuntime.Started original) (position : Nat) : Exploration outer position :=
  match cached : outer.program.acquisition.endpoint with
  | .finished (.unavailable source generated outside) => .unavailable source generated (by cases observed : source.result <;> first | trivial | (simp only [observed] at outside)) cached
  | .finished (.domain source generated catalogue domain limit bound) =>
      .enumerated source generated catalogue domain limit bound cached (execute catalogue position outer.unused (initial catalogue position)) rfl
  | .observing .. | .validating .. | .seeding .. | .folding .. | .reducing .. => .pending (by rw [cached];rfl)

abbrev Alternative (prepared : Prepared input) (position : Nat) := Sigma fun units : Nat => Case prepared units position
def Exploration.branches {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} :
    Exploration outer position → List (Alternative outer.funding.installed position)
  | .pending .. | .unavailable .. => []
  | .enumerated _ _ catalogue _ _ _ _ run _ => (run.endpoint.rows catalogue position).map (fun row => ⟨row.1.val,row.2⟩)
def Exploration.spent {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} : Exploration outer position → Nat
  | .pending .. | .unavailable .. => 0
  | .enumerated _ _ _ _ _ _ _ run _ => run.work.length
def Exploration.finished {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} : Exploration outer position → Bool
  | .pending .. => false
  | .unavailable .. => true
  | .enumerated _ _ catalogue _ _ _ _ run _ => run.endpoint.done catalogue position
theorem Exploration.fits {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} (made : Exploration outer position) : made.spent ≤ outer.unused := by
  cases made with
  | pending | unavailable => exact Nat.zero_le _
  | enumerated => exact Calculation.fits _
def Exploration.unused {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} (made : Exploration outer position) := outer.unused-made.spent
theorem Exploration.same_outer_invoice_account {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} (made : Exploration outer position) :
    outer.spent+made.spent+made.unused = outer.budget.units := by
  have first := outer.consumed_or_retained;have bound := made.fits;unfold unused;omega
def Exploration.slot {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} (made : Exploration outer position)
    (index : Index original) (event : Fin made.spent) : Fin (((outer.funding.resultAt index).invoice (outer.paid index)).bill.units) :=
  ⟨outer.spent+event.val,by
    rw [((outer.funding.resultAt index).invoice (outer.paid index)).size]
    have total := made.same_outer_invoice_account;have inside := event.isLt;omega⟩
theorem Exploration.distinct_slots {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat} (made : Exploration outer position) (index : Index original) :
    Function.Injective (made.slot index) := by
  intro a b same;have values := congrArg Fin.val same;exact Fin.ext (by dsimp only [slot] at values;omega)
theorem Exploration.no_case_event_reuses_an_outer_slot {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat}
    (made : Exploration outer position) (index : Index original) (old : Fin outer.spent) (event : Fin made.spent) : made.slot index event ≠ outer.slot index old := by
  intro same;have values := congrArg Fin.val same;change outer.spent+event.val = old.val at values;have inside := old.isLt;omega
theorem Exploration.every_case_event_uses_the_original_successful_invoice {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat}
    (made : Exploration outer position) (index : Index original) (event : Fin made.spent) :
    ((outer.funding.resultAt index).invoice (outer.paid index)).bill.payment.succeeded = true ∧ (made.slot index event).val = outer.spent+event.val :=
  ⟨((outer.funding.resultAt index).invoice (outer.paid index)).paid,rfl⟩
theorem Exploration.pending_enumeration_has_no_unused_credit {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat}
    (source : SourceQuota.Generated outer.funding.installed) (generated : source = SourceQuota.generate outer.funding.installed)
    (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue) (limit : Nat) (bound : limit = catalogue.bound)
    (same : outer.program.acquisition.endpoint = .finished (.domain source generated catalogue domain limit bound))
    (run : Calculation catalogue position (initial catalogue position) outer.unused) (actual : run = execute catalogue position outer.unused (initial catalogue position))
    (pending : run.endpoint.done catalogue position = false) : (Exploration.enumerated source generated catalogue domain limit bound same run actual).unused = 0 := by
  have used := unfinished_uses_all catalogue position outer.unused (initial catalogue position) (by rw [←actual];exact pending)
  rw [←actual] at used;change outer.unused-run.work.length = 0;omega

theorem Exploration.pending_has_no_unused_credit {original : Prepared input} {outer : CandidateRuntime.Started original} {position : Nat}
    (made : Exploration outer position) (pending : made.finished = false) : made.unused = 0 := by
  cases made with
  | pending unfinished =>
      have used := SourceQuota.Acquisition.unfinished_uses_all (outer.budget.units-1) (SourceQuota.Acquisition.initial outer.funding.installed)
        (by rw [←outer.program.actual];exact unfinished)
      rw [←outer.program.actual] at used
      have count := outer.program.event_count
      have covered := outer.covered
      have positive := outer.positive
      change outer.unused-0 = 0
      dsimp only [CandidateRuntime.Started.unused,CandidateRuntime.Started.spent,CandidateRuntime.Program.nativeLength] at *
      omega
  | unavailable => cases pending
  | enumerated source generated catalogue domain limit bound same run actual =>
      exact pending_enumeration_has_no_unused_credit source generated catalogue domain limit bound same run actual pending

theorem every_affordable_quantity_has_its_own_actual_payment (state : State catalogue position) (done : state.done catalogue position = true)
    (count : Nat) (affordable : ∀ cell ∈ source.snapshot.cached,cell.2.Allows count) :
    ∃ row ∈ state.rows catalogue position,row.1.val = count ∧ row.2.payment = Reference.Payment.generate prepared row.1.val position := by
  obtain ⟨quota,_listed,same⟩ := catalogue.every_affordable_quantity_occurs_in_the_source_domain count affordable
  obtain ⟨row,listed,original⟩ := completed_keeps_every_original_quota catalogue position state done quota
  exact ⟨row,listed,(congrArg Fin.val original).trans same,row.2.generated⟩

inductive Result (prepared : Prepared input) (position : Nat) where
  | empty (budget : CandidateRuntime.BudgetChoice prepared) (absent : prepared.saved = [])
  | unpaid (budget : CandidateRuntime.BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (index : Index prepared) (failed : ¬(funding.resultAt index).funded)
  | zero (budget : CandidateRuntime.BudgetChoice prepared) (funding : EscrowBudget.Funding prepared budget.units)
      (generated : funding = EscrowBudget.reserve prepared budget.units) (paid : ∀ index : Index prepared,(funding.resultAt index).funded) (none : budget.units = 0)
  | exploring (outer : CandidateRuntime.Started prepared) (exploration : Exploration outer position) (generated : exploration = Exploration.generate outer position)
def generateFor (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (position : Nat) : Result prepared position :=
  match CandidateRuntime.openFor prepared budget with
  | .empty budget absent => .empty budget absent
  | .unpaid budget funding generated index failed => .unpaid budget funding generated index failed
  | .zero budget funding generated paid zeroProof => .zero budget funding generated paid zeroProof
  | .started outer => .exploring outer (Exploration.generate outer position) rfl
def generate (prepared : Prepared input) (position : Nat) : Result prepared position := generateFor prepared (CandidateRuntime.budgetFor prepared none) position

/-- This is the actual state before selecting any of the independent inner branches. -/
def Result.after {position : Nat} : Result prepared position → Prepared input
  | .empty .. => prepared
  | .unpaid _ funding .. | .zero _ funding .. => funding.installed
  | .exploring outer .. => outer.funding.installed
def Result.cursor {position : Nat} (audit : Result prepared position) (index : Index audit.after) : Binding.NativeCursor audit.after.saved[index].point :=
  Policy.Protocol.retained audit.after.saved[index].stage
def Result.auditLaw {position : Nat} (audit : Result prepared position) (index : Index audit.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (audit.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result prepared position
  project := fun _ {_} _ _ => audit
noncomputable def Result.retainedNext {position : Nat} (audit : Result prepared position) (index : Index audit.after) : AuthorityCurrent :=
  originalNext (audit.cursor index) (audit.auditLaw index)

structure Branch (prepared : Prepared input) (position : Nat) where
  private mk ::
  outer : CandidateRuntime.Started prepared
  alternative : Alternative outer.funding.installed position
def Result.branches {position : Nat} : Result prepared position → List (Branch prepared position)
  | .empty .. | .unpaid .. | .zero .. => []
  | .exploring outer exploration _ => exploration.branches.map (fun branch => ⟨outer,branch⟩)
noncomputable def Result.nextAt {position : Nat} (audit : Result prepared position) (ordinal : Fin audit.branches.length)
    (index : Index audit.branches[ordinal].alternative.2.after) : AuthorityCurrent :=
  Reference.Payment.Audit.next audit audit.branches[ordinal].alternative.2.payment index

structure Activation (input : Input seed) (override : Option Nat) (requested ordinal : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  budget : CandidateRuntime.BudgetChoice preparation
  budget_generated : budget = CandidateRuntime.budgetFor preparation override
  audit : Result preparation requested
  generated : audit = generateFor preparation budget requested
  branch : Branch preparation requested
  selected : audit.branches[ordinal]? = some branch
  bound : Binding.Linked branch.alternative.2.after point
  bound_generated : Binding.locate branch.alternative.2.after point = .linked bound
inductive Invocation (input : Input seed) (override : Option Nat) (requested ordinal : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | unlisted (preparation : Prepared input) (prepared_generated : preparation = Policy.prepare input)
      (budget : CandidateRuntime.BudgetChoice preparation) (budget_generated : budget = CandidateRuntime.budgetFor preparation override)
      (audit : Result preparation requested) (generated : audit = generateFor preparation budget requested) (absent : audit.branches[ordinal]? = none)
      (bound : Binding.Linked audit.after point) (bound_generated : Binding.locate audit.after point = .linked bound)
  | activated (made : Activation input override requested ordinal point)
def invokeWith (input : Input seed) (override : Option Nat) (requested ordinal : Nat) (point : NativePoint input) : Invocation input override requested ordinal point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let budget := CandidateRuntime.budgetFor preparation override
    let audit := generateFor preparation budget requested
    match selected : audit.branches[ordinal]? with
    | none => match linked : Binding.locate audit.after point with
      | .linked bound => .unlisted preparation rfl budget rfl audit rfl selected bound linked
      | .mismatch broken => False.elim (broken observed)
    | some branch => match linked : Binding.locate branch.alternative.2.after point with
      | .linked bound => .activated ⟨preparation,rfl,budget,rfl,audit,rfl,branch,selected,bound,linked⟩
      | .mismatch broken => False.elim (broken observed)
  else .mismatch observed
noncomputable def Activation.next {override : Option Nat} {requested ordinal : Nat} {point : NativePoint input}
    (made : Activation input override requested ordinal point) : AuthorityCurrent := Reference.Payment.Audit.next made.audit made.branch.alternative.2.payment made.bound.index
noncomputable def Invocation.next? {override : Option Nat} {requested ordinal : Nat} {point : NativePoint input} :
    Invocation input override requested ordinal point → Option AuthorityCurrent
  | .mismatch .. => none
  | .unlisted _ _ _ _ audit _ _ bound _ => some (audit.retainedNext bound.index)
  | .activated made => some made.next
theorem mismatched_observation_is_rejected (input : Input seed) (override : Option Nat) (requested ordinal : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) : invokeWith input override requested ordinal point = .mismatch broken := by
  simp only [invokeWith,dif_neg broken]
def invoke (input : Input seed) (requested ordinal : Nat) (point : NativePoint input) : Invocation input none requested ordinal point :=
  invokeWith input none requested ordinal point

theorem every_matching_listed_branch_is_activated (input : Input seed) (override : Option Nat) (requested ordinal : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading)
    (listed : ((generateFor (Policy.prepare input) (CandidateRuntime.budgetFor (Policy.prepare input) override) requested).branches[ordinal]?).isSome = true) :
    ∃ made : Activation input override requested ordinal point,invokeWith input override requested ordinal point = .activated made := by
  unfold invokeWith;rw [dif_pos observed];dsimp only
  split
  · rename_i absent;rw [absent] at listed;cases listed
  · split
    · exact ⟨_,rfl⟩
    · rename_i broken actual;exact False.elim (broken observed)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee
