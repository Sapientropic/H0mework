import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Machine
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Runtime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Prepayment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed}

def WorkFor {prepared : Prepared input} : (menu : DomainResult prepared) → ReportsFor menu → Nat → Type
  | .empty ..,_ ,_ | .blocked ..,_ ,_ => Unit
  | .ready ..,items,units => Machine.Computation items (Machine.initial items) units
def runFor {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → (units : Nat) → WorkFor menu items units
  | .empty ..,_ ,_ | .blocked ..,_ ,_ => ()
  | .ready ..,items,units => Machine.execute items units (Machine.initial items)
def workLength {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {units : Nat} → WorkFor menu items units → Nat
  | .empty ..,_ ,_,_ | .blocked ..,_ ,_,_ => 0
  | .ready ..,_ ,_,run => run.work.length
theorem work_fits {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) (units : Nat) (run : WorkFor menu items units) :
    workLength menu items run ≤ units := by cases menu with
  | empty | blocked => exact Nat.zero_le _
  | ready => exact run.fits

def finishedFor {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {units : Nat} → WorkFor menu items units → Bool
  | .empty ..,_ ,_,_ | .blocked ..,_ ,_,_ => true
  | .ready ..,items,_,run => run.endpoint.finished items

theorem pending_run_uses_the_entire_allowance {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) (units : Nat)
    (unfinished : finishedFor menu items (runFor menu items units) = false) : workLength menu items (runFor menu items units) = units := by
  cases menu with
  | empty | blocked => cases unfinished
  | ready => exact Machine.unfinished_uses_the_entire_allowance _ units _ unfinished

structure Started (prepared : Prepared input) (units : Nat) where
  private mk ::
  funding : EscrowBudget.Funding prepared units
  funding_generated : funding = EscrowBudget.reserve prepared units
  nonempty : prepared.saved ≠ []
  paid : ∀ index : Index prepared,(funding.resultAt index).funded
  body : Record funding.installed
  body_generated : body = Joint.build funding.installed
  run : WorkFor body.menu body.reports units
  run_generated : run = runFor body.menu body.reports units

inductive Result (prepared : Prepared input) (units : Nat) where
  | empty (absent : prepared.saved = [])
  | unpaid (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (index : Index prepared) (failed : ¬ (funding.resultAt index).funded)
  | started (made : Started prepared units)

def generate (prepared : Prepared input) (units : Nat) : Result prepared units :=
  if absent : prepared.saved = [] then .empty absent else
    let funding := EscrowBudget.reserve prepared units
    match Distributed.inspect (fun index => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ failed => .unpaid funding rfl index failed
    | .accepted every =>
        let body := Joint.build funding.installed
        .started ⟨funding,rfl,absent,fun index => every index (List.mem_finRange _),body,rfl,runFor body.menu body.reports units,rfl⟩

def Result.after {prepared : Prepared input} {units : Nat} : Result prepared units → Prepared input
  | .empty _ => prepared
  | .unpaid funding .. => funding.installed
  | .started made => made.funding.installed

namespace Started
variable {prepared : Prepared input} {units : Nat} (made : Started prepared units)
def spent := workLength made.body.menu made.body.reports made.run
def unused := units-made.spent
theorem consumed_or_retained : made.spent+made.unused = units := by
  have bound := work_fits made.body.menu made.body.reports units made.run
  dsimp only [spent,unused] at *
  omega

def slot (index : Index prepared) (event : Fin made.spent) :
    Fin (((made.funding.resultAt index).invoice (made.paid index)).bill.units) :=
  ⟨event.val,by rw [((made.funding.resultAt index).invoice (made.paid index)).size]
                exact event.isLt.trans_le (work_fits made.body.menu made.body.reports units made.run)⟩
theorem distinct_slots (index : Index prepared) : Function.Injective (made.slot index) := by
  intro left right same
  have values := congrArg Fin.val same
  exact Fin.ext values
theorem every_actual_step_uses_its_prior_source_invoice (index : Index prepared) (event : Fin made.spent) :
    ((made.funding.resultAt index).invoice (made.paid index)).bill.payment.succeeded = true ∧
    (made.slot index event).val = event.val := ⟨((made.funding.resultAt index).invoice (made.paid index)).paid,rfl⟩
theorem the_domain_is_rebuilt_after_the_actual_payment : made.body.menu = Paid.generateAll made.funding.installed := by rw [made.body_generated];rfl
theorem every_original_point_keeps_its_position_and_multiplicity : made.funding.installed.saved.map Cell.point = prepared.saved.map Cell.point :=
  made.funding.source_order_and_multiplicity

def finished := finishedFor made.body.menu made.body.reports made.run
theorem pending_spends_the_entire_actual_allowance (unfinished : made.finished = false) : made.spent = units := by
  dsimp only [finished] at unfinished
  dsimp only [spent]
  rw [made.run_generated] at unfinished ⊢
  exact pending_run_uses_the_entire_allowance made.body.menu made.body.reports units unfinished
inductive Status where
  | completed (finished : made.finished = true)
  | pending (unfinished : made.finished = false) (spent : made.spent = units)
def status : Status made :=
  if finished : made.finished = true then .completed finished
  else let pending := Bool.eq_false_iff.mpr finished
       .pending pending (made.pending_spends_the_entire_actual_allowance pending)

def endpointFor {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu)
    {units : Nat} (run : WorkFor menu items units) (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point :=
  match menu with
  | .empty .. | .blocked .. => Policy.Protocol.retained prepared.saved[index].stage
  | .ready .. => match run.endpoint.selection _ with
    | none => Policy.Protocol.retained prepared.saved[index].stage
    | some selected => selected.policy.report.2.endpoint index

def cursor (index : Index made.funding.installed) := endpointFor made.body.menu made.body.reports made.run index

end Started

def Result.cursor {prepared : Prepared input} {units : Nat} (result : Result prepared units) :
    (index : Index result.after) → Binding.NativeCursor result.after.saved[index].point := by
  cases result with
  | empty absent => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | unpaid funding generated index failed => exact fun actual => Policy.Protocol.retained funding.installed.saved[actual].stage
  | started made => exact made.cursor

def Result.auditLaw {prepared : Prepared input} {units : Nat} (result : Result prepared units) (index : Index result.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (result.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result prepared units
  project := fun _ {_} _ _ => result

namespace Attachment
noncomputable section
variable {original : Prepared input} {units : Nat} (audit : Result original units)
  {source : SourceQuota.Generated audit.after} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue} {items : List (Report all)} (chosen : Selected items) (index : Index audit.after)
  (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot chosen.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source)

def auditLaw : SourceNativeProjectionLaw
    (Responsibility.Canonical.Payment.Runtime.root chosen.policy.report.2 index chosen.policy.first (chosen.policy.paid index) component).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Result original units
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
def read : Result original units :=
  match (facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()) with
  | .inl value => value.2
  | .inr impossible => impossible.elim
theorem the_actual_fee_search_is_active_with_this_whole_ledger_and_next :
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

private noncomputable def nextFor {original : Prepared input} {units : Nat} (audit : Result original units)
    (menu : DomainResult audit.after) (items : ReportsFor menu) (run : WorkFor menu items units) (index : Index audit.after)
    (component : SourceNativeProjectionLaw (Online.Runtime.root (Started.endpointFor menu items run index)).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent := by
  cases menu with
  | empty => exact originalNext (Started.endpointFor _ items run index) component
  | blocked => exact originalNext (Started.endpointFor _ items run index) component
  | ready source catalogue generated all =>
    cases chosen : run.endpoint.selection items with
    | none => exact originalNext (Started.endpointFor _ items run index) component
    | some choice =>
      have same : Started.endpointFor (.ready source catalogue generated all) items run index = choice.policy.report.2.endpoint index := by
        dsimp only [Started.endpointFor]
        rw [chosen]
      let original : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot choice.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source :=
        Eq.mp (congrArg (fun value : Binding.NativeCursor audit.after.saved[index].point =>
          SourceNativeProjectionLaw (Online.Runtime.root value).toAuthoritativeRoot.toLedgerRoot.source) same) component
      exact Attachment.next audit choice index original

noncomputable def Result.next {prepared : Prepared input} {units : Nat} (result : Result prepared units) (index : Index result.after) : AuthorityCurrent := by
  cases result with
  | empty absent => exact originalNext ((Result.empty absent).cursor index) ((Result.empty absent).auditLaw index)
  | unpaid funding generated failedAt failed =>
      exact originalNext ((Result.unpaid funding generated failedAt failed).cursor index) ((Result.unpaid funding generated failedAt failed).auditLaw index)
  | started made => exact nextFor (Result.started made) made.body.menu made.body.reports made.run index ((Result.started made).auditLaw index)

structure Activation (input : Input seed) (units : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  execution : Result preparation units
  generated : execution = generate preparation units
  bound : Binding.Linked execution.after point
  binding_generated : Binding.locate execution.after point = .linked bound

inductive Invocation (input : Input seed) (units : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input units point)

def invoke (input : Input seed) (units : Nat) (point : NativePoint input) : Invocation input units point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let execution := generate preparation units
    match linked : Binding.locate execution.after point with
    | .linked bound => .activated ⟨preparation,rfl,execution,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed

noncomputable def Activation.next {units : Nat} {point : NativePoint input} (made : Activation input units point) : AuthorityCurrent :=
  made.execution.next made.bound.index

theorem every_matching_actual_point_is_activated (input : Input seed) (units : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input units point,invoke input units point = .activated made := by
  unfold invoke
  rw [dif_pos observed]
  dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken exact_broken
    exact False.elim (broken observed)

theorem mismatched_observation_is_rejected (input : Input seed) (units : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invoke input units point = .mismatch broken := by simp only [invoke,dif_neg broken]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Prepayment
