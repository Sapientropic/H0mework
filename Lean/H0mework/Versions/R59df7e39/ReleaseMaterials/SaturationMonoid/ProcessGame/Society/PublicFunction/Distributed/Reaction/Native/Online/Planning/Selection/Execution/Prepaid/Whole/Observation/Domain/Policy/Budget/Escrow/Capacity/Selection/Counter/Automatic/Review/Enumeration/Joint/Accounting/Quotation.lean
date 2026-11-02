import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Allowance
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

def readyFor {prepared : Prepared input} : DomainResult prepared → Bool
  | .ready .. => true
  | _ => false
inductive Check {units : Nat} (shape : Allowance.Shape prepared units) where
  | unpaid (index : Index prepared) (failed : ¬ (shape.funding.resultAt index).funded)
  | outside (notReady : readyFor shape.body.menu = false)
  | short (under : ¬ shape.amount ≤ units)
  | qualified (paid : ∀ index : Index prepared,(shape.funding.resultAt index).funded)
      (ready : readyFor shape.body.menu = true) (enough : shape.amount ≤ units)

def examine {units : Nat} (shape : Allowance.Shape prepared units) : Check shape :=
  match Distributed.inspect (fun index : Index prepared => (shape.funding.resultAt index).funded) (keys prepared) with
  | .rejected index _ failed => .unpaid index failed
  | .accepted paid =>
    if ready : readyFor shape.body.menu = true then
      if enough : shape.amount ≤ units then .qualified (fun index => paid index (List.mem_finRange _)) ready enough else .short enough
    else .outside (Bool.eq_false_iff.mpr ready)

structure Assessment (prepared : Prepared input) (units : Nat) where
  private mk ::
  shape : Allowance.Shape prepared units
  source : shape = Allowance.describe prepared units
  check : Check shape
  generated : check = examine shape

def assess (prepared : Prepared input) (units : Nat) : Assessment prepared units :=
  let shape := Allowance.describe prepared units
  ⟨shape,rfl,examine shape,rfl⟩

structure Qualification {units : Nat} (assessment : Assessment prepared units) : Type where
  private mk ::
  paid : ∀ index : Index prepared,(assessment.shape.funding.resultAt index).funded
  ready : readyFor assessment.shape.body.menu = true
  enough : assessment.shape.amount ≤ units

def Assessment.qualification? {units : Nat} (assessment : Assessment prepared units) : Option (Qualification assessment) :=
  match assessment.check with
  | .qualified paid ready enough => some ⟨paid,ready,enough⟩
  | _ => none

theorem no_qualification_has_an_exact_source_reason {units : Nat} (assessment : Assessment prepared units)
    (absent : assessment.qualification? = none) :
    (∃ index : Index prepared,¬ (assessment.shape.funding.resultAt index).funded) ∨
      readyFor assessment.shape.body.menu = false ∨ ¬ assessment.shape.amount ≤ units := by
  cases found : assessment.check with
  | unpaid index failed => exact .inl ⟨index,failed⟩
  | outside notReady => exact .inr (.inl notReady)
  | short under => exact .inr (.inr under)
  | qualified paid ready enough => simp only [Assessment.qualification?,found,reduceCtorEq] at absent

variable {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
abbrev Row := Sigma fun quota : catalogue.Quota => Assessment prepared quota.val
def directory : List (Row catalogue) := catalogue.quotas.map fun quota => ⟨quota,assess prepared quota.val⟩

structure Pick (rows : List (Row catalogue)) where
  private mk ::
  row : Row catalogue
  listed : row ∈ rows
  qualification : Qualification row.2
inductive Search (rows : List (Row catalogue)) : Type where
  | found (picked : Pick catalogue rows)
  | excluded (absent : ∀ row ∈ rows,row.2.qualification? = none)

def search : (rows : List (Row catalogue)) → Search catalogue rows
  | [] => .excluded (by intro row inside;cases inside)
  | row::rest => match actual : row.2.qualification? with
    | some qualification => .found ⟨row,List.mem_cons_self,qualification⟩
    | none => match search rest with
      | .found picked => .found ⟨picked.row,List.mem_cons_of_mem _ picked.listed,picked.qualification⟩
      | .excluded absent => .excluded (by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other;exact actual
          · exact absent other later)

structure Book where
  private mk ::
  rows : List (Row catalogue)
  source : rows = directory catalogue
  selection : Search catalogue rows
  generated : selection = search catalogue rows

def compile : Book catalogue :=
  let rows := directory catalogue
  ⟨rows,rfl,search catalogue rows,rfl⟩

theorem original_catalogue_is_nonempty (catalogue : SourceQuota.Catalogue source.snapshot) : prepared.saved ≠ [] := by
  intro empty
  have sizes := congrArg List.length catalogue.same
  have length := source.snapshot.cached_length
  simp only [List.length_cons] at sizes
  rw [empty,List.length_nil] at length
  omega

theorem every_affordable_quantity_has_its_own_post_fee_assessment (book : Book catalogue) (count : Nat)
    (affordable : ∀ cell ∈ source.snapshot.cached,cell.2.Allows count) :
    ∃ row ∈ book.rows,row.1.val = count ∧ row.2 = assess prepared row.1.val := by
  obtain ⟨quota,listed,same⟩ := catalogue.every_affordable_quantity_occurs_in_the_source_domain count affordable
  refine ⟨⟨quota,assess prepared quota.val⟩,?_,same,rfl⟩
  rw [book.source]
  exact List.mem_map.mpr ⟨quota,listed,rfl⟩

theorem excluded_covers_every_affordable_quantity (book : Book catalogue)
    (absent : ∀ row ∈ book.rows,row.2.qualification? = none) (count : Nat)
    (affordable : ∀ cell ∈ source.snapshot.cached,cell.2.Allows count) :
    (assess prepared count).qualification? = none := by
  obtain ⟨row,listed,same,generated⟩ := every_affordable_quantity_has_its_own_post_fee_assessment catalogue book count affordable
  have rejected := absent row listed
  rw [generated] at rejected
  cases same
  exact rejected

structure Dispatch (row : Row catalogue) (_qualification : Qualification row.2) (position : Nat) where
  private mk ::
  payment : Reference.Payment.Funded prepared row.1.val position
  generated : Reference.Payment.generate prepared row.1.val position = .ready payment
  parent_finished : payment.parent.finished = true
  tail_finished : Allowance.finishedFor payment.parent.body.menu payment.parent.body.reports payment.tail = true

def dispatch (row : Row catalogue) (qualification : Qualification row.2) (position : Nat) : Dispatch catalogue row qualification position :=
  match actual : Reference.Payment.generate prepared row.1.val position with
  | .empty absent => False.elim (original_catalogue_is_nonempty catalogue absent)
  | .unpaid _funding generated index failed =>
      let same := row.2.shape.funding_generated.trans generated.symm
      False.elim (failed (same ▸ qualification.paid index))
  | .ready payment =>
      let finished := Allowance.quoted_source_bound_finishes_the_actual_execution row.2.shape qualification.enough payment
      ⟨payment,actual,finished.1,finished.2⟩

inductive Result (prepared : Prepared input) (position : Nat) where
  | unavailable (source : SourceQuota.Generated prepared) (source_generated : source = SourceQuota.generate prepared)
      (outside : match source.result with | .domain _ => False | _ => True)
  | exhausted (source : SourceQuota.Generated prepared) (source_generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (book : Book catalogue) (book_generated : book = compile catalogue)
      (absent : ∀ row ∈ book.rows,row.2.qualification? = none)
  | admitted (source : SourceQuota.Generated prepared) (source_generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (domain : source.result = .domain catalogue)
      (book : Book catalogue) (book_generated : book = compile catalogue)
      (picked : Pick catalogue book.rows) (picked_generated : book.selection = .found picked)
      (actual : Dispatch catalogue picked.row picked.qualification position)
      (actual_generated : actual = dispatch catalogue picked.row picked.qualification position)

def generate (prepared : Prepared input) (position : Nat) : Result prepared position :=
  let source := SourceQuota.generate prepared
  match domain : source.result with
  | .empty .. | .blocked .. => .unavailable source rfl (by rw [domain];trivial)
  | .domain catalogue =>
    let book := compile catalogue
    match selected : book.selection with
    | .excluded absent => .exhausted source rfl catalogue domain book rfl absent
    | .found picked => .admitted source rfl catalogue domain book rfl picked selected (dispatch catalogue picked.row picked.qualification position) rfl

def Result.after {position : Nat} : Result prepared position → Prepared input
  | .unavailable .. | .exhausted .. => prepared
  | .admitted _ _ _ _ _ _ _ _ actual _ => actual.payment.parent.funding.installed

def Result.cursor {position : Nat} (result : Result prepared position) :
    (index : Index result.after) → Binding.NativeCursor result.after.saved[index].point := by
  cases result with
  | unavailable source generated outside => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | exhausted source generated catalogue domain book bookGenerated absent => exact fun index => Policy.Protocol.retained prepared.saved[index].stage
  | admitted source generated catalogue domain book bookGenerated picked chosen actual actualGenerated =>
      exact Reference.Payment.endpointFor actual.payment.parent.body.menu actual.payment.parent.body.reports actual.payment.parent.run actual.payment.tail

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
theorem the_actual_source_budget_is_active_with_whole_ledger_and_next :
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
  | unavailable source generated outside =>
      exact originalNext ((Result.unavailable source generated outside).cursor index) ((Result.unavailable source generated outside).auditLaw index)
  | exhausted source generated catalogue domain book bookGenerated absent =>
      exact originalNext ((Result.exhausted source generated catalogue domain book bookGenerated absent).cursor index)
        ((Result.exhausted source generated catalogue domain book bookGenerated absent).auditLaw index)
  | admitted source generated catalogue domain book bookGenerated picked chosen actual actualGenerated =>
      exact nextFor (Result.admitted source generated catalogue domain book bookGenerated picked chosen actual actualGenerated)
        actual.payment.parent.body.menu actual.payment.parent.body.reports actual.payment.parent.run actual.payment.tail index
        ((Result.admitted source generated catalogue domain book bookGenerated picked chosen actual actualGenerated).auditLaw index)

structure Activation (input : Input seed) (requested : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  execution : Result preparation requested
  generated : execution = generate preparation requested
  bound : Binding.Linked execution.after point
  binding_generated : Binding.locate execution.after point = .linked bound
inductive Invocation (input : Input seed) (requested : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input requested point)
def invoke (input : Input seed) (requested : Nat) (point : NativePoint input) : Invocation input requested point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let execution := generate preparation requested
    match linked : Binding.locate execution.after point with
    | .linked bound => .activated ⟨preparation,rfl,execution,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed
noncomputable def Activation.next {requested : Nat} {point : NativePoint input} (made : Activation input requested point) : AuthorityCurrent :=
  made.execution.next made.bound.index
theorem every_matching_actual_point_uses_a_source_generated_allowance (input : Input seed) (requested : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input requested point,invoke input requested point = .activated made := by
  unfold invoke
  rw [dif_pos observed]
  dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken exact_broken;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (requested : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invoke input requested point = .mismatch broken := by simp only [invoke,dif_neg broken]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation
