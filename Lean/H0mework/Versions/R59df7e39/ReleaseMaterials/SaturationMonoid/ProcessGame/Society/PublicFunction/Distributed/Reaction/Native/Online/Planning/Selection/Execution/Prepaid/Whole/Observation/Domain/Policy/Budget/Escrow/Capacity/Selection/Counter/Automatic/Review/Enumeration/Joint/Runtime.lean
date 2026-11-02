import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Choice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

abbrev Report {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    (all : Candidates source catalogue) := Sigma fun owner : Ready all => Generated owner

def reports {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    (all : Candidates source catalogue) : List (Report all) := (ready all).map fun owner => ⟨owner,generate owner⟩

def firstVerified {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    {all : Candidates source catalogue} : List (Report all) → Option (Report all)
  | [] => none
  | head::tail => if head.2.completed.isSome then some head else firstVerified tail

theorem every_released_report_has_a_complete_global_choice {source : SourceQuota.Generated prepared}
    {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}
    (items : List (Report all)) (report : Report all) (selected : firstVerified items = some report) :
    ∃ choice : Choice all,report.2.completed = some choice := by
  induction items with
  | nil => cases selected
  | cons head tail ih =>
    dsimp only [firstVerified] at selected
    split at selected
    · rename_i completed
      cases Option.some.inj selected
      exact Option.isSome_iff_exists.mp completed
    · exact ih selected

def actual {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    {all : Candidates source catalogue} (items : List (Report all)) : Option (Report all) :=
  match firstVerified items with
  | some report => some report
  | none => items.head?

def ReportsFor : DomainResult prepared → Type
  | .empty .. | .blocked .. => Unit
  | .ready _ _ _ all => List (Report all)
def produceFor : (menu : DomainResult prepared) → ReportsFor menu
  | .empty .. | .blocked .. => ()
  | .ready _ _ _ all => reports all

abbrev PaymentReport {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    (all : Candidates source catalogue) := Sigma fun report : Report all => NativePayment.Book report.2

def PaymentsFor : DomainResult prepared → Type
  | .empty .. | .blocked .. => Unit
  | .ready _ _ _ all => List (PaymentReport all)
def paymentsFor : (menu : DomainResult prepared) → ReportsFor menu → PaymentsFor menu
  | .empty ..,_ | .blocked ..,_ => ()
  | .ready ..,items => items.map fun report => ⟨report,NativePayment.generate report.2⟩

abbrev ResponsibilityReport {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    (all : Candidates source catalogue) := Sigma fun report : Report all => Responsibility.Book report.2

def ResponsibilitiesFor : DomainResult prepared → Type
  | .empty .. | .blocked .. => Unit
  | .ready _ _ _ all => List (ResponsibilityReport all)
def responsibilitiesFor : (menu : DomainResult prepared) → ReportsFor menu → ResponsibilitiesFor menu
  | .empty ..,_ | .blocked ..,_ => ()
  | .ready ..,items => items.map fun report => ⟨report,Responsibility.generate report.2⟩

theorem every_actual_report_gets_its_own_complete_payment_book {source : SourceQuota.Generated prepared}
    {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}
    (items : List (Report all)) (report : Report all) (inside : report ∈ items) :
    (⟨report,NativePayment.generate report.2⟩ : PaymentReport all) ∈
      items.map (fun report => (⟨report,NativePayment.generate report.2⟩ : PaymentReport all)) :=
  List.mem_map.mpr ⟨report,inside,rfl⟩

structure Record (prepared : Prepared input) where
  private mk ::
  menu : DomainResult prepared
  generated : menu = Paid.generateAll prepared
  reports : ReportsFor menu
  reports_generated : reports = produceFor menu

def build (prepared : Prepared input) : Record prepared :=
  let menu := Paid.generateAll prepared
  ⟨menu,rfl,produceFor menu,rfl⟩

def accountedActual {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    {all : Candidates source catalogue} (items : List (Report all)) : Option (Report all) :=
  match (Accounting.compile items).verdict with
  | .selected choice => some choice.policy.report
  | .blocked _ => actual items

def SelectionsFor : (menu : DomainResult prepared) → ReportsFor menu → Type
  | .empty ..,_ | .blocked ..,_ => Unit
  | .ready ..,items => Accounting.Result items

def selectionsFor : (menu : DomainResult prepared) → (items : ReportsFor menu) → SelectionsFor menu items
  | .empty ..,_ | .blocked ..,_ => ()
  | .ready ..,items => Accounting.compile items


def executeFor : (menu : DomainResult prepared) → ReportsFor menu → (index : Index prepared) → Binding.NativeCursor prepared.saved[index].point
  | .empty ..,_,index | .blocked ..,_,index => Policy.Protocol.retained prepared.saved[index].stage
  | .ready ..,items,index => match accountedActual items with
    | some report => report.2.endpoint index
    | none => Policy.Protocol.retained prepared.saved[index].stage

def InstallationsFor : (menu : DomainResult prepared) → Index prepared → Type
  | .empty ..,_ | .blocked ..,_ => Unit
  | .ready _ _ _ all,index => Option (Sigma fun report : Report all => Responsibility.Canonical.Installed report.2 index)
def installationsFor : (menu : DomainResult prepared) → ReportsFor menu → (index : Index prepared) → InstallationsFor menu index
  | .empty ..,_,_ | .blocked ..,_,_ => ()
  | .ready ..,items,index => match actual items with
    | none => none
    | some report => match Responsibility.Canonical.install? report.2 index with
      | none => none
      | some installed => some ⟨report,installed⟩

def ConstructionsFor : (menu : DomainResult prepared) → Index prepared → Type
  | .empty ..,_ | .blocked ..,_ => Unit
  | .ready _ _ _ all,index => Option (Sigma fun report : Report all => Responsibility.Canonical.Payment.Runtime.Installation report.2 index)
def constructionsFor : (menu : DomainResult prepared) → ReportsFor menu → (index : Index prepared) → ConstructionsFor menu index
  | .empty ..,_,_ | .blocked ..,_,_ => ()
  | .ready ..,items,index => match actual items with
    | none => none
    | some report => some ⟨report,Responsibility.Canonical.Payment.Runtime.install report.2 index⟩


def Record.endpoint (made : Record prepared) (index : Index prepared) := executeFor made.menu made.reports index

inductive Obligation (prepared : Prepared input) where
  | original (debt : Policy.Obligation prepared)
  | menu (debt : Automatic.Obligation prepared)
  | report {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
      {all : Candidates source catalogue} (owner : Ready all) (made : Generated owner)
  | sourceEnumeration | sourceJoin | branchFields | entryInternals | intentOperands | frameInternals | keyInternals | moveInternals | dedupMembership | admissionInternals | outerSelection | nativeInternals | guard | allocation | ledgerInstallation | storage | announcement

def reportPending : (menu : DomainResult prepared) → ReportsFor menu → List (Obligation prepared)
  | .empty ..,_ | .blocked ..,_ => []
  | .ready ..,items => items.map fun report => .report report.1 report.2

def Record.pending (made : Record prepared) : List (Obligation prepared) :=
  (Policy.obligations prepared).map .original ++ (menuPending made.menu).map .menu ++ reportPending made.menu made.reports ++
    [.sourceEnumeration,.sourceJoin,.branchFields,.entryInternals,.intentOperands,.frameInternals,.keyInternals,.moveInternals,.dedupMembership,.admissionInternals,.outerSelection,.nativeInternals,.guard,.allocation,.ledgerInstallation,.storage,.announcement]

theorem every_original_obligation_is_retained (made : Record prepared) (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Obligation.original debt ∈ made.pending :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨debt,inside,rfl⟩)))

namespace Runtime
variable {point : NativePoint input} (record : Record prepared) (bound : Binding.Linked prepared point)
abbrev cursor := record.endpoint bound.index

def nativeEndpoint : Binding.NativeCursor point := bound.point_exact ▸ cursor record bound

structure Snapshot where
  private mk ::
  execution : Record prepared
  execution_exact : execution = record
  binding : Binding.Linked prepared point
  binding_exact : binding = bound
  pending : List (Obligation prepared)
  pending_exact : pending = record.pending
  learning : Binding.NativeCursor point
  learning_exact : learning = nativeEndpoint record bound
  whole : Evaluation (cursor record bound).source.val.code
  whole_exact : whole = Window.evaluate (cursor record bound).model (Policy.initial input point).depth
    ((cursor record bound).depth-(Policy.initial input point).depth)
  native : Authority.FullDisposition (cursor record bound).model ((cursor record bound).depth-1)
  native_exact : native = Authority.fullGenerate _ _
  payments : PaymentsFor record.menu
  payments_exact : payments = paymentsFor record.menu record.reports
  responsibilities : ResponsibilitiesFor record.menu
  responsibilities_exact : responsibilities = responsibilitiesFor record.menu record.reports
  installation : InstallationsFor record.menu bound.index
  installation_exact : installation = installationsFor record.menu record.reports bound.index
  construction : ConstructionsFor record.menu bound.index
  construction_exact : construction = constructionsFor record.menu record.reports bound.index
  selection : SelectionsFor record.menu record.reports
  selection_exact : selection = selectionsFor record.menu record.reports

def generate : Snapshot record bound :=
  ⟨record,rfl,bound,rfl,record.pending,rfl,nativeEndpoint record bound,rfl,
    Window.evaluate (cursor record bound).model (Policy.initial input point).depth
      ((cursor record bound).depth-(Policy.initial input point).depth),rfl,Authority.fullGenerate _ _,rfl,paymentsFor record.menu record.reports,rfl,responsibilitiesFor record.menu record.reports,rfl,installationsFor record.menu record.reports bound.index,rfl,constructionsFor record.menu record.reports bound.index,rfl,selectionsFor record.menu record.reports,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (cursor record bound).source.val.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (cursor record bound).source.val.input (cursor record bound).depth).current → Snapshot record bound
  project := fun _ {_} _ _ _own => generate record bound

def root := (Online.Runtime.root (cursor record bound)).withProjectionCoface (projectionLaw record bound)

theorem original_programme_root_is_preserved : (root record bound).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (cursor record bound).source.val.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (cursor record bound).source.val.input) :=
  ⟨ProgrammeSource.V _,root record bound,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (cursor record bound).source.val.input) where
  State := Nat
  stateAt := stateAt record bound
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (cursor record bound).source.val.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (cursor record bound).source.val.input first).current =
        (ProgrammeHistory.visitAt (cursor record bound).source.val.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Online.Runtime.Face)
  | computation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (cursor record bound).source.val.input) where
  process := process record bound
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (cursor record bound)).componentAt (Online.Runtime.facade (cursor record bound)).seed previous
    | .computation => projectionLaw record bound
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Online.Runtime.facade (cursor record bound)).installationAt (Online.Runtime.facade (cursor record bound)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Online.Runtime.root (cursor record bound)).toAuthoritativeRoot.source (projectionLaw record bound))
    | computation =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Online.Runtime.root (cursor record bound)).toAuthoritativeRoot.source (projectionLaw record bound)
  projectionAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (cursor record bound)).projectionAt (Online.Runtime.facade (cursor record bound)).seed previous
    | .computation => ()

abbrev activated := (facade record bound).seed.advance (cursor record bound).depth

theorem activated_state : (activated record bound).state = (cursor record bound).depth := by
  have all (n : Nat) : ((facade record bound).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Snapshot record bound :=
  match (facade record bound).readoutAt (activated record bound) .computation with
  | .inl output => output.2 (by
      change (ProgrammeHistory.visitAt (cursor record bound).source.val.input (activated record bound).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_generated_catalogue_and_paid_review_reach_the_original_root_ledger_and_next :
    let active := activated record bound
    (read record bound).execution = record ∧
    (read record bound).binding = bound ∧
    (read record bound).learning = nativeEndpoint record bound ∧
    (read record bound).pending = record.pending ∧
    (read record bound).whole = Window.evaluate (cursor record bound).model (Policy.initial input point).depth
      ((cursor record bound).depth-(Policy.initial input point).depth) ∧
    (read record bound).native = Authority.fullGenerate _ _ ∧
    HEq ((facade record bound).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record bound).stateAt ((process record bound).successor active.state) := by
  have rooted := (facade record bound).readoutAt_factorizes (activated record bound) .computation
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem the_complete_native_payment_books_reach_the_original_root_ledger_and_next :
    let active := activated record bound
    (read record bound).payments = paymentsFor record.menu record.reports ∧
    (root record bound).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (cursor record bound).source.val.input).toAuthoritativeRoot.toRoot ∧
    HEq ((facade record bound).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record bound).stateAt ((process record bound).successor active.state) := by
  have rooted := (facade record bound).readoutAt_factorizes (activated record bound) .computation
  exact ⟨(read record bound).payments_exact,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem the_source_generated_responsibility_fragments_reach_the_original_root_and_next :
    let active := activated record bound
    (read record bound).responsibilities = responsibilitiesFor record.menu record.reports ∧
    (root record bound).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (cursor record bound).source.val.input).toAuthoritativeRoot.toRoot ∧
    HEq ((facade record bound).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record bound).stateAt ((process record bound).successor active.state) := by
  have rooted := (facade record bound).readoutAt_factorizes (activated record bound) .computation
  exact ⟨(read record bound).responsibilities_exact,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem the_source_generated_canonical_installation_reaches_the_original_invocation :
    (read record bound).installation = installationsFor record.menu record.reports bound.index :=
  (read record bound).installation_exact

theorem the_actual_constructor_work_and_shortfall_reach_the_original_invocation :
    (read record bound).construction = constructionsFor record.menu record.reports bound.index :=
  (read record bound).construction_exact

theorem the_full_report_directory_and_accounted_choice_reach_the_original_invocation :
    (read record bound).selection = selectionsFor record.menu record.reports :=
  (read record bound).selection_exact

theorem every_old_obligation_reaches_the_same_root (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Obligation.original debt ∈ (read record bound).pending := by
  rw [(read record bound).pending_exact]
  exact every_original_obligation_is_retained record debt inside
end Runtime

abbrev AuthorityCurrent := Sigma fun network : WorldRelationNetwork => SourceNativeLivingRootCurrentAt network

noncomputable def originalNext {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
    (component : SourceNativeProjectionLaw (Online.Runtime.root cursor).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent :=
  let root := (Online.Runtime.root cursor).withProjectionCoface component
  let visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot :=
    ProgrammeHistory.temporalVisit cursor.source.val.input cursor.depth
  let generated := root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
  let successor := (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated.wholeLedgerWriteBack).get (by rfl)
  ⟨ProgrammeSource.N cursor.source.val.input,⟨ProgrammeSource.V _,root,visit.next successor.next_eq⟩⟩

noncomputable def selectedNext {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
    {all : Candidates source catalogue} {items : List (Report all)} (choice : Accounting.Selected items) (index : Index prepared)
    (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot choice.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent :=
  ⟨Responsibility.Canonical.N choice.policy.report.2 index,
    (Responsibility.Canonical.Payment.Runtime.active choice.policy.report.2 index choice.policy.first (choice.policy.paid index) component).tick.nextCurrent⟩

noncomputable def nextFor (menu : DomainResult prepared) (items : ReportsFor menu) (index : Index prepared)
    (component : SourceNativeProjectionLaw (Online.Runtime.root (executeFor menu items index)).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent := by
  cases menu with
  | empty => exact originalNext (executeFor _ items index) component
  | blocked => exact originalNext (executeFor _ items index) component
  | ready source catalogue generated all =>
      cases selected : (Accounting.compile items).verdict with
      | blocked empty => exact originalNext (executeFor _ items index) component
      | selected choice =>
          let candidate := choice.policy
          let report := candidate.report
          have same : executeFor (.ready source catalogue generated all) items index = report.2.endpoint index := by
            dsimp only [executeFor,accountedActual]
            rw [selected]
          let original : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot report.2 index).toAuthoritativeRoot.toLedgerRoot.source := Eq.mp (congrArg (fun value : Binding.NativeCursor prepared.saved[index].point => SourceNativeProjectionLaw (Online.Runtime.root value).toAuthoritativeRoot.toLedgerRoot.source) same) component
          exact selectedNext choice index original

structure Activation (input : Input seed) (point : NativePoint input) where
  private mk ::
  prepared : Prepared input
  prepared_generated : prepared = prepare input
  execution : Record prepared
  execution_generated : execution = build prepared
  observed : point.signal (position := input.position) input.site = input.reading
  bound : Binding.Linked prepared point
  binding_generated : Binding.locate prepared point = .linked bound
  snapshot : Runtime.Snapshot execution bound
  snapshot_generated : snapshot = Runtime.read execution bound

noncomputable def Activation.next {point : NativePoint input} (made : Activation input point) : AuthorityCurrent :=
  nextFor made.execution.menu made.execution.reports made.bound.index (Runtime.projectionLaw made.execution made.bound)

private def activate (input : Input seed) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) : Activation input point :=
  let prepared := prepare input
  let execution := build prepared
  match linked : Binding.locate prepared point with
  | .linked bound => ⟨prepared,rfl,execution,rfl,observed,bound,linked,Runtime.read execution bound,rfl⟩
  | .mismatch broken => False.elim (broken observed)

inductive Invocation (input : Input seed) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input point)

def invoke (input : Input seed) (point : NativePoint input) : Invocation input point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    .activated (activate input point observed)
  else .mismatch observed

theorem mismatched_observation_is_rejected_before_all_quota_generation (input : Input seed) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invoke input point = .mismatch broken := by simp only [invoke,dif_neg broken]

theorem every_actual_matching_point_is_activated_without_a_caller_selected_quota (input : Input seed) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input point,invoke input point = .activated made :=
  ⟨activate input point observed,by simp only [invoke,dif_pos observed]⟩

theorem Activation.the_automatic_planner_is_blind_to_the_actual_point {point other : NativePoint input}
    (left : Activation input point) (right : Activation input other) :
    left.prepared = right.prepared ∧ HEq left.execution right.execution := by
  have same := left.prepared_generated.trans right.prepared_generated.symm
  have transport (a b : Prepared input) (equal : a = b) : HEq (build a) (build b) := by cases equal;rfl
  exact ⟨same,(heq_of_eq left.execution_generated).trans ((transport _ _ same).trans (heq_of_eq right.execution_generated.symm))⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
namespace BodyAcquisition
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}

def ownerWeight (owner : Ready all) := Review.capacity owner+3
def remainingWeight (owners : List (Ready all)) := (owners.map ownerWeight).sum
inductive Reports (all : Candidates source catalogue) where
  | waiting (cached : List (Report all)) (remaining : List (Ready all))
      (conserved : cached++remaining.map (fun owner => ⟨owner,Joint.generate owner⟩) = Joint.reports all)
  | working (cached : List (Report all)) (owner : Ready all) (rest : List (Ready all))
      (conserved : cached++(owner::rest).map (fun item => ⟨item,Joint.generate item⟩) = Joint.reports all)
      (cursor : ReportAcquisition.State owner)
  | finished (cached : List (Report all)) (complete : cached = Joint.reports all)
def reportsInitial (all : Candidates source catalogue) : Reports all := .waiting [] (ready all) rfl
inductive ReportEvent (all : Candidates source catalogue) where
  | opened (owner : Ready all)
  | operation (owner : Ready all) (event : ReportAcquisition.Event owner)
  | cached (owner : Ready all) (made : Joint.Generated owner) (generated : made = Joint.generate owner)
  | complete (cached : List (Report all)) (generated : cached = Joint.reports all)
def reportMove : Reports all → Option (Reports all × ReportEvent all)
  | .waiting cached [] conserved =>
      let complete : cached = Joint.reports all := by simpa only [List.map_nil,List.append_nil] using conserved
      some (.finished cached complete,.complete cached complete)
  | .waiting cached (owner::rest) conserved => some (.working cached owner rest conserved (ReportAcquisition.initial owner),.opened owner)
  | .working cached owner rest conserved (.finished made generated) =>
      let report : Report all := ⟨owner,made⟩
      some (.waiting (cached++[report]) rest (by
        simpa only [report,generated,List.map_cons,List.append_assoc,List.singleton_append] using conserved),.cached owner made generated)
  | .working cached owner rest conserved cursor@(.running ..) =>
      match actual : ReportAcquisition.move owner cursor with
      | none => none
      | some (after,event) => some (.working cached owner rest conserved after,.operation owner event)
  | .finished .. => none

def Reports.rank : Reports all → Nat
  | .waiting _ remaining _ => remainingWeight remaining+1
  | .working _ _ rest _ cursor => remainingWeight rest+cursor.rank _+2
  | .finished .. => 0
def Reports.done : Reports all → Bool | .finished .. => true | _ => false
theorem report_progress {before after : Reports all} {event : ReportEvent all}
    (actual : reportMove before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | waiting cached remaining conserved =>
      cases remaining <;> dsimp only [reportMove] at actual <;> cases Option.some.inj actual
      all_goals simp only [Reports.rank,remainingWeight,ownerWeight,ReportAcquisition.initial,ReportAcquisition.State.rank,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil];omega
  | working cached owner rest conserved cursor =>
      cases cursor with
      | finished =>
          dsimp only [reportMove] at actual;cases Option.some.inj actual
          simp only [Reports.rank,ReportAcquisition.State.rank];omega
      | running =>
          dsimp only [reportMove] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := ReportAcquisition.progress owner step
            simp only [Reports.rank];omega
  | finished => cases actual

theorem report_none_iff_done (before : Reports all) : reportMove before = none ↔ before.done = true := by
  cases before with
  | waiting cached remaining conserved => cases remaining <;> simp [reportMove,Reports.done]
  | working cached owner rest conserved cursor =>
      cases cursor with
      | finished => simp [reportMove,Reports.done]
      | running left current work history balance endpoint conserved =>
          dsimp only [reportMove,Reports.done];split
          · rename_i stopped;have done := (ReportAcquisition.no_move_iff_done owner _).mp stopped;cases done
          · simp
  | finished => simp [reportMove,Reports.done]

private theorem canonical (record : Record prepared) : record = Joint.build prepared := by
  rcases record with ⟨menu,generated,items,exactItems⟩
  cases generated;cases exactItems;rfl
private def finish (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared)
    (items : ReportsFor menu) (actual : items = produceFor menu) : Record prepared := ⟨menu,generated,items,actual⟩
def weightFor : (menu : DomainResult prepared) → Nat
  | .empty .. | .blocked .. => 0
  | .ready _ _ _ all => (reportsInitial all).rank+1
inductive State (prepared : Prepared input) where
  | opening
  | reporting (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (domain : source.result = .domain catalogue) (all : Candidates source catalogue)
      (generated : DomainResult.ready source catalogue domain all = Paid.generateAll prepared) (cursor : Reports all)
  | finished (record : Record prepared) (generated : record = Joint.build prepared)
inductive Event (prepared : Prepared input) where
  | menu (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared)
  | report (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (all : Candidates source catalogue) (event : ReportEvent all)
  | complete (record : Record prepared) (generated : record = Joint.build prepared)
def move : State prepared → Option (State prepared × Event prepared)
  | .opening =>
      match actual : Paid.generateAll prepared with
      | .empty source absent =>
          let record := finish (.empty source absent) actual.symm () rfl
          some (.finished record (canonical record),.menu record.menu record.generated)
      | .blocked source cell listed broken =>
          let record := finish (.blocked source cell listed broken) actual.symm () rfl
          some (.finished record (canonical record),.menu record.menu record.generated)
      | .ready source catalogue domain all =>
          some (.reporting source catalogue domain all actual.symm (reportsInitial all),.menu (.ready source catalogue domain all) actual.symm)
  | .reporting source catalogue domain all generated (.finished cached complete) =>
      let record := finish (.ready source catalogue domain all) generated cached complete
      some (.finished record (canonical record),.complete record (canonical record))
  | .reporting source catalogue domain all generated cursor@(.waiting ..)
  | .reporting source catalogue domain all generated cursor@(.working ..) =>
      match _actual : reportMove cursor with
      | none => none
      | some (after,event) => some (.reporting source catalogue domain all generated after,.report source catalogue all event)
  | .finished .. => none

def State.rank : State prepared → Nat
  | .opening => weightFor (Paid.generateAll prepared)+1
  | .reporting _ _ _ _ _ cursor => cursor.rank+1
  | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared} {event : Event prepared}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual
      all_goals simp only [State.rank]
      all_goals simp_all only [weightFor]
      all_goals omega
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
      | waiting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := report_progress step
            simp only [State.rank];omega
      | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := report_progress step
            simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | opening => dsimp only [move,State.done];split <;> simp
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | waiting | working =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (report_none_iff_done _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end BodyAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
namespace MenuBodyAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
private theorem canonical (made : Record prepared) : made = Joint.build prepared := by
  rcases made with ⟨menu,generated,items,actual⟩;cases generated;cases actual;rfl
inductive State (prepared : Prepared input) where
  | opening
  | menu (cursor : Paid.MenuAcquisition.State prepared)
  | reporting (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (domain : source.result = .domain catalogue) (all : Candidates source catalogue)
      (generated : DomainResult.ready source catalogue domain all = Paid.generateAll prepared)
      (cursor : BodyAcquisition.Reports all)
  | finished (record : Record prepared) (generated : record = Joint.build prepared)

def continuationBound (prepared : Prepared input) := BodyAcquisition.weightFor (Paid.generateAll prepared)+1
def State.rank : State prepared → Nat
  | .opening => (Paid.MenuAcquisition.initial prepared).rank+continuationBound prepared+2
  | .menu cursor => cursor.rank+continuationBound prepared+1
  | .reporting _ _ _ _ _ cursor => cursor.rank+1
  | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
private def afterMenu (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared) : State prepared :=
  match menu with
  | .empty source absent =>
      let record : Record prepared := ⟨.empty source absent,generated,(),rfl⟩
      .finished record (canonical record)
  | .blocked source cell listed broken =>
      let record : Record prepared := ⟨.blocked source cell listed broken,generated,(),rfl⟩
      .finished record (canonical record)
  | .ready source catalogue domain all => .reporting source catalogue domain all generated (BodyAcquisition.reportsInitial all)
private theorem afterMenu_bound (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared) :
    (afterMenu menu generated).rank ≤ continuationBound prepared := by
  cases menu <;> simp only [afterMenu,State.rank,continuationBound]
  all_goals rw [←generated];simp only [BodyAcquisition.weightFor];omega
inductive Event (prepared : Prepared input) where
  | opened
  | menu (event : Paid.MenuAcquisition.Event prepared)
  | received (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared)
  | report (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (all : Candidates source catalogue) (event : BodyAcquisition.ReportEvent all)
  | complete (record : Record prepared) (generated : record = Joint.build prepared)

def move : State prepared → Option (State prepared × Event prepared)
  | .opening => some (.menu (Paid.MenuAcquisition.initial prepared),.opened)
  | .menu (.finished menu generated) => some (afterMenu menu generated,.received menu generated)
  | .menu cursor@(.source ..) | .menu cursor@(.listing ..) | .menu cursor@(.waiting ..) | .menu cursor@(.working ..) =>
      match _actual : Paid.MenuAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.menu after,.menu event)
  | .reporting source catalogue domain all generated (.finished cached complete) =>
      let record : Record prepared := ⟨.ready source catalogue domain all,generated,cached,complete⟩
      some (.finished record (canonical record),.complete record (canonical record))
  | .reporting source catalogue domain all generated cursor@(.waiting ..)
  | .reporting source catalogue domain all generated cursor@(.working ..) =>
      match _actual : BodyAcquisition.reportMove cursor with
      | none => none
      | some (after,event) => some (.reporting source catalogue domain all generated after,.report source catalogue all event)
  | .finished .. => none

theorem progress {before after : State prepared} {event : Event prepared}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | menu cursor =>
      cases cursor with
      | finished menu generated =>
          dsimp only [move] at actual;cases Option.some.inj actual
          have bound := afterMenu_bound menu generated
          apply lt_of_le_of_lt bound
          simp only [State.rank,Paid.MenuAcquisition.State.rank];omega
      | source =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.MenuAcquisition.progress step
            simp only [State.rank];omega
      | listing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.MenuAcquisition.progress step
            simp only [State.rank];omega
      | waiting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.MenuAcquisition.progress step
            simp only [State.rank];omega
      | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.MenuAcquisition.progress step
            simp only [State.rank];omega
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
      | waiting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := BodyAcquisition.report_progress step
            simp only [State.rank];omega
      | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := BodyAcquisition.report_progress step
            simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | opening | finished => simp [move,State.done]
  | menu cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | source | listing | waiting | working =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Paid.MenuAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | waiting | working =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (BodyAcquisition.report_none_iff_done _).mp stopped;cases done)
            | simp
end MenuBodyAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
namespace CandidateBodyAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
private theorem canonical (made : Record prepared) : made = Joint.build prepared := by
  rcases made with ⟨menu,generated,items,actual⟩;cases generated;cases actual;rfl
inductive State (prepared : Prepared input) where
  | opening
  | menu (cursor : Paid.CandidateMenu.State prepared)
  | reporting (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (domain : source.result = .domain catalogue) (all : Candidates source catalogue)
      (generated : DomainResult.ready source catalogue domain all = Paid.generateAll prepared)
      (cursor : BodyAcquisition.Reports all)
  | finished (record : Record prepared) (generated : record = Joint.build prepared)

def continuationBound (prepared : Prepared input) := BodyAcquisition.weightFor (Paid.generateAll prepared)+1
def State.rank : State prepared → Nat
  | .opening => (Paid.CandidateMenu.initial prepared).rank+continuationBound prepared+2
  | .menu cursor => cursor.rank+continuationBound prepared+1
  | .reporting _ _ _ _ _ cursor => cursor.rank+1
  | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
private def afterMenu (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared) : State prepared :=
  match menu with
  | .empty source absent =>
      let record : Record prepared := ⟨.empty source absent,generated,(),rfl⟩
      .finished record (canonical record)
  | .blocked source cell listed broken =>
      let record : Record prepared := ⟨.blocked source cell listed broken,generated,(),rfl⟩
      .finished record (canonical record)
  | .ready source catalogue domain all => .reporting source catalogue domain all generated (BodyAcquisition.reportsInitial all)
private theorem afterMenu_bound (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared) :
    (afterMenu menu generated).rank ≤ continuationBound prepared := by
  cases menu <;> simp only [afterMenu,State.rank,continuationBound]
  all_goals rw [←generated];simp only [BodyAcquisition.weightFor];omega
inductive Event (prepared : Prepared input) where
  | opened
  | menu (event : Paid.CandidateMenu.Event prepared)
  | received (menu : DomainResult prepared) (generated : menu = Paid.generateAll prepared)
  | report (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (all : Candidates source catalogue) (event : BodyAcquisition.ReportEvent all)
  | complete (record : Record prepared) (generated : record = Joint.build prepared)

def move : State prepared → Option (State prepared × Event prepared)
  | .opening => some (.menu (Paid.CandidateMenu.initial prepared),.opened)
  | .menu (.finished menu generated) => some (afterMenu menu generated,.received menu generated)
  | .menu cursor@(.source ..) | .menu cursor@(.listing ..) | .menu cursor@(.waiting ..) | .menu cursor@(.working ..) =>
      match _actual : Paid.CandidateMenu.move cursor with
      | none => none
      | some (after,event) => some (.menu after,.menu event)
  | .reporting source catalogue domain all generated (.finished cached complete) =>
      let record : Record prepared := ⟨.ready source catalogue domain all,generated,cached,complete⟩
      some (.finished record (canonical record),.complete record (canonical record))
  | .reporting source catalogue domain all generated cursor@(.waiting ..)
  | .reporting source catalogue domain all generated cursor@(.working ..) =>
      match _actual : BodyAcquisition.reportMove cursor with
      | none => none
      | some (after,event) => some (.reporting source catalogue domain all generated after,.report source catalogue all event)
  | .finished .. => none

theorem progress {before after : State prepared} {event : Event prepared}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | menu cursor =>
      cases cursor with
      | finished menu generated =>
          dsimp only [move] at actual;cases Option.some.inj actual
          have bound := afterMenu_bound menu generated
          apply lt_of_le_of_lt bound
          simp only [State.rank,Paid.CandidateMenu.State.rank];omega
      | source =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.CandidateMenu.progress step
            simp only [State.rank];omega
      | listing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.CandidateMenu.progress step
            simp only [State.rank];omega
      | waiting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.CandidateMenu.progress step
            simp only [State.rank];omega
      | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Paid.CandidateMenu.progress step
            simp only [State.rank];omega
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
      | waiting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := BodyAcquisition.report_progress step
            simp only [State.rank];omega
      | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := BodyAcquisition.report_progress step
            simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | opening | finished => simp [move,State.done]
  | menu cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | source | listing | waiting | working =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Paid.CandidateMenu.no_move_iff_done _).mp stopped;cases done)
            | simp
  | reporting source catalogue domain all generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | waiting | working =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (BodyAcquisition.report_none_iff_done _).mp stopped;cases done)
            | simp
end CandidateBodyAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
