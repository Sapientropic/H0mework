import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Choice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

def DecisionFor : DomainResult prepared → Type
  | .empty .. | .blocked .. => Unit
  | .ready _ _ _ all => Decision all

def decideFor : (menu : DomainResult prepared) → DecisionFor menu
  | .empty .. | .blocked .. => ()
  | .ready _ _ _ all => decideAll all

def executeMenu : (menu : DomainResult prepared) → DecisionFor menu → (index : Index prepared) → Binding.NativeCursor prepared.saved[index].point
  | .empty ..,_,index | .blocked ..,_,index => Policy.Protocol.retained prepared.saved[index].stage
  | .ready _ _ _ _,decision,index => match decision.result with
    | .selected choice => (choice.policy.view index).endpoint
    | .blocked _ => Policy.Protocol.retained prepared.saved[index].stage

theorem the_globally_selected_section_is_actually_executed {source : SourceQuota.Generated prepared}
    {catalogue : SourceQuota.Catalogue source.snapshot} (same : source.result = .domain catalogue)
    (all : Candidates source catalogue) (decision : Decision all) (choice : Choice all)
    (selected : decision.result = .selected choice) (index : Index prepared) :
    executeMenu (.ready source catalogue same all) decision index = (choice.policy.view index).endpoint := by
  simp only [executeMenu,selected]

theorem an_empty_global_policy_menu_retains_the_original_preparation {source : SourceQuota.Generated prepared}
    {catalogue : SourceQuota.Catalogue source.snapshot} (same : source.result = .domain catalogue)
    (all : Candidates source catalogue) (decision : Decision all) (empty : offers all = [])
    (blocked : decision.result = .blocked empty) (index : Index prepared) :
    executeMenu (.ready source catalogue same all) decision index = Policy.Protocol.retained prepared.saved[index].stage := by
  simp only [executeMenu,blocked]

structure Protocol (prepared : Prepared input) where
  private mk ::
  menu : DomainResult prepared
  generated : menu = generateAll prepared
  decision : DecisionFor menu

def build (prepared : Prepared input) : Protocol prepared :=
  let menu := generateAll prepared
  ⟨menu,rfl,decideFor menu⟩

abbrev Proposal : DomainResult prepared → Type
  | .empty .. | .blocked .. => Unit
  | .ready _ _ _ all => Offer all

def checkProposal : (menu : DomainResult prepared) → Proposal menu → Option (DecisionFor menu)
  | .empty ..,_ | .blocked ..,_ => none
  | .ready _ _ _ all,offer => if verified : verify all offer = true then some (decisionOfVerified all offer verified) else none

namespace Protocol
variable (record : Protocol prepared)
def endpoint (index : Index prepared) := executeMenu record.menu record.decision index

def replace (proposal : Proposal record.menu) : Option (Protocol prepared) :=
  match checkProposal record.menu proposal with
  | none => none
  | some decision => some ⟨record.menu,record.generated,decision⟩

theorem every_verified_replacement_preserves_the_entire_source_menu (proposal : Proposal record.menu)
    (next : Protocol prepared) (replaced : record.replace proposal = some next) : next.menu = record.menu := by
  unfold replace at replaced
  split at replaced
  · cases replaced
  · cases Option.some.inj replaced
    rfl
end Protocol

inductive Obligation (prepared : Prepared input) where
  | original (debt : Policy.Obligation prepared)
  | menu (source : DomainResult prepared)
  | alternatives {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
      (all : Candidates source catalogue) (debt : Debt all)
  | sourceEnumeration | sourceJoin | pointTransport | globalComparison | globalVerification
  | execution | ledgerInstallation | storage | announcement

def menuPending : DomainResult prepared → List (Obligation prepared)
  | .empty source absent => [.menu (.empty source absent)]
  | .blocked source cell listed broken => [.menu (.blocked source cell listed broken)]
  | .ready source catalogue same all => .menu (.ready source catalogue same all)::(pending all).map (.alternatives all)

def Protocol.pending (record : Protocol prepared) : List (Obligation prepared) :=
  (Policy.obligations prepared).map .original ++ menuPending record.menu ++
    [.sourceEnumeration,.sourceJoin,.pointTransport,.globalComparison,.globalVerification,
      .execution,.ledgerInstallation,.storage,.announcement]

theorem every_original_obligation_is_retained (record : Protocol prepared) (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Obligation.original debt ∈ record.pending :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨debt,inside,rfl⟩))

namespace Runtime
variable {point : NativePoint input} (record : Protocol prepared) (bound : Binding.Linked prepared point)
abbrev cursor := record.endpoint bound.index

def nativeEndpoint : Binding.NativeCursor point := bound.point_exact ▸ cursor record bound

structure Snapshot where
  private mk ::
  execution : Protocol prepared
  execution_exact : execution = record
  binding : Binding.Linked prepared point
  binding_exact : binding = bound
  pending : List (Obligation prepared)
  pending_exact : pending = record.pending
  learning : Binding.NativeCursor point
  learning_exact : learning = nativeEndpoint record bound
  whole : Evaluation (cursor record bound).source.val.code
  whole_exact : whole = Window.evaluate (cursor record bound).model (initial input point).depth
    ((cursor record bound).depth-(initial input point).depth)
  native : Authority.FullDisposition (cursor record bound).model ((cursor record bound).depth-1)
  native_exact : native = Authority.fullGenerate _ _

def generate : Snapshot record bound :=
  ⟨record,rfl,bound,rfl,record.pending,rfl,nativeEndpoint record bound,rfl,
    Window.evaluate (cursor record bound).model (initial input point).depth
      ((cursor record bound).depth-(initial input point).depth),rfl,Authority.fullGenerate _ _,rfl⟩

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

theorem the_complete_cross_quota_choice_is_consumed_with_its_actual_root_ledger_and_next :
    let active := activated record bound
    (read record bound).execution = record ∧
    (read record bound).binding = bound ∧
    (read record bound).learning = nativeEndpoint record bound ∧
    (read record bound).pending = record.pending ∧
    (read record bound).whole = Window.evaluate (cursor record bound).model (initial input point).depth
      ((cursor record bound).depth-(initial input point).depth) ∧
    (read record bound).native = Authority.fullGenerate _ _ ∧
    HEq ((facade record bound).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record bound).stateAt ((process record bound).successor active.state) := by
  have rooted := (facade record bound).readoutAt_factorizes (activated record bound) .computation
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem every_old_obligation_reaches_the_same_root (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Obligation.original debt ∈ (read record bound).pending := by
  rw [(read record bound).pending_exact]
  exact every_original_obligation_is_retained record debt inside
end Runtime

structure Activation (input : Input seed) (point : NativePoint input) where
  private mk ::
  prepared : Prepared input
  prepared_generated : prepared = prepare input
  execution : Protocol prepared
  execution_generated : execution = build prepared
  observed : point.signal (position := input.position) input.site = input.reading
  bound : Binding.Linked prepared point
  binding_generated : Binding.locate prepared point = .linked bound
  snapshot : Runtime.Snapshot execution bound
  snapshot_generated : snapshot = Runtime.read execution bound

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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
