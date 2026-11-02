import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (future : Opponent request.model.source.code) (rounds : Nat)
  (made : Local.Occurrence request quotas point future rounds)

abbrev model := request.model
local notation "model" => model request
abbrev start := point
local notation "start" => start request point
abbrev rival := future
local notation "rival" => rival request future
abbrev controls := made.controls
local notation "controls" => controls request quotas point future rounds made
abbrev Snapshot := Local.Output request quotas point future rounds
local notation "Snapshot" => Snapshot request quotas point future rounds
abbrev snapshot : Snapshot := made.generated
local notation "snapshot" => snapshot request quotas point future rounds made
abbrev SearchSnapshot := PaidSearch.PublicResult request quotas point future
local notation "SearchSnapshot" => SearchSnapshot request quotas point future
abbrev paidControls := made.generated.paidControls
local notation "paidControls" => paidControls request quotas point future rounds made
abbrev checkpoint := Splice.install start rival paidControls
local notation "checkpoint" => checkpoint request quotas point future rounds made

def searchAvailable (visit : Nat) := if arrival checkpoint ≤ visit then some made.generated.search else none
local notation "searchAvailable" => searchAvailable request quotas point future rounds made

abbrev cutPoint (count : Nat) := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice.install start rival ((controls).take count)

local notation "cutPoint" => cutPoint request quotas point future rounds made

abbrev full := cutPoint (controls).length

local notation "full" => full request quotas point future rounds made

abbrev source := (full).source

local notation "source" => source request quotas point future rounds made

abbrev bound := Distributed.Recall.Information.Agency.Protocol.Continuation.Replanning.native model full

local notation "bound" => bound request quotas point future rounds made

def available (visit : Nat) := if arrival full ≤ visit then some snapshot else none

local notation "available" => available request quotas point future rounds made

theorem the_generated_learning_and_root_share_one_actual_source :
    Local.full request quotas point future rounds = full := by
  change Splice.install start rival (Local.produce request quotas point future rounds).controls =
    Splice.install start rival ((controls).take (controls).length)
  rw [List.take_length]
  have same := congrArg Local.Output.controls made.exact_generation
  exact congrArg (Splice.install start rival) same.symm

local notation "the_generated_learning_and_root_share_one_actual_source" => the_generated_learning_and_root_share_one_actual_source request quotas point future rounds made

theorem the_search_checkpoint_is_an_actual_prefix_of_the_same_final_source :
    ∃ suffix, full = Splice.install checkpoint rival suffix := by
  have extended : ∃ suffix, controls = paidControls ++ suffix :=
    Local.Output.controls_extend_the_same_actual_paid_search made.generated
  obtain ⟨suffix,extended⟩ := extended
  refine ⟨suffix,?_⟩
  change Splice.install start rival ((controls).take (controls).length) = _
  rw [List.take_length,extended]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  exact List.foldl_append

theorem the_paid_search_and_later_feedback_preserve_one_complete_native_financial_prefix
    (visit : Nat) (earlier : visit ≤ arrival checkpoint) :
    Native.Coupling.Match (model).source.code (checkpoint).source.input (source).input
      (Financial.accountAt (checkpoint).source.input visit)
      (Financial.accountAt (source).input visit) := by
  obtain ⟨suffix,extended⟩ :=
    the_search_checkpoint_is_an_actual_prefix_of_the_same_final_source request quotas point future rounds made
  change Native.Coupling.Match _ _ (full).source.input _
    (Financial.accountAt (full).source.input visit)
  rw [extended]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix
    («model» := model) checkpoint rival suffix visit earlier

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source).input).restructuringSource.toLedgerSource where
  Projection := Bool
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun phase {current} _ _ => (visit : Nat) →
    current = (ProgrammeHistory.visitAt (source).input visit).current →
      (if phase then Option Snapshot else Option SearchSnapshot)
  project := fun phase {_} _ _ visit _ => match phase with
    | false => searchAvailable visit
    | true => available visit

local notation "projectionLaw" => projectionLaw request quotas point future rounds made

def root := (Native.AuthorityRuntime.root bound).withProjectionCoface
  projectionLaw

local notation "root" => root request quotas point future rounds made

theorem original_programme_root_is_preserved :
    (root).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source).input).toAuthoritativeRoot.toRoot := rfl

local notation "original_programme_root_is_preserved" => original_programme_root_is_preserved request quotas point future rounds made

def stateAt (visit : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source).input) :=
  ⟨ProgrammeSource.V (source).input,root ,
    ProgrammeHistory.temporalVisit (source).input visit⟩

local notation "stateAt" => stateAt request quotas point future rounds made

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source).input) where
  State := Nat
  «stateAt» := stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun visit => ⟨visit+1,rfl,HEq.rfl⟩

local notation "process" => process request quotas point future rounds made

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | search | learning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source).input) where
  «process» := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade bound).componentAt
        (Native.AuthorityRuntime.facade bound).seed previous
    | .search | .learning => projectionLaw
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade bound).installationAt
          (Native.AuthorityRuntime.facade bound).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root bound).toAuthoritativeRoot.source
            projectionLaw)
    | search | learning =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root bound).toAuthoritativeRoot.source
          projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade bound).projectionAt
        (Native.AuthorityRuntime.facade bound).seed previous
    | .search => false
    | .learning => true

local notation "facade" => facade request quotas point future rounds made

abbrev activated (count : Nat) := (facade).seed.advance
  (arrival (cutPoint count))

local notation "activated" => activated request quotas point future rounds made

theorem activated_state (count : Nat) :
    (activated count).state =
      arrival (cutPoint count) := by
  have state (n : Nat) : ((facade).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact state _

local notation "activated_state" => activated_state request quotas point future rounds made

def read (count : Nat) : Option Snapshot :=
  match (facade).readoutAt
    (activated count) .learning with
  | .inl actual => actual.2 (arrival (cutPoint count)) (by
      change (ProgrammeHistory.visitAt (source).input
        (activated count).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

local notation "read" => read request quotas point future rounds made

def readSearch (visit : Nat) : Option SearchSnapshot :=
  match (facade).readoutAt ((facade).seed.advance visit) .search with
  | .inl actual => actual.2 visit (by
      have state (n : Nat) : ((facade).seed.advance n).state = n := by
        induction n with
        | zero => rfl
        | succ n ih => exact congrArg Nat.succ ih
      change (ProgrammeHistory.visitAt (source).input ((facade).seed.advance visit).state).current = _
      rw [state])
  | .inr impossible => nomatch impossible

theorem search_is_released_at_its_actual_paid_checkpoint :
    readSearch request quotas point future rounds made (arrival checkpoint) = some made.generated.search := by
  change searchAvailable (arrival checkpoint) = _
  exact if_pos (Nat.le_refl _)

theorem the_final_named_read_releases_its_source_generated_outcome :
    read ((controls).length) = some snapshot := by
  change available (arrival full) = _
  exact if_pos (Nat.le_refl _)

local notation "the_final_named_read_releases_its_source_generated_outcome" => the_final_named_read_releases_its_source_generated_outcome request quotas point future rounds made

theorem no_learning_result_precedes_the_actual_paid_source (visit : Nat)
    (early : visit < arrival full) :
    available visit = none :=
  if_neg (Nat.not_le.mpr early)

local notation "no_learning_result_precedes_the_actual_paid_source" => no_learning_result_precedes_the_actual_paid_source request quotas point future rounds made

theorem each_actual_prefix_extends_to_the_same_fixed_source (count : Nat) :
    full  =
      Splice.install (cutPoint count) rival
        ((controls).drop count) := by
  change Splice.install _ rival ((controls).take _) = _
  rw [List.take_of_length_le (Nat.le_refl (controls).length)]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

local notation "each_actual_prefix_extends_to_the_same_fixed_source" => each_actual_prefix_extends_to_the_same_fixed_source request quotas point future rounds made

theorem each_actual_cut_is_the_same_visit_in_the_fixed_source (count : Nat) :
    (ProgrammeHistory.visitAt (source).input
      (arrival (cutPoint count))).current =
    (ProgrammeHistory.visitAt (cutPoint count).source.input
      (arrival (cutPoint count))).current := by
  change (ProgrammeHistory.visitAt (full).source.input _).current = _
  rw [each_actual_prefix_extends_to_the_same_fixed_source  count]
  exact Machine.actual_prefix_from_events (cutPoint count).source.input
    (Splice.install (cutPoint count) rival
      ((controls).drop count)).source.input rfl rfl
    (arrival (cutPoint count))
    (Installation.Chain.fold_keeps_every_prior_raw_event («model» := model) _ rival _) _ (Nat.le_refl _)

local notation "each_actual_cut_is_the_same_visit_in_the_fixed_source" => each_actual_cut_is_the_same_visit_in_the_fixed_source request quotas point future rounds made

theorem each_actual_prefix_preserves_its_entire_native_financial_account (count visit : Nat)
    (earlier : visit ≤ arrival (cutPoint count)) :
    Native.Coupling.Match (model).source.code (cutPoint count).source.input
      (source).input
      (Financial.accountAt (cutPoint count).source.input visit)
      (Financial.accountAt (source).input visit) := by
  change Native.Coupling.Match _ _ (full).source.input _
    (Financial.accountAt (full).source.input visit)
  rw [each_actual_prefix_extends_to_the_same_fixed_source  count]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix («model» := model) _ rival _ visit earlier

local notation "each_actual_prefix_preserves_its_entire_native_financial_account" => each_actual_prefix_preserves_its_entire_native_financial_account request quotas point future rounds made

theorem each_live_stage_is_the_next_actual_cut (count : Nat)
    (inside : count < (controls).length) :
    arrival (cutPoint (count+1)) =
      arrival (cutPoint count)+1 := by
  change arrival (Splice.install _ rival ((controls).take (count+1))) = _
  rw [List.take_succ_eq_append_getElem inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl

local notation "each_live_stage_is_the_next_actual_cut" => each_live_stage_is_the_next_actual_cut request quotas point future rounds made

theorem the_same_root_consumes_each_actual_cut_full_account_and_literal_next (count : Nat) :
    let current := activated count
    (ProgrammeHistory.visitAt (source).input
      (arrival (cutPoint count))).current =
      (ProgrammeHistory.visitAt (cutPoint count).source.input
        (arrival (cutPoint count))).current ∧
    Native.Coupling.Match (model).source.code (cutPoint count).source.input
      (source).input
      (Financial.accountAt (cutPoint count).source.input
        (arrival (cutPoint count)))
      (Financial.accountAt (source).input
        (arrival (cutPoint count))) ∧
    HEq ((facade).readoutAt current .learning)
      (current.tick.generated.projectionOutcome (.component true)) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    ((count < (controls).length) →
      current.tick.nextCurrent = (activated (count+1)).current) := by
  have rooted := (facade).readoutAt_factorizes
    (activated count) .learning
  refine ⟨each_actual_cut_is_the_same_visit_in_the_fixed_source  count,
    each_actual_prefix_preserves_its_entire_native_financial_account  count _ (Nat.le_refl _),
    rooted.2.2.2.1,rooted.2.2.1,?_⟩
  intro inside
  apply rooted.2.2.2.2.trans
  change (facade).process.stateAt
    (Nat.succ ((facade).seed.advance
      (arrival (cutPoint count))).state) = _
  have state (n : Nat) : ((facade).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  change (facade).process.stateAt
    (Nat.succ ((facade).seed.advance
      (arrival (cutPoint count))).state) =
    (facade).process.stateAt
      (((facade).seed.advance
        (arrival (cutPoint (count+1)))).state)
  rw [state,state,each_live_stage_is_the_next_actual_cut  count inside]

local notation "the_same_root_consumes_each_actual_cut_full_account_and_literal_next" => the_same_root_consumes_each_actual_cut_full_account_and_literal_next request quotas point future rounds made

theorem actual_visit (visit : Nat) : ((facade).seed.advance visit).state = visit := by
  induction visit with
  | zero => rfl
  | succ visit ih => exact congrArg Nat.succ ih
local notation "actual_visit" => actual_visit request quotas point future rounds made

theorem all_closed_faces_consume_the_same_full_ledger_and_generated_next
    (visit : Nat) (face : Face) :
    let active := (facade).seed.advance visit
    HEq ((facade).readoutAt active face)
      (active.tick.generated.projectionOutcome
        (((facade).installationAt active face).embed ((facade).projectionAt active face))) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = ((facade).seed.advance (visit+1)).current := by
  have rooted := (facade).readoutAt_factorizes ((facade).seed.advance visit) face
  refine ⟨rooted.2.2.2.1,rooted.2.2.1,?_⟩
  apply rooted.2.2.2.2.trans
  change (facade).process.stateAt (Nat.succ ((facade).seed.advance visit).state) =
    (facade).process.stateAt ((facade).seed.advance (visit+1)).state
  rw [actual_visit,actual_visit]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Runtime
