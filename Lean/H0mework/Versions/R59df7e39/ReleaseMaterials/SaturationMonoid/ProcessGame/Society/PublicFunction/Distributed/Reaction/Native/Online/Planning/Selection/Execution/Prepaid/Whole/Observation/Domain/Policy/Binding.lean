import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Runtime
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
 {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
 {input : Input seed}
private def finiteTableEq {A B : Type} [DecidableEq A] [DecidableEq B] (xs : List A) :
    DecidableEq (∀ x ∈ xs, B) := fun first second =>
  if same : xs.attach.map (fun x => first x.val x.property) = xs.attach.map (fun x => second x.val x.property) then
    isTrue (funext (fun x => funext (fun inside =>
      (List.map_eq_map_iff.mp same) ⟨x,inside⟩ (List.mem_attach _ _))))
  else isFalse (fun equal => same (by subst second;rfl))

private instance : DecidableEq seed.source.code.Policy := finiteTableEq _
private instance : DecidableEq Reaction.Side := by
  intro a b;cases a <;> cases b <;> simp <;> infer_instance
private instance : DecidableEq (Reaction.Table seed.source.code) := finiteTableEq _
private instance : DecidableEq (Distributed.Recall.Information.Origin seed) := by
  intro first second
  cases first;cases second
  simp only [Distributed.Recall.Information.Origin.mk.injEq]
  infer_instance
private instance (budget : Nat) (origin : Distributed.Recall.Information.Origin seed) :
    DecidableEq (Feedback.Cut.Table (Distributed.Recall.Information.originSource seed budget origin)
      (Distributed.Recall.Information.initialInput seed budget) 0) := finiteTableEq _
private instance (budget : Nat) : DecidableEq (Distributed.Recall.Information.World seed budget) := by
  intro first second
  cases first with
  | mk origin programme rival phase =>
    cases second with
    | mk other otherProgramme otherRival otherPhase =>
      by_cases same : origin = other
      · subst other
        simp only [Distributed.Recall.Information.World.mk.injEq,true_and,heq_iff_eq]
        infer_instance
      · exact isFalse (fun equal => same (congrArg Distributed.Recall.Information.World.origin equal))
private instance : DecidableEq (Command seed) := by
  intro a b;cases a <;> cases b <;> simp <;> infer_instance
private instance (actor : P) (units : List Nat) (horizon budget : Nat) :
    DecidableEq (Point seed actor units horizon budget) := by
  intro first second
  cases first;cases second
  simp only [Point.mk.injEq]
  infer_instance

namespace Binding
variable (prepared : Prepared input) (point : NativePoint input)

def scan : Option (Index prepared) :=
  (keys prepared).find? (fun index => decide (prepared.saved[index].point = point))

theorem every_observed_actual_point_is_saved
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ index : Index prepared, prepared.saved[index].point = point := by
  have inside := (in_fiber_exactly_for_the_actual_local_signal seed input.actor input.position
    input.units input.horizon input.budget input.site input.reading point).mpr observed
  have projected : point ∈ prepared.saved.map Cell.point := by
    rw [prepared.generated]
    rw [cellsFor_preserves_every_original_point]
    exact List.mem_map.mpr ⟨⟨point,inside⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨cell,member,samePoint⟩ := List.mem_map.mp projected
  obtain ⟨index,bounded,same⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨index,bounded⟩,(congrArg Cell.point same).trans samePoint⟩

theorem scan_ne_none
    (observed : point.signal (position := input.position) input.site = input.reading) :
    scan prepared point ≠ none := by
  intro empty
  obtain ⟨index,same⟩ := every_observed_actual_point_is_saved prepared point observed
  have failed := (List.find?_eq_none.mp empty) index (List.mem_finRange index)
  exact failed (decide_eq_true same)

structure Linked where
  private mk ::
  index : Index prepared
  point_exact : prepared.saved[index].point = point
  original : scan prepared point = some index

inductive Result where
  | linked (bound : Linked prepared point)
  | mismatch (observed : point.signal (position := input.position) input.site ≠ input.reading)

def locate : Result prepared point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    match found : scan prepared point with
    | some index => .linked ⟨index,of_decide_eq_true (List.find?_some (p := fun index : Index prepared => decide (prepared.saved[index].point = point)) found),found⟩
    | none => False.elim (scan_ne_none prepared point observed found)
  else .mismatch observed

abbrev NativeCursor := Cursor (point.world.native seed input.budget) (point.world.input seed input.budget)

private theorem initial_heq {a b : NativePoint input} (same : a = b) :
    HEq (initial input a) (initial input b) := by cases same;rfl

namespace Linked
variable {prepared point} (bound : Linked prepared point) (record : Protocol prepared)
def current (_bound : Linked prepared point) : NativeCursor point := initial input point

def endpoint : NativeCursor point := bound.point_exact ▸ record.endpoint bound.index

def read := Runtime.read record bound.index

theorem current_is_the_original_trace_endpoint :
    bound.current = (point.trace (position := input.position)).endpoint := rfl

theorem the_saved_initial_current_is_the_same_actual_occurrence :
    HEq (initial input prepared.saved[bound.index].point) bound.current := by
  exact initial_heq bound.point_exact

theorem endpoint_is_the_same_cached_native_execution :
    HEq (record.endpoint bound.index) (bound.endpoint record) := by
  exact (@eqRec_heq (NativePoint input) (fun p => NativeCursor p) _ _ bound.point_exact (record.endpoint bound.index)).symm

private theorem endpoint_input_after_transport {a b : NativePoint input} (same : a = b)
    (cursor : NativeCursor a) :
    ((same ▸ cursor : NativeCursor b).source.val.input) = cursor.source.val.input := by
  cases same
  rfl

theorem bound_endpoint_keeps_the_original_root_input :
    (bound.endpoint record).source.val.input = (record.endpoint bound.index).source.val.input :=
  endpoint_input_after_transport bound.point_exact _

theorem the_bound_actual_current_consumes_the_cached_protocol_whole_ledger_and_own_next :
    let active := Runtime.activated record bound.index
    HEq (initial input prepared.saved[bound.index].point) bound.current ∧
    (bound.read record).execution = record ∧
    HEq (bound.read record).learning (bound.endpoint record) ∧
    (bound.endpoint record).source.val.input = (record.endpoint bound.index).source.val.input ∧
    (bound.read record).outstanding = obligations prepared ∧
    HEq ((Runtime.facade record bound.index).readoutAt active .computation)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (Runtime.process record bound.index).stateAt
      ((Runtime.process record bound.index).successor active.state) := by
  have consumed := Runtime.the_original_root_consumes_the_public_choice_actual_preparation_whole_responsibility_and_next
    record bound.index
  exact ⟨bound.the_saved_initial_current_is_the_same_actual_occurrence,
    consumed.1,bound.endpoint_is_the_same_cached_native_execution record,
    bound.bound_endpoint_keeps_the_original_root_input record,consumed.2.1,
    consumed.2.2.2.2.2.1,consumed.2.2.2.2.2.2.1,consumed.2.2.2.2.2.2.2⟩

end Linked
end Binding
namespace Adaptive
variable (prepared : Prepared input)
def localBenefit {point : NativePoint input} (stage : Stage input point) : Local stage → Local stage → Prop :=
  match stage with
  | .stopped _ | .blocked _ => fun _ _ => True
  | .ready scope => fun new previous =>
      ∀ rival : Opponent (initial input point).source.val.code,
        benefit (initial input point) (tensor scope input.span new rival) (tensor scope input.span previous rival)

def NoWorse (new previous : Section prepared) : Prop :=
  prepared.saved ≠ [] ∧ Coherent prepared new ∧
    ∀ index : Index prepared, allOpponentNoWorse prepared.saved[index].stage
      (readTerm prepared new index) (readTerm prepared previous index)
def Benefit (new previous : Section prepared) : Prop :=
  ∀ index : Index prepared, localBenefit prepared.saved[index].stage
    (readTerm prepared new index) (readTerm prepared previous index)
def Better (previous new : Section prepared) : Prop :=
  NoWorse prepared new previous ∧ ¬ Benefit prepared previous new

private theorem local_noWorse_iff {point : NativePoint input} (stage : Stage input point)
    (new previous : Local stage) (covered : Covered stage) :
    Policy.localNoWorse stage new previous ↔ allOpponentNoWorse stage new previous := by
  cases stage with
  | stopped _ => exact covered.elim
  | blocked _ => exact covered.elim
  | ready scope =>
    exact and_congr_right fun _ => finite_relation_iff_every_same_adaptive_opponent scope input.span
      (accepts (initial input point)) new previous covered.1 covered.2

private theorem local_benefit_iff {point : NativePoint input} (stage : Stage input point)
    (new previous : Local stage) (covered : Covered stage) :
    Policy.localBenefit stage new previous ↔ localBenefit stage new previous := by
  cases stage with
  | stopped _ => exact Iff.rfl
  | blocked _ => exact Iff.rfl
  | ready scope =>
    exact finite_relation_iff_every_same_adaptive_opponent scope input.span
      (benefit (initial input point)) new previous covered.1 covered.2

variable (record : Protocol prepared) (authorized : record.authorized = true)
include record authorized
theorem noWorse_iff (new previous : Section prepared) :
    Policy.NoWorse prepared new previous ↔ NoWorse prepared new previous := by
  constructor
  · rintro ⟨informed,coherent,all⟩
    exact ⟨informed,coherent,fun index => (local_noWorse_iff _ _ _
      (record.authorized_coverage authorized index)).mp (all index)⟩
  · rintro ⟨informed,coherent,all⟩
    exact ⟨informed,coherent,fun index => (local_noWorse_iff _ _ _
      (record.authorized_coverage authorized index)).mpr (all index)⟩
theorem benefit_iff (new previous : Section prepared) :
    Policy.Benefit prepared new previous ↔ Benefit prepared new previous := by
  constructor
  · intro all index
    exact (local_benefit_iff _ _ _ (record.authorized_coverage authorized index)).mp (all index)
  · intro all index
    exact (local_benefit_iff _ _ _ (record.authorized_coverage authorized index)).mpr (all index)

theorem selected_has_no_full_domain_adaptive_opponent_dominator
    (choice : Choice prepared (baseline prepared)) (other : Section prepared) :
    ¬ Better prepared choice.policy.term other := by
  rintro ⟨accepted,strict⟩
  exact selected_has_no_full_domain_responsibility_dominator prepared (baseline prepared) choice other
    ⟨(noWorse_iff prepared record authorized _ _).mpr accepted,
      fun reverse => strict ((benefit_iff prepared record authorized _ _).mp reverse)⟩

theorem every_available_uniform_adaptive_improvement_is_selected
    (choice : Choice prepared (baseline prepared))
    (available : ∃ other : Section prepared, Better prepared (baseline prepared) other) :
    Better prepared (baseline prepared) choice.policy.term := by
  have finite : ∃ other : Section prepared, Policy.Better prepared (baseline prepared) other := by
    obtain ⟨other,accepted,strict⟩ := available
    exact ⟨other,(noWorse_iff prepared record authorized _ _).mpr accepted,
      fun reverse => strict ((benefit_iff prepared record authorized _ _).mp reverse)⟩
  have selected := every_available_uniform_real_improvement_is_selected prepared (baseline prepared) choice finite
  exact ⟨(noWorse_iff prepared record authorized _ _).mp selected.1,
    fun reverse => selected.2 ((benefit_iff prepared record authorized _ _).mpr reverse)⟩
end Adaptive

namespace Binding.Installed
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {prepared : Prepared input} {point : NativePoint input}
  (bound : Binding.Linked prepared point) (record : Protocol prepared)
inductive Obligation where
  | original (debt : Policy.Obligation prepared)
  | sourceLookup

def obligations : List (Obligation (prepared := prepared)) :=
  .sourceLookup :: (Policy.obligations prepared).map .original

structure Snapshot where
  private mk ::
  binding : Binding.Linked prepared point
  binding_exact : binding = bound
  protocol : Protocol prepared
  protocol_exact : protocol = record
  original : Runtime.Snapshot record bound.index
  original_exact : original = Runtime.read record bound.index
  outstanding : List (Obligation (prepared := prepared))
  outstanding_exact : outstanding = obligations (prepared := prepared)
  learning : Binding.NativeCursor point
  learning_exact : learning = bound.endpoint record
  same_source : learning.source.val.input = (record.endpoint bound.index).source.val.input

def generate : Snapshot bound record :=
  ⟨bound,rfl,record,rfl,Runtime.read record bound.index,rfl,
    obligations,rfl,bound.endpoint record,rfl,bound.bound_endpoint_keeps_the_original_root_input record⟩

abbrev cursor := record.endpoint bound.index

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (cursor bound record).source.val.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (cursor bound record).source.val.input (cursor bound record).depth).current → Snapshot bound record
  project := fun _ {_} _ _ _own => generate bound record

def root := (Runtime.root record bound.index).withProjectionCoface (projectionLaw bound record)

theorem original_root_is_preserved : (root bound record).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (cursor bound record).source.val.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (cursor bound record).source.val.input) :=
  ⟨ProgrammeSource.V _,root bound record,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (cursor bound record).source.val.input) where
  State := Nat
  stateAt := stateAt bound record
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (cursor bound record).source.val.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (cursor bound record).source.val.input first).current =
        (ProgrammeHistory.visitAt (cursor bound record).source.val.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Runtime.Face)
  | binding

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (cursor bound record).source.val.input) where
  process := process bound record
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Runtime.facade record bound.index).componentAt (Runtime.facade record bound.index).seed previous
    | .binding => projectionLaw bound record
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Runtime.facade record bound.index).installationAt (Runtime.facade record bound.index).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Runtime.root record bound.index).toAuthoritativeRoot.source (projectionLaw bound record))
    | binding =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Runtime.root record bound.index).toAuthoritativeRoot.source (projectionLaw bound record)
  projectionAt := fun _ face => match face with
    | .previous previous => (Runtime.facade record bound.index).projectionAt (Runtime.facade record bound.index).seed previous
    | .binding => ()

abbrev activated := (facade bound record).seed.advance (cursor bound record).depth

theorem activated_state : (activated bound record).state = (cursor bound record).depth := by
  have all (n : Nat) : ((facade bound record).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Snapshot bound record :=
  match (facade bound record).readoutAt (activated bound record) .binding with
  | .inl output => output.2 (by
      change (ProgrammeHistory.visitAt (cursor bound record).source.val.input (activated bound record).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_the_generated_binding_and_retains_all_original_responsibilities :
    let active := activated bound record
    (read bound record).binding = bound ∧
    (read bound record).protocol = record ∧
    (read bound record).learning = bound.endpoint record ∧
    (read bound record).learning.source.val.input = (record.endpoint bound.index).source.val.input ∧
    (read bound record).original = Runtime.read record bound.index ∧
    (read bound record).outstanding = obligations (prepared := prepared) ∧
    HEq ((facade bound record).readoutAt active .binding) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process bound record).stateAt ((process bound record).successor active.state) := by
  have rooted := (facade bound record).readoutAt_factorizes (activated bound record) .binding
  exact ⟨rfl,rfl,rfl,(read bound record).same_source,rfl,rfl,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Binding.Installed
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
