import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.SelfBudget
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Review

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code)

abbrev Supported (program : Program model.source.code) :=
  ∀ n < Whole.Complete.horizon domain,(stage model.source.code fallback program n).supported

def noWorse (new old : Program model.source.code) : Prop :=
  ∀ (world : Replanning.Point model domain) (environment : Opponent model.source.code),
    let current := Finite.actualEvaluation model world.val fallback new environment
    let prior := Finite.actualEvaluation model world.val fallback old environment
    (Authority.Trace.Lawful.inventory current.native).due.Subperm
      (Authority.Trace.Lawful.inventory prior.native).due ∧
    ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis

def improves (old new : Program model.source.code) : Prop :=
  noWorse model domain fallback new old ∧ ¬ noWorse model domain fallback old new

theorem finite_order_is_the_actual_order (pool : List (Program model.source.code))
    (new old : Program model.source.code) (newInside : new ∈ pool) (oldInside : old ∈ pool) :
    Selection.Review.noWorse model domain fallback pool new old ↔ noWorse model domain fallback new old := by
  constructor
  · intro all world environment
    exact (Finite.one_common_table_preserves_two_complete_actual_occurrences model world.val fallback pool
      (fun current prior => (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
        ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis)
      new old newInside oldInside).mp
      (all world (Replanning.every_point_is_source_generated model domain world)) environment
  · intro all world _ table _
    exact all world (Finite.opponent world.val fallback pool table)

abbrev pair (program : Program model.source.code) := [reference,program]

def Checked (program : Program model.source.code) : Prop :=
  Selection.acceptable model domain fallback (pair model reference program) reference program ∧
    Selection.Review.improves model domain fallback (pair model reference program) reference program

instance (program : Program model.source.code) : Decidable (Checked model domain fallback reference program) := by
  unfold Checked
  infer_instance

theorem checked_exact (program : Program model.source.code) :
    Checked model domain fallback reference program ↔
      Bounds.Accepted model domain fallback reference program ∧ improves model domain fallback reference program := by
  have first : reference ∈ pair model reference program := by simp only [pair,List.mem_cons_self]
  have second : program ∈ pair model reference program := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  rw [Checked,Selection.acceptable_iff_every_common_external_opponent model domain fallback _ reference program first second]
  simp only [Selection.Review.improves,improves,finite_order_is_the_actual_order model domain fallback _ program reference second first,
    finite_order_is_the_actual_order model domain fallback _ reference program first second]
  rfl

/-- The horizon is generated from the public domain; this layer has no material-floor premise. -/
def catalogue (budget : Nat) : List (Program model.source.code) :=
  (programs model.source.code budget (Whole.Complete.horizon domain)).filter
    (fun program => program.length == Whole.Complete.horizon domain)

def Within (budget : Nat) : Prop := ∃ program ∈ catalogue model domain budget,Checked model domain fallback reference program

private theorem every_menu_rule_is_supported (budget : Nat) (rule : Rule model.source.code)
    (generated : rule ∈ ruleMenu model.source.code budget) : rule.supported := by
  obtain ⟨work,inside,entry⟩ := List.mem_flatMap.mp generated
  obtain ⟨events,_,rfl⟩ := List.mem_map.mp entry
  intro policy chosen
  cases work with
  | none => cases chosen
  | some original =>
    have same : original = policy := Option.some.inj chosen
    subst policy
    have table : original ∈ List.pi model.source.code.keys (fun _ => words model.source.code.actions budget) := by
      rcases List.mem_cons.mp inside with impossible | later
      · cases impossible
      · obtain ⟨policy,member,same⟩ := List.mem_map.mp later
        cases Option.some.inj same
        exact member
    intro key inside request present
    exact (mem_words_iff _ _ _).mp ((List.mem_pi _ _).mp table key inside) |>.2 request present

theorem every_catalogue_program_uses_only_original_actions (budget : Nat) (program : Program model.source.code)
    (generated : program ∈ catalogue model domain budget) : Supported model domain fallback program := by
  obtain ⟨member,length⟩ := List.mem_filter.mp generated
  have size : program.length = Whole.Complete.horizon domain := by simpa only [beq_iff_eq] using length
  have entries := ((mem_sequences_iff _ _ _).mp member).2
  intro ordinal inside
  have bounded : ordinal < program.length := by omega
  have exactStage : stage model.source.code fallback program ordinal = program[ordinal] := by
    simp only [stage,List.getElem?_eq_getElem bounded,Option.getD_some]
  rw [exactStage]
  exact every_menu_rule_is_supported model budget _ (entries _ (List.getElem_mem bounded))

instance (budget : Nat) : Decidable (Within model domain fallback reference budget) := by
  unfold Within
  infer_instance

abbrev Available := ∃ program : Program model.source.code,
  Supported model domain fallback program ∧ Checked model domain fallback reference program

theorem a_raw_improvement_has_a_source_generated_finite_layer
    (available : Available model domain fallback reference) : ∃ budget,Within model domain fallback reference budget := by
  obtain ⟨raw,supported,checked⟩ := available
  let budget := SelfBudget.sourceCap model domain fallback raw
  let candidate := SelfBudget.representative model domain fallback raw
  have equivalent : Checked model domain fallback reference candidate := by
    apply (checked_exact model domain fallback reference candidate).mpr
    obtain ⟨accepted,better⟩ := (checked_exact model domain fallback reference raw).mp checked
    have forward : noWorse model domain fallback candidate reference ↔ noWorse model domain fallback raw reference := by
      constructor <;> intro all world environment <;>
        simpa only [candidate,SelfBudget.complete_evaluation_is_preserved] using all world environment
    have backward : noWorse model domain fallback reference candidate ↔ noWorse model domain fallback reference raw := by
      constructor <;> intro all world environment <;>
        simpa only [candidate,SelfBudget.complete_evaluation_is_preserved] using all world environment
    refine ⟨?_,forward.mpr better.1,fun contrary => better.2 (backward.mp contrary)⟩
    intro world environment
    change Synthesis.accepts _ _ (Finite.actualEvaluation model world.val fallback candidate environment) _
    rw [show candidate = SelfBudget.representative model domain fallback raw from rfl,
      SelfBudget.complete_evaluation_is_preserved]
    exact accepted world environment
  refine ⟨budget,candidate,?_,equivalent⟩
  apply List.mem_filter.mpr
  refine ⟨SelfBudget.every_supported_representative_is_generated model domain fallback raw supported,?_⟩
  simp only [candidate,normalized,List.length_map,List.length_range,beq_self_eq_true]

structure Discovery (budget : Nat) where
  program : Program model.source.code
  generated : program ∈ catalogue model domain budget
  checked : Checked model domain fallback reference program

structure Result where
  budget : Nat
  discovery : Discovery model domain fallback reference budget
  lower_refuted : ∀ smaller < budget,¬ Within model domain fallback reference smaller


inductive Enquiry (budget : Nat) where
  | found (discovery : Discovery model domain fallback reference budget)
      (minimum : Result model domain fallback reference)
      (same : minimum.discovery.program = discovery.program) (bounded : minimum.budget ≤ budget)
  | pending (refuted : ∀ program ∈ catalogue model domain budget,¬ Checked model domain fallback reference program)

/-- Existence proves termination; it does not supply the chosen program or a search bound. -/
def least (available : Available model domain fallback reference) : Nat :=
  Nat.find (a_raw_improvement_has_a_source_generated_finite_layer model domain fallback reference available)


def generate (available : Available model domain fallback reference) : Result model domain fallback reference :=
  let budget := least model domain fallback reference available
  let selected := List.chooseX (Checked model domain fallback reference) (catalogue model domain budget)
    (Nat.find_spec (a_raw_improvement_has_a_source_generated_finite_layer model domain fallback reference available))
  ⟨budget,⟨selected.val,selected.property.1,selected.property.2⟩,
    fun _ earlier => Nat.find_min (a_raw_improvement_has_a_source_generated_finite_layer model domain fallback reference available) earlier⟩

private theorem menu_is_monotone (small large : Nat) (enough : small ≤ large)
    (rule : Rule model.source.code) (inside : rule ∈ ruleMenu model.source.code small) :
    rule ∈ ruleMenu model.source.code large := by
  obtain ⟨work,member,events⟩ := List.mem_flatMap.mp inside
  apply List.mem_flatMap.mpr
  refine ⟨work,?_,events⟩
  rcases List.mem_cons.mp member with absent | present
  · exact List.mem_cons.mpr (Or.inl absent)
  · obtain ⟨policy,generated,same⟩ := List.mem_map.mp present
    apply List.mem_cons.mpr
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨policy,?_,same⟩
    apply (List.mem_pi _ _).mpr
    intro key inside
    obtain ⟨bounded,supported⟩ := (mem_words_iff _ _ _).mp ((List.mem_pi _ _).mp generated key inside)
    exact (mem_words_iff _ _ _).mpr ⟨bounded.trans enough,supported⟩

theorem catalogue_is_monotone (small large : Nat) (enough : small ≤ large)
    (program : Program model.source.code) (inside : program ∈ catalogue model domain small) :
    program ∈ catalogue model domain large := by
  obtain ⟨generated,length⟩ := List.mem_filter.mp inside
  obtain ⟨bounded,entries⟩ := (mem_sequences_iff _ _ _).mp generated
  apply List.mem_filter.mpr
  refine ⟨(mem_sequences_iff _ _ _).mpr ⟨bounded,?_⟩,length⟩
  intro rule member
  exact menu_is_monotone model small large enough rule (entries rule member)

/-- A finite successful enquiry starts the canonical search from zero; its witness cannot choose the result. -/
def inquire (budget : Nat) : Enquiry model domain fallback reference budget :=
  if found : Within model domain fallback reference budget then
    let witness := List.chooseX (Checked model domain fallback reference) (catalogue model domain budget) found
    let minimum := generate model domain fallback reference
      ⟨witness.val,every_catalogue_program_uses_only_original_actions model domain fallback budget witness.val witness.property.1,witness.property.2⟩
    have enough : minimum.budget ≤ budget := by
      by_contra absent
      exact minimum.lower_refuted budget (by omega) found
    .found ⟨minimum.discovery.program,catalogue_is_monotone model domain minimum.budget budget enough
      minimum.discovery.program minimum.discovery.generated,minimum.discovery.checked⟩ minimum rfl enough
  else .pending (fun program inside valid => found ⟨program,inside,valid⟩)

structure Observation where
  budget : Nat
  result : Enquiry model domain fallback reference budget

structure Search (budget : Nat) where
  counting : Gross.Joint.Outcome model.source.code.law (Joint.sourceAxes model) model.source.code.actions
  counting_exact : counting = Joint.countReadings model
  observations : List (Observation model domain fallback reference)
  result : Enquiry model domain fallback reference budget

/-- A pending layer is consumed by the next actual query; discovery ends this finite search. -/
def compile : (budget : Nat) → Search model domain fallback reference budget
  | 0 =>
    let result := inquire model domain fallback reference 0
    ⟨Joint.countReadings model,rfl,[⟨0,result⟩],result⟩
  | budget+1 =>
    let prior := compile budget
    match prior.result with
    | .found discovery minimum same bounded =>
      ⟨prior.counting,prior.counting_exact,prior.observations,
        .found ⟨discovery.program,catalogue_is_monotone model domain budget (budget+1) (Nat.le_succ _) discovery.program discovery.generated,
          discovery.checked⟩ minimum same (bounded.trans (Nat.le_succ _))⟩
    | .pending _ =>
      let result := inquire model domain fallback reference (budget+1)
      ⟨prior.counting,prior.counting_exact,prior.observations++[⟨budget+1,result⟩],result⟩

def Enquiry.program? {budget : Nat} : Enquiry model domain fallback reference budget → Option (Program model.source.code)
  | .found discovery _ _ _ => some discovery.program
  | .pending _ => none

theorem the_actual_compiler_eventually_finds_every_existing_raw_improvement
    (available : Available model domain fallback reference) :
    ∃ budget,∃ program : Program model.source.code,
      (compile model domain fallback reference budget).result.program? = some program ∧
      Bounds.Accepted model domain fallback reference program ∧ improves model domain fallback reference program := by
  obtain ⟨budget,raw,inside,valid⟩ := a_raw_improvement_has_a_source_generated_finite_layer model domain fallback reference available
  refine ⟨budget,?_⟩
  cases result : (compile model domain fallback reference budget).result with
  | found discovery minimum same bounded =>
    exact ⟨discovery.program,rfl,(checked_exact model domain fallback reference discovery.program).mp discovery.checked⟩
  | pending refuted => exact False.elim (refuted raw inside valid)

theorem existence_proofs_cannot_select_the_discovered_program
    (first second : Available model domain fallback reference) :
    generate model domain fallback reference first = generate model domain fallback reference second := rfl

def verify (budget : Nat) (program : Program model.source.code) : Bool :=
  decide (Checked model domain fallback reference program ∧
    ∀ smaller ∈ List.range budget,¬ Within model domain fallback reference smaller)

theorem every_generated_result_has_an_independent_review (available : Available model domain fallback reference) :
    verify model domain fallback reference (generate model domain fallback reference available).budget
      (generate model domain fallback reference available).discovery.program = true := by
  simp only [verify,decide_eq_true_eq,List.mem_range]
  exact ⟨(generate model domain fallback reference available).discovery.checked,
    (generate model domain fallback reference available).lower_refuted⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open
