import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)


namespace Synthesis

abbrev Rule := {control // control ∈ menu bound}
abbrev rules : List (Rule bound) := (menu bound).attach

def plan (rule : Rule bound) : Program bound budget := by
  refine ⟨List.replicate budget rule.val, List.mem_filter.mpr ⟨(mem_sequences_iff _ _ _).mpr ⟨?_,?_⟩,?_⟩⟩
  · simp only [List.length_replicate, le_refl]
  · intro control inside
    have same := (List.mem_replicate.mp inside).2
    exact same ▸ rule.property
  · simp only [List.length_replicate, decide_true]

def rows : List (Information.Row bound budget) := (worlds bound budget).flatMap fun world =>
  (Authority.Trace.Selection.rows (world.native bound budget) (world.input bound budget) world.phase.val).map (Sigma.mk world)

def axes : List (Information.Axis bound budget) := (worlds bound budget).flatMap fun world =>
  (Authority.Trace.Selection.axes (world.native bound budget) (world.input bound budget) world.phase.val).map (Sigma.mk world)

def acceptable (reference : Program bound budget) (rule : Rule bound) : Prop :=
  ∀ row ∈ rows bound budget, Information.Holds bound budget reference (plan bound budget rule) row

instance (reference : Program bound budget) (rule : Rule bound) : Decidable (acceptable bound budget reference rule) := by
  unfold acceptable; infer_instance

theorem acceptable_iff_every_world (reference : Program bound budget) (rule : Rule bound) :
    acceptable bound budget reference rule ↔ ∀ world : World bound budget,
      Authority.Trace.Selection.acceptable (world.native bound budget) (world.input bound budget) world.phase.val rfl
        (term bound budget world reference) (term bound budget world (plan bound budget rule)) := by
  constructor
  · intro all world
    apply (Authority.Trace.Selection.rows_iff _ _ _ _ _ _).mp
    intro row inside
    exact all ⟨world,row⟩ (List.mem_flatMap.mpr ⟨world,every_world_is_generated _ _ _,List.mem_map.mpr ⟨row,inside,rfl⟩⟩)
  · intro all row inside
    obtain ⟨world,_,membership⟩ := List.mem_flatMap.mp inside
    obtain ⟨localRow,generated,same⟩ := List.mem_map.mp membership
    subst row
    exact (Authority.Trace.Selection.rows_iff _ _ _ _ _ _).mpr (all world) localRow generated

structure Candidate (reference : Program bound budget) where
  rule : Rule bound
  accepted : acceptable bound budget reference rule

abbrev Candidate.programme {bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {budget : Nat} {reference : Program bound budget}
    (candidate : Candidate bound budget reference) := plan bound budget candidate.rule

def check (reference : Program bound budget) (rule : Rule bound) : Option (Candidate bound budget reference) :=
  if accepted : acceptable bound budget reference rule then some ⟨rule,accepted⟩ else none

def candidates (reference : Program bound budget) := (rules bound).filterMap (check bound budget reference)

theorem every_accepted_rule_is_generated (reference : Program bound budget) (rule : Rule bound)
    (accepted : acceptable bound budget reference rule) :
    ∃ candidate ∈ candidates bound budget reference, candidate.rule = rule := by
  refine ⟨⟨rule,accepted⟩,List.mem_filterMap.mpr ⟨rule,List.mem_attach _ _,?_⟩,rfl⟩
  simp [check,accepted]

abbrev Choice (reference : Program bound budget) := Selected (axes bound budget)
  (fun candidate : Candidate bound budget reference => Information.benefit bound budget candidate.programme)
  (candidates bound budget reference)

structure Rejection (reference : Program bound budget) (rule : Rule bound) where
  row : Information.Row bound budget
  original : row ∈ rows bound budget
  broken : ¬ Information.Holds bound budget reference (plan bound budget rule) row

inductive Outcome (reference : Program bound budget) where
  | selected (choice : Choice bound budget reference)
  | blocked (rejected : ∀ rule : Rule bound, Rejection bound budget reference rule)

def compile (reference : Program bound budget) : Outcome bound budget reference :=
  match result : choose (axes bound budget)
    (fun candidate : Candidate bound budget reference => Information.benefit bound budget candidate.programme)
      (candidates bound budget reference) with
  | some choice => .selected choice
  | none => .blocked (fun rule => match inspect
      (Information.Holds bound budget reference (plan bound budget rule)) (rows bound budget) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate,member,_⟩ := every_accepted_rule_is_generated bound budget reference rule all
          rw [empty] at member
          exact List.not_mem_nil member))

def verify (reference : Program bound budget) (rule : Rule bound) : Bool := decide (
  acceptable bound budget reference rule ∧ ∀ other ∈ rules bound, acceptable bound budget reference other →
    ¬ Improves (axes bound budget) (Information.benefit bound budget) (plan bound budget rule) (plan bound budget other))

theorem verify_iff (reference : Program bound budget) (rule : Rule bound) : verify bound budget reference rule = true ↔
    acceptable bound budget reference rule ∧ ∀ other : Rule bound, acceptable bound budget reference other →
      ¬ Improves (axes bound budget) (Information.benefit bound budget) (plan bound budget rule) (plan bound budget other) := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (List.mem_attach _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem independently_replayed_choice_is_accepted (reference : Program bound budget) (choice : Choice bound budget reference) :
    verify bound budget reference choice.policy.rule = true := by
  apply (verify_iff _ _ _ _).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro other accepted
  obtain ⟨candidate,member,same⟩ := every_accepted_rule_is_generated bound budget reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget) (Information.benefit bound budget) choice.policy.programme candidate.programme at maximal
  simpa only [Candidate.programme,same] using maximal

def Feasible (rule : Rule bound) : Prop := ∀ world : World bound budget,
  Cut.Feasible (world.source bound budget) (world.input bound budget) world.phase.val (term bound budget world (plan bound budget rule))

def NoWorse (new old : Program bound budget) : Prop := ∀ world : World bound budget,
  Authority.Trace.Selection.NoWorse (world.native bound budget) (world.input bound budget) world.phase.val rfl
    (term bound budget world new) (term bound budget world old)

abbrev BenefitNoWorse (new old : Program bound budget) :=
  Distributed.NoWorse (axes bound budget) (Information.benefit bound budget) new old
abbrev Better (old new : Program bound budget) := NoWorse bound budget new old ∧ ¬ BenefitNoWorse bound budget old new

theorem no_worse_bounds_actual_benefits (new old : Program bound budget) (bounded : NoWorse bound budget new old) :
    BenefitNoWorse bound budget new old := by
  intro axis inside
  obtain ⟨world,_,membership⟩ := List.mem_flatMap.mp inside
  obtain ⟨localAxis,generated,same⟩ := List.mem_map.mp membership
  subst axis
  exact Authority.Trace.Selection.no_worse_bounds_the_benefit_vector _ _ _ _ _ _ (bounded world) localAxis generated

theorem selected_has_no_distributed_rule_dominator (reference : Program bound budget) (choice : Choice bound budget reference)
    (other : Rule bound) (feasible : Feasible bound budget other) :
    ¬ Better bound budget choice.policy.programme (plan bound budget other) := by
  intro improves
  have own := (acceptable_iff_every_world _ _ _ _).mp choice.policy.accepted
  have accepted := (acceptable_iff_every_world bound budget reference other).mpr
    (fun world => ⟨feasible world, Distributed.noWorse_trans (improves.1 world) (own world).2⟩)
  obtain ⟨candidate,member,same⟩ := every_accepted_rule_is_generated bound budget reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget) (Information.benefit bound budget) choice.policy.programme candidate.programme at maximal
  simp only [Candidate.programme,same] at maximal
  exact maximal ⟨no_worse_bounds_actual_benefits bound budget _ _ improves.1,improves.2⟩

theorem every_distributed_rule_improvement_is_realized (reference : Program bound budget) (choice : Choice bound budget reference)
    (available : ∃ rule : Rule bound, Feasible bound budget rule ∧ Better bound budget reference (plan bound budget rule)) :
    Better bound budget reference choice.policy.programme := by
  have own := (acceptable_iff_every_world _ _ _ _).mp choice.policy.accepted
  refine ⟨fun world => (own world).2,?_⟩
  intro reverse
  obtain ⟨other,feasible,improves⟩ := available
  have accepted := (acceptable_iff_every_world bound budget reference other).mpr (fun world => ⟨feasible world,improves.1 world⟩)
  obtain ⟨candidate,member,same⟩ := every_accepted_rule_is_generated bound budget reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget) (Information.benefit bound budget) choice.policy.programme candidate.programme at maximal
  simp only [Candidate.programme,same] at maximal
  exact maximal ⟨Distributed.noWorse_trans (no_worse_bounds_actual_benefits bound budget _ _ improves.1) reverse,
    fun backward => improves.2 (Distributed.noWorse_trans reverse backward)⟩

theorem every_actual_plan_offset_uses_the_same_local_rule (rule : Rule bound) (world : World bound budget)
    (offset : Nat) (active : offset < budget-world.phase.val) :
    (term bound budget world (plan bound budget rule)).val[offset]? = some rule.val := by
  change ((List.replicate budget rule.val).take (budget-world.phase.val))[offset]? = _
  rw [List.getElem?_take_of_lt active, List.getElem?_replicate_of_lt (by omega)]


theorem strict_improvement_has_an_actual_benefit_coordinate (old new : Program bound budget)
    (improves : Better bound budget old new) :
    ∃ axis ∈ axes bound budget, Information.benefit bound budget new axis < Information.benefit bound budget old axis :=
  ((Distributed.improves_iff _ _ old new).mp
    ⟨no_worse_bounds_actual_benefits bound budget new old improves.1,improves.2⟩).2


/-- This rule table is fixed before any hidden world is selected. Each worker reads its own key. -/
def work (rule : Rule bound) (site : Fin bound.source.code.sites) (signal : Fin bound.source.code.signals) :=
  match rule.val with
  | none => []
  | some policy => bound.source.code.action policy site signal

theorem each_workers_actual_work_depends_only_on_its_own_record (rule : Rule bound)
    (site : Fin bound.source.code.sites) (first second : World bound budget)
    (same : first.observation bound budget site = second.observation bound budget site) :
    work bound rule site (first.observation bound budget site) = work bound rule site (second.observation bound budget site) :=
  congrArg (work bound rule site) same

def Locality (rule : Rule bound) (world : World bound budget) : Prop :=
  ∀ (rival : Opponent bound.source.code) (offset : Nat) (_active : offset < budget-world.phase.val)
    (site : Fin bound.source.code.sites) (event : Reaction.Choice bound.source.code)
    (_activation : event.val = .activate site)
    (_chosen : decision bound.source.code ⟨rival,budget⟩
      (Residual.run bound.source.code (Residual.scheduleAt (world.source bound budget) world.phase.val
        (term bound budget world (plan bound budget rule)).val) ⟨rival,budget⟩ (world.state bound budget) offset) = some event),
    ((Future.target (world.source bound budget) (world.input bound budget) world.phase.val rival
      (term bound budget world (plan bound budget rule)).val).actualExecution
        ((world.source bound budget).history.length+1+(world.phase.val+offset))).submitted =
      work bound rule site
        ((Residual.run bound.source.code (Residual.scheduleAt (world.source bound budget) world.phase.val
          (term bound budget world (plan bound budget rule)).val) ⟨rival,budget⟩ (world.state bound budget) offset).frame.inbox site)

theorem actual_emitted_activation_reads_only_that_workers_record (rule : Rule bound) (world : World bound budget)
    (rival : Opponent bound.source.code) (offset : Nat) (active : offset < budget-world.phase.val)
    (site : Fin bound.source.code.sites) (event : Reaction.Choice bound.source.code)
    (activation : event.val = .activate site)
    (chosen : decision bound.source.code ⟨rival,budget⟩
      (Residual.run bound.source.code (Residual.scheduleAt (world.source bound budget) world.phase.val
        (term bound budget world (plan bound budget rule)).val) ⟨rival,budget⟩ (world.state bound budget) offset) = some event) :
    ((Future.target (world.source bound budget) (world.input bound budget) world.phase.val rival
      (term bound budget world (plan bound budget rule)).val).actualExecution
        ((world.source bound budget).history.length+1+(world.phase.val+offset))).submitted =
      work bound rule site
        ((Residual.run bound.source.code (Residual.scheduleAt (world.source bound budget) world.phase.val
          (term bound budget world (plan bound budget rule)).val) ⟨rival,budget⟩ (world.state bound budget) offset).frame.inbox site) := by
  rw [Future.future_word_is_actually_submitted _ _ _ _ _ rfl offset]
  have selected := every_actual_plan_offset_uses_the_same_local_rule bound budget rule world offset active
  change word bound.source.code ((term bound budget world (plan bound budget rule)).val[offset]?.getD _)
    ⟨rival,budget⟩ _ = _
  rw [selected]
  simp only [Option.getD_some]
  unfold word work
  cases control : rule.val with
  | none => rfl
  | some policy =>
    simp only [chosen]
    rw [activation]
    rfl


def AnswerSound (world : World bound budget) (reference : Program bound budget) : Outcome bound budget reference → Prop
  | .selected choice => verify bound budget reference choice.policy.rule = true ∧
      Cut.FeasibleAgainstEveryOpponent (world.source bound budget) (world.input bound budget) world.phase.val
        (term bound budget world choice.policy.programme) ∧
      Authority.Trace.Selection.AgainstEveryOpponent (world.native bound budget) (world.input bound budget) world.phase.val rfl
        (term bound budget world choice.policy.programme) (term bound budget world reference) ∧
      (∀ other : Rule bound, Feasible bound budget other → ¬ Better bound budget choice.policy.programme (plan bound budget other)) ∧
      ((∃ other : Rule bound, Feasible bound budget other ∧ Better bound budget reference (plan bound budget other)) →
        Better bound budget reference choice.policy.programme)
  | .blocked rejected => ∀ rule, (rejected rule).row.1 ∈ worlds bound budget ∧
      (rejected rule).row.2 ∈ Authority.Trace.Selection.rows ((rejected rule).row.1.native bound budget)
        ((rejected rule).row.1.input bound budget) (rejected rule).row.1.phase.val ∧
      ¬ Information.Holds bound budget reference (plan bound budget rule) (rejected rule).row

theorem generated_distributed_answer_is_sound (world : World bound budget) (reference : Program bound budget)
    (outcome : Outcome bound budget reference) : AnswerSound bound budget world reference outcome := by
  cases outcome with
  | selected choice =>
    have safe := (acceptable_iff_every_world _ _ _ _).mp choice.policy.accepted world
    exact ⟨independently_replayed_choice_is_accepted _ _ _ choice,
      (Cut.feasibility_iff_every_future_opponent _ _ _ rfl rfl _).mp safe.1,
      (Authority.Trace.Selection.comparison_iff_every_future_opponent _ _ _ rfl rfl _ _).mp safe.2,
      selected_has_no_distributed_rule_dominator _ _ _ choice, every_distributed_rule_improvement_is_realized _ _ _ choice⟩
  | blocked rejected =>
    intro rule
    obtain ⟨source,generated,membership⟩ := List.mem_flatMap.mp (rejected rule).original
    obtain ⟨row,original,same⟩ := List.mem_map.mp membership
    have equality := congrArg (fun row : Information.Row bound budget => row.1) same
    cases equality
    have localEquality : HEq row (rejected rule).row.2 := (Sigma.mk.inj same).2
    cases localEquality
    exact ⟨generated,original,(rejected rule).broken⟩

end Synthesis


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information
