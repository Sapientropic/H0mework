import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Selection
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Feedback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

abbrev menu : List (Option bound.source.code.Policy) := none :: bound.source.code.policies.map some

def programs : List (List (Option bound.source.code.Policy)) :=
  (sequences (menu bound) budget).filter fun term => term.length = budget

abbrev Program := {term // term ∈ programs bound budget}

structure Origin where
  history : {history // history ∈ bound.source.code.histories}
  response : {table // table ∈ Reaction.tables bound.source.code}
  side : Side

def origins : List (Origin bound) := bound.source.code.histories.attach.flatMap fun history =>
  (Reaction.tables bound.source.code).attach.flatMap fun response =>
    [⟨history, response, .original⟩, ⟨history, response, .replacement⟩]

abbrev initialInput : Input bound.source.code := ⟨fun _ _ _ => none, budget⟩

abbrev originSource (origin : Origin bound) : Machine Party Good Port (Mandate.State Party Technology) Instrument where
  code := bound.source.code
  reference := bound.source.reference
  reference_generated := bound.source.reference_generated
  history := origin.history.val
  original := origin.history.property
  opponent := Reaction.respond bound.source.code origin.response.val
  side := origin.side
  feedback? := some (initialInput bound budget)

structure World where
  origin : Origin bound
  programme : Program bound budget
  rival : {table // table ∈ Cut.tables (originSource bound budget origin) (initialInput bound budget) 0}
  phase : Fin (budget + 1)

def worlds : List (World bound budget) := (origins bound).flatMap fun origin =>
  (programs bound budget).attach.flatMap fun programme =>
    (Cut.tables (originSource bound budget origin) (initialInput bound budget) 0).attach.flatMap fun rival =>
      (List.finRange (budget + 1)).map fun phase => ⟨origin, programme, rival, phase⟩

abbrev World.opponent (world : World bound budget) :=
  Cut.opponent (originSource bound budget world.origin) (initialInput bound budget) 0 world.rival.val

abbrev World.source (world : World bound budget) :=
  Future.target (originSource bound budget world.origin) (initialInput bound budget) 0
    (world.opponent bound budget) world.programme.val

abbrev World.input (world : World bound budget) :=
  Future.takeover (originSource bound budget world.origin) (initialInput bound budget) 0 (world.opponent bound budget)

abbrev World.native (world : World bound budget) : Native.Authority.Bound
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  {bound with source := world.source bound budget}

abbrev World.state (world : World bound budget) :=
  (world.source bound budget).feedbackState (world.input bound budget) world.phase.val

abbrev World.observation (world : World bound budget) (site : Fin bound.source.code.sites) :=
  (world.state bound budget).frame.inbox site

theorem every_origin_is_generated (origin : Origin bound) : origin ∈ origins bound := by
  apply List.mem_flatMap.mpr
  refine ⟨origin.history, List.mem_attach _ _, List.mem_flatMap.mpr ?_⟩
  refine ⟨origin.response, List.mem_attach _ _, ?_⟩
  cases origin with
  | mk history response side => cases side <;> simp

theorem every_world_is_generated (world : World bound budget) : world ∈ worlds bound budget := by
  apply List.mem_flatMap.mpr
  refine ⟨world.origin, every_origin_is_generated bound world.origin, List.mem_flatMap.mpr ?_⟩
  refine ⟨world.programme, List.mem_attach _ _, List.mem_flatMap.mpr ?_⟩
  exact ⟨world.rival, List.mem_attach _ _, List.mem_map.mpr ⟨world.phase, List.mem_finRange _, rfl⟩⟩

theorem every_world_uses_its_actual_native_source (world : World bound budget) :
    (world.source bound budget).feedback? = some (world.input bound budget) ∧
      (world.source bound budget).continuation = [] ∧
      (world.native bound budget).source.code.law = Mandate.law bound.base bound.scope ∧
      (world.native bound budget).source.code.task = bound.scope.task :=
  ⟨rfl, rfl, bound.law_exact, bound.task_exact⟩

theorem world_budget (world : World bound budget) :
    (world.state bound budget).remaining = budget - world.phase.val := by
  have actual := Future.the_whole_future_run_is_the_actual_state
    (originSource bound budget world.origin) (initialInput bound budget) 0
    (world.opponent bound budget) world.programme.val world.phase.val
  have rest := congrArg (fun state : State bound.source.code => state.remaining) actual
  simp only [Residual.remaining_is_the_seed_budget] at rest
  dsimp only [Residual.seed, Machine.feedbackState, Machine.feedbackInitial, initialInput] at rest
  simpa only [Nat.zero_add] using rest


private theorem menu_is_available_in_every_world (world : World bound budget)
    (control : Option bound.source.code.Policy) (inside : control ∈ menu bound) :
    control ∈ Residual.controlMenu (world.source bound budget) := by
  rcases List.mem_cons.mp inside with same | generated
  · exact same ▸ List.mem_append_left _ List.mem_cons_self
  · exact List.mem_append_right _ generated

def term (world : World bound budget) (programme : Program bound budget) :
    Cut.Term (world.source bound budget) (world.input bound budget) world.phase.val := by
  refine ⟨programme.val.take (budget - world.phase.val), (mem_sequences_iff _ _ _).mpr ⟨?_, ?_⟩⟩
  · change (programme.val.take (budget - world.phase.val)).length ≤ (world.state bound budget).remaining
    rw [world_budget]
    exact List.length_take_le _ _
  · intro control inside
    apply menu_is_available_in_every_world bound budget world control
    exact ((mem_sequences_iff _ _ _).mp (List.mem_filter.mp programme.property).1).2 control
      (List.mem_of_mem_take inside)

def cell (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals) :
    List (World bound budget) := (worlds bound budget).filter fun world => world.observation bound budget site = observation

theorem in_cell_iff (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (world : World bound budget) : world ∈ cell bound budget site observation ↔
      world.observation bound budget site = observation := by
  simp only [cell, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun same => ⟨every_world_is_generated bound budget world, same⟩⟩

abbrev Row := Sigma fun world : World bound budget =>
  Authority.Trace.Selection.Row (world.native bound budget) (world.input bound budget) world.phase.val

def rows (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals) : List (Row bound budget) :=
  (cell bound budget site observation).flatMap fun world =>
    (Authority.Trace.Selection.rows (world.native bound budget) (world.input bound budget) world.phase.val).map (Sigma.mk world)

def Holds (reference programme : Program bound budget) (row : Row bound budget) : Prop :=
  Authority.Trace.Selection.Holds (row.1.native bound budget) (row.1.input bound budget) row.1.phase.val rfl
    (term bound budget row.1 reference) (term bound budget row.1 programme) row.2

instance (reference programme : Program bound budget) (row : Row bound budget) :
    Decidable (Holds bound budget reference programme row) := by unfold Holds; infer_instance

def acceptable (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) : Prop :=
  ∀ row ∈ rows bound budget site observation, Holds bound budget reference programme row

instance (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) : Decidable (acceptable bound budget site observation reference programme) := by
  unfold acceptable; infer_instance

theorem acceptable_iff_every_compatible_world
    (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) :
    acceptable bound budget site observation reference programme ↔
      ∀ world ∈ cell bound budget site observation,
        Authority.Trace.Selection.acceptable (world.native bound budget) (world.input bound budget) world.phase.val rfl
          (term bound budget world reference) (term bound budget world programme) := by
  constructor
  · intro all world compatible
    apply (Authority.Trace.Selection.rows_iff _ _ _ _ _ _).mp
    intro row inside
    exact all ⟨world,row⟩ (List.mem_flatMap.mpr ⟨world,compatible,List.mem_map.mpr ⟨row,inside,rfl⟩⟩)
  · intro all row inside
    obtain ⟨world, compatible, membership⟩ := List.mem_flatMap.mp inside
    obtain ⟨localRow, generated, same⟩ := List.mem_map.mp membership
    subst row
    exact (Authority.Trace.Selection.rows_iff _ _ _ _ _ _).mpr (all world compatible) localRow generated

abbrev Axis := Sigma fun world : World bound budget =>
  Authority.Trace.Selection.Axis (world.native bound budget) (world.input bound budget) world.phase.val

def axes (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals) : List (Axis bound budget) :=
  (cell bound budget site observation).flatMap fun world =>
    (Authority.Trace.Selection.axes (world.native bound budget) (world.input bound budget) world.phase.val).map (Sigma.mk world)

def benefit (programme : Program bound budget) (axis : Axis bound budget) : ℚ :=
  Authority.Trace.Selection.benefitCost (axis.1.native bound budget) (axis.1.input bound budget) axis.1.phase.val rfl
    (term bound budget axis.1 programme) axis.2

structure Candidate (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) where
  programme : Program bound budget
  accepted : acceptable bound budget site observation reference programme

def check (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) : Option (Candidate bound budget site observation reference) :=
  if accepted : acceptable bound budget site observation reference programme then some ⟨programme, accepted⟩ else none

def candidates (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) :=
  (programs bound budget).attach.filterMap (check bound budget site observation reference)

theorem every_accepted_programme_is_generated (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference programme : Program bound budget)
    (accepted : acceptable bound budget site observation reference programme) :
    ∃ candidate ∈ candidates bound budget site observation reference, candidate.programme = programme := by
  refine ⟨⟨programme,accepted⟩,List.mem_filterMap.mpr ⟨programme,List.mem_attach _ _,?_⟩,rfl⟩
  simp [check, accepted]

abbrev Choice (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) :=
  Selected (axes bound budget site observation)
    (fun candidate : Candidate bound budget site observation reference => benefit bound budget candidate.programme)
    (candidates bound budget site observation reference)

structure Rejection (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) where
  row : Row bound budget
  original : row ∈ rows bound budget site observation
  broken : ¬ Holds bound budget reference programme row

inductive Outcome (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) where
  | selected (choice : Choice bound budget site observation reference)
  | blocked (rejected : ∀ programme : Program bound budget, Rejection bound budget site observation reference programme)

def compile (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) : Outcome bound budget site observation reference :=
  match result : choose (axes bound budget site observation)
    (fun candidate : Candidate bound budget site observation reference => benefit bound budget candidate.programme)
      (candidates bound budget site observation reference) with
  | some choice => .selected choice
  | none => .blocked (fun programme => match inspect (Holds bound budget reference programme) (rows bound budget site observation) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := every_accepted_programme_is_generated bound budget site observation reference programme all
          rw [empty] at member
          exact List.not_mem_nil member))

/-- A second scan reads the raw generated programmes, without calling choose. -/
def verify (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) : Bool := decide (
  acceptable bound budget site observation reference programme ∧
    ∀ other ∈ (programs bound budget).attach,
      acceptable bound budget site observation reference other →
        ¬ Improves (axes bound budget site observation) (benefit bound budget) programme other)

theorem independently_replayed_selection_is_accepted (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference : Program bound budget)
    (choice : Choice bound budget site observation reference) :
    verify bound budget site observation reference choice.policy.programme = true := by
  simp only [verify, decide_eq_true_eq]
  refine ⟨choice.policy.accepted, ?_⟩
  intro other _ accepted
  obtain ⟨candidate, member, same⟩ := every_accepted_programme_is_generated bound budget site observation reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget site observation) (benefit bound budget) choice.policy.programme candidate.programme at maximal
  simpa only [same] using maximal

/-- The chooser has no actual-world or actual-cut argument. -/
def selectedProgramme (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) : Option (Program bound budget) :=
  match compile bound budget site observation reference with
  | .selected choice => some choice.policy.programme
  | .blocked _ => none

theorem indistinguishable_actual_worlds_receive_the_same_programme (site : Fin bound.source.code.sites)
    (reference : Program bound budget) (first second : World bound budget)
    (same : first.observation bound budget site = second.observation bound budget site) :
    selectedProgramme bound budget site (first.observation bound budget site) reference =
      selectedProgramme bound budget site (second.observation bound budget site) reference := congrArg (fun observation => selectedProgramme bound budget site observation reference) same


def Feasible (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (programme : Program bound budget) : Prop :=
  ∀ world ∈ cell bound budget site observation,
    Cut.Feasible (world.source bound budget) (world.input bound budget) world.phase.val (term bound budget world programme)

def NoWorse (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (new old : Program bound budget) : Prop :=
  ∀ world ∈ cell bound budget site observation,
    Authority.Trace.Selection.NoWorse (world.native bound budget) (world.input bound budget) world.phase.val rfl
      (term bound budget world new) (term bound budget world old)

abbrev BenefitNoWorse (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (new old : Program bound budget) := Distributed.NoWorse (axes bound budget site observation) (benefit bound budget) new old

abbrev Better (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (old new : Program bound budget) :=
  NoWorse bound budget site observation new old ∧ ¬ BenefitNoWorse bound budget site observation old new

theorem no_worse_trans (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (first middle last : Program bound budget) (forward : NoWorse bound budget site observation first middle)
    (prior : NoWorse bound budget site observation middle last) : NoWorse bound budget site observation first last :=
  fun world compatible => Distributed.noWorse_trans (forward world compatible) (prior world compatible)

theorem no_worse_bounds_all_actual_benefits (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (new old : Program bound budget)
    (bounded : NoWorse bound budget site observation new old) : BenefitNoWorse bound budget site observation new old := by
  intro axis inside
  obtain ⟨world, compatible, membership⟩ := List.mem_flatMap.mp inside
  obtain ⟨localAxis, generated, same⟩ := List.mem_map.mp membership
  subst axis
  exact Authority.Trace.Selection.no_worse_bounds_the_benefit_vector _ _ _ _ _ _ (bounded world compatible) localAxis generated

theorem accepted_iff_feasible_and_no_worse (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference programme : Program bound budget) :
    acceptable bound budget site observation reference programme ↔
      Feasible bound budget site observation programme ∧ NoWorse bound budget site observation programme reference := by
  rw [acceptable_iff_every_compatible_world]
  exact ⟨fun all => ⟨fun world member => (all world member).1, fun world member => (all world member).2⟩,
    fun all world member => ⟨all.1 world member, all.2 world member⟩⟩

theorem selected_has_no_information_feasible_dominator (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference : Program bound budget)
    (choice : Choice bound budget site observation reference) (other : Program bound budget)
    (feasible : Feasible bound budget site observation other) :
    ¬ Better bound budget site observation choice.policy.programme other := by
  intro improves
  have own := (accepted_iff_feasible_and_no_worse bound budget site observation reference choice.policy.programme).mp choice.policy.accepted
  have accepted := (accepted_iff_feasible_and_no_worse bound budget site observation reference other).mpr
    ⟨feasible, no_worse_trans bound budget site observation _ _ _ improves.1 own.2⟩
  obtain ⟨candidate, member, same⟩ := every_accepted_programme_is_generated bound budget site observation reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget site observation) (benefit bound budget) choice.policy.programme candidate.programme at maximal
  rw [same] at maximal
  exact maximal ⟨no_worse_bounds_all_actual_benefits bound budget site observation _ _ improves.1, improves.2⟩

theorem every_information_feasible_improvement_is_realized (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference : Program bound budget)
    (choice : Choice bound budget site observation reference)
    (available : ∃ other : Program bound budget, Feasible bound budget site observation other ∧
      Better bound budget site observation reference other) :
    Better bound budget site observation reference choice.policy.programme := by
  have own := (accepted_iff_feasible_and_no_worse bound budget site observation reference choice.policy.programme).mp choice.policy.accepted
  refine ⟨own.2, ?_⟩
  intro reverse
  obtain ⟨other, feasible, improves⟩ := available
  have accepted := (accepted_iff_feasible_and_no_worse bound budget site observation reference other).mpr ⟨feasible,improves.1⟩
  obtain ⟨candidate, member, same⟩ := every_accepted_programme_is_generated bound budget site observation reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound budget site observation) (benefit bound budget) choice.policy.programme candidate.programme at maximal
  rw [same] at maximal
  exact maximal ⟨Distributed.noWorse_trans
    (no_worse_bounds_all_actual_benefits bound budget site observation _ _ improves.1) reverse,
    fun backward => improves.2 (Distributed.noWorse_trans reverse backward)⟩

theorem rejection_names_a_compatible_actual_world_and_original_row
    (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget)
    (rejected : Rejection bound budget site observation reference programme) :
    rejected.row.1.observation bound budget site = observation ∧
      rejected.row.2 ∈ Authority.Trace.Selection.rows (rejected.row.1.native bound budget)
        (rejected.row.1.input bound budget) rejected.row.1.phase.val ∧
      ¬ Holds bound budget reference programme rejected.row := by
  obtain ⟨world, compatible, membership⟩ := List.mem_flatMap.mp rejected.original
  obtain ⟨localRow, original, same⟩ := List.mem_map.mp membership
  have equality := congrArg (fun row : Row bound budget => row.1) same
  cases equality
  have localEquality : HEq localRow rejected.row.2 := (Sigma.mk.inj same).2
  cases localEquality
  exact ⟨(in_cell_iff bound budget site observation _).mp compatible, original, rejected.broken⟩

theorem verify_iff (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) : verify bound budget site observation reference programme = true ↔
      acceptable bound budget site observation reference programme ∧
        ∀ other : Program bound budget, acceptable bound budget site observation reference other →
          ¬ Improves (axes bound budget site observation) (benefit bound budget) programme other := by
  simp only [verify, decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (List.mem_attach _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

def choiceOfVerified (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference programme : Program bound budget) (verified : verify bound budget site observation reference programme = true) :
    Choice bound budget site observation reference := by
  have checked := (verify_iff bound budget site observation reference programme).mp verified
  let candidate : Candidate bound budget site observation reference := ⟨programme,checked.1⟩
  refine ⟨candidate, List.mem_filterMap.mpr ⟨programme,List.mem_attach _ _,?_⟩,?_⟩
  · simp [check, checked.1, candidate]
  · intro other _
    exact checked.2 other.programme other.accepted

theorem verified_choice_keeps_the_submitted_programme (site : Fin bound.source.code.sites)
    (observation : Fin bound.source.code.signals) (reference programme : Program bound budget)
    (verified : verify bound budget site observation reference programme = true) :
    (choiceOfVerified bound budget site observation reference programme verified).policy.programme = programme := rfl


theorem every_generated_programme_is_supported_at_the_original_cut
    (origin : Origin bound) (programme : Program bound budget) :
    programme.val ∈ Residual.scheduleTerms (originSource bound budget origin) (initialInput bound budget) 0 := by
  apply (mem_sequences_iff _ _ _).mpr
  obtain ⟨member, length⟩ := List.mem_filter.mp programme.property
  obtain ⟨bounded,supported⟩ := (mem_sequences_iff _ _ _).mp member
  refine ⟨bounded, ?_⟩
  intro control inside
  rcases List.mem_cons.mp (supported control inside) with same | generated
  · exact same ▸ List.mem_append_left _ List.mem_cons_self
  · exact List.mem_append_right _ generated

/-- A single finite table covers all generated programmes, even for a fully adaptive rival. -/
abbrev realizedWorld (origin : Origin bound) (programme : Program bound budget)
    (rival : Opponent bound.source.code) (phase : Fin (budget + 1)) : World bound budget where
  origin := origin
  programme := programme
  rival := ⟨Residual.restrict bound.source.code
    (Residual.seed (originSource bound budget origin) (initialInput bound budget) 0)
    (Residual.schedules (originSource bound budget origin) (initialInput bound budget) 0) rival,
    Residual.restriction_is_generated _ _ _ rival⟩
  phase := phase

theorem every_actual_adaptive_prefix_has_a_generated_world
    (origin : Origin bound) (programme : Program bound budget)
    (rival : Opponent bound.source.code) (phase : Fin (budget + 1)) :
    let world := realizedWorld bound budget origin programme rival phase
    world ∈ worlds bound budget ∧ world.state bound budget =
      (Future.target (originSource bound budget origin) (initialInput bound budget) 0 rival programme.val).feedbackState
        (Future.takeover (originSource bound budget origin) (initialInput bound budget) 0 rival) phase.val := by
  refine ⟨every_world_is_generated _ _ _, ?_⟩
  let source := originSource bound budget origin
  let input := initialInput bound budget
  have generated : Residual.scheduleAt source 0 programme.val ∈ Residual.schedules source input 0 :=
    List.mem_map.mpr ⟨programme.val,
      every_generated_programme_is_supported_at_the_original_cut bound budget origin programme,rfl⟩
  have covered := Residual.one_restriction_preserves_the_whole_remaining_run bound.source.code
    (Residual.seed source input 0) (Residual.schedules source input 0)
    (Residual.scheduleAt source 0 programme.val) generated ⟨rival,budget⟩ phase.val (by
      change phase.val ≤ budget
      omega)
  have first := Future.the_whole_future_run_is_the_actual_state source input 0
    ((realizedWorld bound budget origin programme rival phase).opponent bound budget) programme.val phase.val
  have second := Future.the_whole_future_run_is_the_actual_state source input 0 rival programme.val phase.val
  simpa only [Nat.zero_add] using first.trans (covered.trans second.symm)

theorem choice_is_safe_in_every_compatible_world_against_every_future_opponent
    (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) (choice : Choice bound budget site observation reference)
    (world : World bound budget) (compatible : world.observation bound budget site = observation) :
    Cut.FeasibleAgainstEveryOpponent (world.source bound budget) (world.input bound budget) world.phase.val
        (term bound budget world choice.policy.programme) ∧
      Authority.Trace.Selection.AgainstEveryOpponent (world.native bound budget) (world.input bound budget) world.phase.val rfl
        (term bound budget world choice.policy.programme) (term bound budget world reference) := by
  have accepted := (acceptable_iff_every_compatible_world bound budget site observation reference choice.policy.programme).mp
    choice.policy.accepted world ((in_cell_iff bound budget site observation world).mpr compatible)
  exact ⟨(Cut.feasibility_iff_every_future_opponent _ _ _ rfl rfl _).mp accepted.1,
    (Authority.Trace.Selection.comparison_iff_every_future_opponent _ _ _ rfl rfl _ _).mp accepted.2⟩

theorem a_common_feasible_reference_cannot_be_information_blocked
    (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (reference : Program bound budget) (feasible : Feasible bound budget site observation reference)
    (rejected : ∀ programme : Program bound budget, Rejection bound budget site observation reference programme) : False := by
  have accepted := (accepted_iff_feasible_and_no_worse bound budget site observation reference reference).mpr
    ⟨feasible, fun _ _ _ _ => le_refl _⟩
  exact (rejected reference).broken (accepted (rejected reference).row (rejected reference).original)


theorem strict_improvement_names_an_actual_benefit_coordinate
    (site : Fin bound.source.code.sites) (observation : Fin bound.source.code.signals)
    (old new : Program bound budget) (improves : Better bound budget site observation old new) :
    ∃ axis ∈ axes bound budget site observation, benefit bound budget new axis < benefit bound budget old axis :=
  ((Distributed.improves_iff _ _ old new).mp
    ⟨no_worse_bounds_all_actual_benefits bound budget site observation new old improves.1, improves.2⟩).2

def AnswerSound (world : World bound budget) (site : Fin bound.source.code.sites)
    (reference : Program bound budget) : Outcome bound budget site (world.observation bound budget site) reference → Prop
  | .selected choice =>
      verify bound budget site (world.observation bound budget site) reference choice.policy.programme = true ∧
      Cut.FeasibleAgainstEveryOpponent (world.source bound budget) (world.input bound budget) world.phase.val
        (term bound budget world choice.policy.programme) ∧
      Authority.Trace.Selection.AgainstEveryOpponent (world.native bound budget) (world.input bound budget) world.phase.val rfl
        (term bound budget world choice.policy.programme) (term bound budget world reference) ∧
      (∀ other : Program bound budget, Feasible bound budget site (world.observation bound budget site) other →
        ¬ Better bound budget site (world.observation bound budget site) choice.policy.programme other) ∧
      ((∃ other : Program bound budget, Feasible bound budget site (world.observation bound budget site) other ∧
        Better bound budget site (world.observation bound budget site) reference other) →
          Better bound budget site (world.observation bound budget site) reference choice.policy.programme)
  | .blocked rejected => ∀ programme,
      (rejected programme).row.1.observation bound budget site = world.observation bound budget site ∧
        (rejected programme).row.2 ∈ Authority.Trace.Selection.rows ((rejected programme).row.1.native bound budget)
          ((rejected programme).row.1.input bound budget) (rejected programme).row.1.phase.val ∧
        ¬ Holds bound budget reference programme (rejected programme).row

theorem actual_observation_compiler_is_sound (world : World bound budget) (site : Fin bound.source.code.sites)
    (reference : Program bound budget)
    (outcome : Outcome bound budget site (world.observation bound budget site) reference) :
    AnswerSound bound budget world site reference outcome := by
  cases outcome with
  | selected choice =>
    have safe := choice_is_safe_in_every_compatible_world_against_every_future_opponent
      bound budget site (world.observation bound budget site) reference choice world rfl
    exact ⟨independently_replayed_selection_is_accepted _ _ _ _ _ choice,safe.1,safe.2,
      selected_has_no_information_feasible_dominator _ _ _ _ _ choice,
      every_information_feasible_improvement_is_realized _ _ _ _ _ choice⟩
  | blocked rejected => exact fun programme =>
      rejection_names_a_compatible_actual_world_and_original_row _ _ _ _ _ _ (rejected programme)


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information
