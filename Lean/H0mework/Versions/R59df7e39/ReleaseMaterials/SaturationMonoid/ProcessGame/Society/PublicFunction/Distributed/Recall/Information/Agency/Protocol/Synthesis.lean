import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

namespace Synthesis

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

abbrev TableAt (world : World model budget) :=
  {table : Cut.Table (world.source model budget) (world.input model budget) world.phase.val //
    table ∈ Cut.tables (world.source model budget) (world.input model budget) world.phase.val}

abbrev EconomicAt (world : World model budget) :=
  {axis : EconomicAxis model.source.code // axis ∈ economicAxes (world.source model budget) world.phase.val}

@[inline] def readTable (world : World model budget) (protocol : Rule model.source.code) (table : TableAt model budget world) :=
  tableEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl protocol table.val

inductive Test (world : World model budget) where
  | legal | complete | profile | native
  | economic (axis : EconomicAt model budget world)

def tests (world : World model budget) : List (Test model budget world) :=
  [.legal,.complete,.profile,.native] ++ (economicAxes (world.source model budget) world.phase.val).attach.map Test.economic

theorem every_test_is_generated (world : World model budget) (test : Test model budget world) : test ∈ tests model budget world := by
  cases test with
  | legal => simp [tests]
  | complete => simp [tests]
  | profile => simp [tests]
  | native => simp [tests]
  | economic axis => exact List.mem_append_right _ (List.mem_map.mpr ⟨axis,List.mem_attach _ _,rfl⟩)

structure Row where
  world : World model budget
  table : TableAt model budget world
  test : Test model budget world

def rows : List (Row model budget) := (worlds model budget).flatMap fun world =>
  (Cut.tables (world.source model budget) (world.input model budget) world.phase.val).attach.flatMap fun table =>
    (tests model budget world).map fun test => ⟨world,table,test⟩

theorem every_row_is_source_generated (row : Row model budget) : row ∈ rows model budget := by
  rcases row with ⟨world,table,test⟩
  exact List.mem_flatMap.mpr ⟨world,every_world_is_generated _ _ _,List.mem_flatMap.mpr
    ⟨table,List.mem_attach _ _,List.mem_map.mpr ⟨test,every_test_is_generated _ _ _ _,rfl⟩⟩⟩

def holds (reference protocol : Rule model.source.code) (row : Row model budget) : Prop :=
  let current := readTable model budget row.world protocol row.table
  let original := readTable model budget row.world reference row.table
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = original.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native original.native
  | .economic axis => current.value axis.val ≤ original.value axis.val

instance (reference protocol : Rule model.source.code) (row : Row model budget) : Decidable (holds model budget reference protocol row) := by
  unfold holds
  cases row.test <;> infer_instance

def accepts (coordinates : List (EconomicAxis code)) (new old : Evaluation code) : Prop :=
  new.legal = true ∧ new.complete = true ∧ new.profile = old.profile ∧
    Authority.Trace.Lawful.NoWorse new.native old.native ∧
      ∀ axis ∈ coordinates, new.value axis ≤ old.value axis

instance (coordinates : List (EconomicAxis code)) (new old : Evaluation code) : Decidable (accepts code coordinates new old) := by
  unfold accepts
  infer_instance

omit [DecidableEq Port] [DecidableEq Technology] in
theorem accepts_trans (coordinates : List (EconomicAxis code)) (first middle last : Evaluation code)
    (left : accepts code coordinates first middle) (right : accepts code coordinates middle last) :
    accepts code coordinates first last :=
  ⟨left.1,left.2.1,left.2.2.1.trans right.2.2.1,Authority.Trace.Lawful.trans left.2.2.2.1 right.2.2.2.1,
    fun axis inside => (left.2.2.2.2 axis inside).trans (right.2.2.2.2 axis inside)⟩

def acceptable (reference protocol : Rule model.source.code) : Prop :=
  ∀ row ∈ rows model budget, holds model budget reference protocol row

theorem acceptable_iff_every_generated_world (reference protocol : Rule model.source.code) :
    acceptable model budget reference protocol ↔ ∀ (world : World model budget) (table : TableAt model budget world),
      accepts model.source.code (economicAxes (world.source model budget) world.phase.val)
        (readTable model budget world protocol table) (readTable model budget world reference table) := by
  constructor
  · intro all world table
    refine ⟨all ⟨world,table,.legal⟩ (every_row_is_source_generated _ _ _),
      all ⟨world,table,.complete⟩ (every_row_is_source_generated _ _ _),
      all ⟨world,table,.profile⟩ (every_row_is_source_generated _ _ _),
      all ⟨world,table,.native⟩ (every_row_is_source_generated _ _ _),?_⟩
    intro axis inside
    exact all ⟨world,table,.economic ⟨axis,inside⟩⟩ (every_row_is_source_generated _ _ _)
  · intro all row _
    rcases row with ⟨world,table,test⟩
    cases test with
    | legal => exact (all world table).1
    | complete => exact (all world table).2.1
    | profile => exact (all world table).2.2.1
    | native => exact (all world table).2.2.2.1
    | economic axis => exact (all world table).2.2.2.2 axis.val axis.property


/-- Generate each complete evaluation once per world/table pair before testing its fields. -/
def packed (reference protocol : Rule model.source.code) : Prop :=
  ∀ world ∈ worlds model budget,
    ∀ table ∈ Cut.tables (world.source model budget) (world.input model budget) world.phase.val,
      accepts model.source.code (economicAxes (world.source model budget) world.phase.val)
        (tableEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl protocol table)
        (tableEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl reference table)

theorem acceptable_iff_packed (reference protocol : Rule model.source.code) :
    acceptable model budget reference protocol ↔ packed model budget reference protocol := by
  rw [acceptable_iff_every_generated_world]
  constructor
  · intro all world _ table original
    exact all world ⟨table,original⟩
  · intro all world table
    exact all world (every_world_is_generated model budget world) table.val table.property

instance decidableAcceptable (reference protocol : Rule model.source.code) : Decidable (acceptable model budget reference protocol) := by
  letI : Decidable (packed model budget reference protocol) := by unfold packed; infer_instance
  exact decidable_of_iff (packed model budget reference protocol) (acceptable_iff_packed model budget reference protocol).symm

theorem acceptable_trans (first middle last : Rule model.source.code)
    (left : acceptable model budget middle first) (right : acceptable model budget last middle) :
    acceptable model budget last first := by
  apply (acceptable_iff_every_generated_world _ _ _ _).mpr
  intro world table
  exact accepts_trans _ _ _ _ _ ((acceptable_iff_every_generated_world _ _ _ _).mp left world table)
    ((acceptable_iff_every_generated_world _ _ _ _).mp right world table)

theorem acceptable_iff_every_common_external_opponent (reference protocol : Rule model.source.code) :
    acceptable model budget reference protocol ↔ ∀ (world : World model budget) (rival : Opponent model.source.code),
      accepts model.source.code (economicAxes (world.source model budget) world.phase.val)
        (actualEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl protocol rival)
        (actualEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl reference rival) := by
  rw [acceptable_iff_every_generated_world]
  apply forall_congr'
  intro world
  constructor
  · intro finite
    apply (finite_relation_iff_same_external_adaptive_opponent (world.native model budget) (world.input model budget) world.phase.val rfl rfl
      (accepts model.source.code (economicAxes (world.source model budget) world.phase.val)) protocol reference).mp
    intro table generated
    exact finite ⟨table,generated⟩
  · intro all table
    have finite := (finite_relation_iff_same_external_adaptive_opponent (world.native model budget) (world.input model budget) world.phase.val rfl rfl
      (accepts model.source.code (economicAxes (world.source model budget) world.phase.val)) protocol reference).mpr all
    exact finite table.val table.property

inductive Axis where
  | economic (world : World model budget) (table : TableAt model budget world) (axis : EconomicAt model budget world)
  | native (world : World model budget) (table : TableAt model budget world) (anchor : Rule model.source.code)

def axes : List (Axis model budget) := (worlds model budget).flatMap fun world =>
  (Cut.tables (world.source model budget) (world.input model budget) world.phase.val).attach.flatMap fun table =>
    (economicAxes (world.source model budget) world.phase.val).attach.map (Axis.economic world table) ++
      (rules model.source.code).map (Axis.native world table)

def benefit (protocol : Rule model.source.code) : Axis model budget → ℚ
  | .economic world table axis => (readTable model budget world protocol table).value axis.val
  | .native world table anchor =>
      if (Authority.Trace.Lawful.inventory (readTable model budget world protocol table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (readTable model budget world anchor table).native).due then 0 else 1

theorem acceptance_bounds_every_benefit (reference protocol : Rule model.source.code)
    (accepted : acceptable model budget reference protocol) :
    Distributed.NoWorse (axes model budget) (benefit model budget) protocol reference := by
  intro axis _
  cases axis with
  | economic world table axis =>
    exact ((acceptable_iff_every_generated_world _ _ _ _).mp accepted world table).2.2.2.2 axis.val axis.property
  | native world table anchor =>
    have native := ((acceptable_iff_every_generated_world _ _ _ _).mp accepted world table).2.2.2.1
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
    by_cases old : (Authority.Trace.Lawful.inventory (readTable model budget world reference table).native).due.Subperm
      (Authority.Trace.Lawful.inventory (readTable model budget world anchor table).native).due
    · have new := native.2.trans old
      simp only [if_pos old,if_pos new,le_refl]
    · split <;> simp_all

structure Candidate (reference : Rule model.source.code) where
  protocol : Rule model.source.code
  accepted : acceptable model budget reference protocol

def check (reference protocol : Rule model.source.code) : Option (Candidate model budget reference) :=
  if accepted : acceptable model budget reference protocol then some ⟨protocol,accepted⟩ else none

def candidates (reference : Rule model.source.code) :=
  (rules model.source.code).filterMap (check model budget reference)

theorem every_accepted_protocol_is_generated (reference protocol : Rule model.source.code)
    (accepted : acceptable model budget reference protocol) :
    ∃ candidate ∈ candidates model budget reference, candidate.protocol = protocol := by
  refine ⟨⟨protocol,accepted⟩,List.mem_filterMap.mpr ⟨protocol,every_rule_is_source_generated _ _,?_⟩,rfl⟩
  simp only [check,dif_pos accepted]

abbrev Choice (reference : Rule model.source.code) := Selected (axes model budget)
  (fun candidate : Candidate model budget reference => benefit model budget candidate.protocol) (candidates model budget reference)

structure Rejection (reference protocol : Rule model.source.code) where
  row : Row model budget
  original : row ∈ rows model budget
  broken : ¬ holds model budget reference protocol row

inductive Outcome (reference : Rule model.source.code) where
  | selected (choice : Choice model budget reference)
  | blocked (rejected : ∀ protocol : Rule model.source.code, Rejection model budget reference protocol)

def compile (reference : Rule model.source.code) : Outcome model budget reference :=
  match result : choose (axes model budget) (fun candidate : Candidate model budget reference => benefit model budget candidate.protocol)
    (candidates model budget reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol => match inspect (holds model budget reference protocol) (rows model budget) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted accepted => False.elim (by
          have witness := every_accepted_protocol_is_generated model budget reference protocol accepted
          rw [choose_none_iff_empty] at result
          obtain ⟨candidate,inside,_⟩ := witness
          simp only [result,List.not_mem_nil] at inside))

def verify (reference protocol : Rule model.source.code) : Bool :=
  decide (acceptable model budget reference protocol ∧ ∀ other ∈ rules model.source.code,
    acceptable model budget reference other →
      ¬ Distributed.Improves (axes model budget) (benefit model budget) protocol other)

theorem selected_has_no_full_responsibility_dominator (reference : Rule model.source.code)
    (choice : Choice model budget reference) (other : Rule model.source.code)
    (accepted : acceptable model budget choice.policy.protocol other) :
    ¬ Distributed.Improves (axes model budget) (benefit model budget) choice.policy.protocol other := by
  have original := acceptable_trans model budget other choice.policy.protocol reference accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model budget reference other original
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model budget) (benefit model budget) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_full_responsibility_improvement_is_realized (reference : Rule model.source.code)
    (choice : Choice model budget reference)
    (available : ∃ other : Rule model.source.code, acceptable model budget reference other ∧
      Distributed.Improves (axes model budget) (benefit model budget) reference other) :
    Distributed.Improves (axes model budget) (benefit model budget) reference choice.policy.protocol := by
  constructor
  · exact acceptance_bounds_every_benefit model budget reference choice.policy.protocol choice.policy.accepted
  · intro backward
    obtain ⟨other,accepted,better⟩ := available
    obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model budget reference other accepted
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (axes model budget) (benefit model budget) choice.policy.protocol candidate.protocol at maximal
    rw [same] at maximal
    apply maximal
    constructor
    · intro axis member
      exact (better.1 axis member).trans (backward axis member)
    · intro reverse
      apply better.2
      intro axis member
      exact (backward axis member).trans (reverse axis member)


theorem verify_iff (reference protocol : Rule model.source.code) :
    verify model budget reference protocol = true ↔ acceptable model budget reference protocol ∧
      ∀ other : Rule model.source.code, acceptable model budget reference other →
        ¬ Distributed.Improves (axes model budget) (benefit model budget) protocol other := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (every_rule_is_source_generated _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem independently_replayed_choice_is_accepted (reference : Rule model.source.code)
    (choice : Choice model budget reference) : verify model budget reference choice.policy.protocol = true := by
  apply (verify_iff model budget reference choice.policy.protocol).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro other accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model budget reference other accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model budget) (benefit model budget) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_verified_protocol_protects_its_own_actual_full_responsibility
    (reference protocol : Rule model.source.code) (checked : verify model budget reference protocol = true)
    (world : World model budget) (rival : Opponent model.source.code) :
    accepts model.source.code (economicAxes (world.source model budget) world.phase.val)
      (actualEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl protocol rival)
      (actualEvaluation (world.native model budget) (world.input model budget) world.phase.val rfl reference rival) :=
  (acceptable_iff_every_common_external_opponent model budget reference protocol).mp
    ((verify_iff model budget reference protocol).mp checked).1 world rival

theorem strict_improvement_has_an_actual_responsibility_coordinate (old new : Rule model.source.code)
    (better : Distributed.Improves (axes model budget) (benefit model budget) old new) :
    ∃ axis ∈ axes model budget, benefit model budget new axis < benefit model budget old axis :=
  ((Distributed.improves_iff (axes model budget) (benefit model budget) old new).mp better).2

end Synthesis
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol
