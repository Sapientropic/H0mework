import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (pool : List (Program model.source.code))


abbrev TableAt (world : Replanning.Point model domain) :=
  {table : Finite.Table world.val original pool // table ∈ Finite.tables world.val original pool}

structure Row where
  world : Replanning.Point model domain
  table : TableAt model domain original pool world
  test : Replanning.Test model domain world

def rows : List (Row model domain original pool) := (Replanning.points model domain).flatMap fun world =>
  (Finite.tables world.val original pool).attach.flatMap fun table =>
    (Replanning.tests model domain world).map fun test => ⟨world,table,test⟩

theorem every_row_is_source_generated (row : Row model domain original pool) : row ∈ rows model domain original pool := by
  rcases row with ⟨world,table,test⟩
  exact List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
    ⟨table,List.mem_attach _ _,List.mem_map.mpr ⟨test,Replanning.every_test_is_generated _ _ _ _,rfl⟩⟩⟩

@[inline] def readTable (world : Replanning.Point model domain) (program : Program model.source.code)
    (table : TableAt model domain original pool world) :=
  Finite.tableEvaluation model world.val original pool program table.val

def holds (reference protocol : Program model.source.code) (row : Row model domain original pool) : Prop :=
  let current := readTable model domain original pool row.world protocol row.table
  let original := readTable model domain original pool row.world reference row.table
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = original.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native original.native
  | .economic axis => current.value axis.val ≤ original.value axis.val

instance (reference protocol : Program model.source.code) (row : Row model domain original pool) : Decidable (holds model domain original pool reference protocol row) := by
  unfold holds
  cases row.test <;> infer_instance

def acceptable (reference protocol : Program model.source.code) : Prop :=
  ∀ row ∈ rows model domain original pool, holds model domain original pool reference protocol row

theorem acceptable_iff_every_generated_cursor (reference protocol : Program model.source.code) :
    acceptable model domain original pool reference protocol ↔ ∀ (world : Replanning.Point model domain) (table : TableAt model domain original pool world),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (readTable model domain original pool world protocol table) (readTable model domain original pool world reference table) := by
  constructor
  · intro all world table
    refine ⟨all ⟨world,table,.legal⟩ (every_row_is_source_generated _ _ _ _ _),
      all ⟨world,table,.complete⟩ (every_row_is_source_generated _ _ _ _ _),
      all ⟨world,table,.profile⟩ (every_row_is_source_generated _ _ _ _ _),
      all ⟨world,table,.native⟩ (every_row_is_source_generated _ _ _ _ _),?_⟩
    intro axis inside
    exact all ⟨world,table,.economic ⟨axis,inside⟩⟩ (every_row_is_source_generated _ _ _ _ _)
  · intro all row _
    rcases row with ⟨world,table,test⟩
    cases test with
    | legal => exact (all world table).1
    | complete => exact (all world table).2.1
    | profile => exact (all world table).2.2.1
    | native => exact (all world table).2.2.2.1
    | economic axis => exact (all world table).2.2.2.2 axis.val axis.property


/-- Generate each complete evaluation once per world/table pair before testing its fields. -/
def packed (reference protocol : Program model.source.code) : Prop :=
  ∀ world ∈ Replanning.points model domain,
    ∀ table ∈ Finite.tables world.val original pool,
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (Finite.tableEvaluation model world.val original pool protocol table)
        (Finite.tableEvaluation model world.val original pool reference table)

theorem acceptable_iff_packed (reference protocol : Program model.source.code) :
    acceptable model domain original pool reference protocol ↔ packed model domain original pool reference protocol := by
  rw [acceptable_iff_every_generated_cursor]
  constructor
  · intro all world _ table original
    exact all world ⟨table,original⟩
  · intro all world table
    exact all world (Replanning.every_point_is_source_generated model domain world) table.val table.property

instance decidableAcceptable (reference protocol : Program model.source.code) : Decidable (acceptable model domain original pool reference protocol) := by
  letI : Decidable (packed model domain original pool reference protocol) := by unfold packed; infer_instance
  exact decidable_of_iff (packed model domain original pool reference protocol) (acceptable_iff_packed model domain original pool reference protocol).symm

theorem acceptable_trans (first middle last : Program model.source.code)
    (left : acceptable model domain original pool middle first) (right : acceptable model domain original pool last middle) :
    acceptable model domain original pool last first := by
  apply (acceptable_iff_every_generated_cursor _ _ _ _ _ _).mpr
  intro world table
  exact Synthesis.accepts_trans _ _ _ _ _ ((acceptable_iff_every_generated_cursor _ _ _ _ _ _).mp left world table)
    ((acceptable_iff_every_generated_cursor _ _ _ _ _ _).mp right world table)

theorem acceptable_iff_every_common_external_opponent (reference protocol : Program model.source.code)
    (referenceGenerated : reference ∈ pool) (protocolGenerated : protocol ∈ pool) :
    acceptable model domain original pool reference protocol ↔ ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (Finite.actualEvaluation model world.val original protocol rival)
        (Finite.actualEvaluation model world.val original reference rival) := by
  rw [acceptable_iff_every_generated_cursor]
  apply forall_congr'
  intro world
  constructor
  · intro finite
    apply (Finite.one_common_table_preserves_two_complete_actual_occurrences model world.val original pool
      (Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)) protocol reference protocolGenerated referenceGenerated).mp
    intro table generated
    exact finite ⟨table,generated⟩
  · intro all table
    exact all (Finite.opponent world.val original pool table.val)

inductive Axis where
  | economic (world : Replanning.Point model domain) (table : TableAt model domain original pool world) (axis : Replanning.EconomicAt model domain world)
  | native (world : Replanning.Point model domain) (table : TableAt model domain original pool world) (anchor : Program model.source.code)

def axes : List (Axis model domain original pool) := (Replanning.points model domain).flatMap fun world =>
  (Finite.tables world.val original pool).attach.flatMap fun table =>
    (economicAxes world.val.source world.val.cut).attach.map (Axis.economic world table) ++
      (pool).map (Axis.native world table)

def benefit (protocol : Program model.source.code) : Axis model domain original pool → ℚ
  | .economic world table axis => (readTable model domain original pool world protocol table).value axis.val
  | .native world table anchor =>
      if (Authority.Trace.Lawful.inventory (readTable model domain original pool world protocol table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (readTable model domain original pool world anchor table).native).due then 0 else 1

theorem acceptance_bounds_every_benefit (reference protocol : Program model.source.code)
    (accepted : acceptable model domain original pool reference protocol) :
    Distributed.NoWorse (axes model domain original pool) (benefit model domain original pool) protocol reference := by
  intro axis _
  cases axis with
  | economic world table axis =>
    exact ((acceptable_iff_every_generated_cursor _ _ _ _ _ _).mp accepted world table).2.2.2.2 axis.val axis.property
  | native world table anchor =>
    have native := ((acceptable_iff_every_generated_cursor _ _ _ _ _ _).mp accepted world table).2.2.2.1
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
    by_cases old : (Authority.Trace.Lawful.inventory (readTable model domain original pool world reference table).native).due.Subperm
      (Authority.Trace.Lawful.inventory (readTable model domain original pool world anchor table).native).due
    · have new := native.2.trans old
      simp only [if_pos old,if_pos new,le_refl]
    · split <;> simp_all

structure Candidate (reference : Program model.source.code) where
  protocol : Program model.source.code
  generated : protocol ∈ pool
  accepted : acceptable model domain original pool reference protocol

def check (reference : Program model.source.code) (protocol : {program : Program model.source.code // program ∈ pool}) :
    Option (Candidate model domain original pool reference) :=
  if accepted : acceptable model domain original pool reference protocol.val then some ⟨protocol.val,protocol.property,accepted⟩ else none

def candidates (reference : Program model.source.code) :=
  pool.attach.filterMap (check model domain original pool reference)

theorem every_accepted_protocol_is_generated (reference protocol : Program model.source.code)
    (generated : protocol ∈ pool) (accepted : acceptable model domain original pool reference protocol) :
    ∃ candidate ∈ candidates model domain original pool reference, candidate.protocol = protocol := by
  refine ⟨⟨protocol,generated,accepted⟩,List.mem_filterMap.mpr ⟨⟨protocol,generated⟩,List.mem_attach _ _,?_⟩,rfl⟩
  simp only [check,dif_pos accepted]

abbrev Choice (reference : Program model.source.code) := Selected (axes model domain original pool)
  (fun candidate : Candidate model domain original pool reference => benefit model domain original pool candidate.protocol) (candidates model domain original pool reference)

structure Rejection (reference protocol : Program model.source.code) where
  row : Row model domain original pool
  generated : row ∈ rows model domain original pool
  broken : ¬ holds model domain original pool reference protocol row

inductive Outcome (reference : Program model.source.code) where
  | selected (choice : Choice model domain original pool reference)
  | blocked (rejected : ∀ protocol : Program model.source.code, protocol ∈ pool → Rejection model domain original pool reference protocol)

def compile (reference : Program model.source.code) : Outcome model domain original pool reference :=
  match result : choose (axes model domain original pool) (fun candidate : Candidate model domain original pool reference => benefit model domain original pool candidate.protocol)
    (candidates model domain original pool reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol generated => match inspect (holds model domain original pool reference protocol) (rows model domain original pool) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted accepted => False.elim (by
          have witness := every_accepted_protocol_is_generated model domain original pool reference protocol generated accepted
          rw [choose_none_iff_empty] at result
          obtain ⟨candidate,inside,_⟩ := witness
          simp only [result,List.not_mem_nil] at inside))

def verify (reference protocol : Program model.source.code) : Bool :=
  decide (acceptable model domain original pool reference protocol ∧ ∀ other ∈ pool,
    acceptable model domain original pool reference other →
      ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) protocol other)

theorem selected_has_no_full_responsibility_dominator (reference : Program model.source.code)
    (choice : Choice model domain original pool reference) (other : Program model.source.code) (generated : other ∈ pool)
    (accepted : acceptable model domain original pool choice.policy.protocol other) :
    ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) choice.policy.protocol other := by
  have through := acceptable_trans model domain original pool other choice.policy.protocol reference accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original pool reference other generated through
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_full_responsibility_improvement_is_realized (reference : Program model.source.code)
    (choice : Choice model domain original pool reference)
    (available : ∃ other ∈ pool, acceptable model domain original pool reference other ∧
      Distributed.Improves (axes model domain original pool) (benefit model domain original pool) reference other) :
    Distributed.Improves (axes model domain original pool) (benefit model domain original pool) reference choice.policy.protocol := by
  constructor
  · exact acceptance_bounds_every_benefit model domain original pool reference choice.policy.protocol choice.policy.accepted
  · intro backward
    obtain ⟨other,generated,accepted,better⟩ := available
    obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original pool reference other generated accepted
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) choice.policy.protocol candidate.protocol at maximal
    rw [same] at maximal
    apply maximal
    constructor
    · intro axis member
      exact (better.1 axis member).trans (backward axis member)
    · intro reverse
      apply better.2
      intro axis member
      exact (backward axis member).trans (reverse axis member)


theorem verify_iff (reference protocol : Program model.source.code) :
    verify model domain original pool reference protocol = true ↔ acceptable model domain original pool reference protocol ∧
      ∀ other ∈ pool, acceptable model domain original pool reference other →
        ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) protocol other := by
  simp only [verify,decide_eq_true_eq]

theorem independently_replayed_choice_is_accepted (reference : Program model.source.code)
    (choice : Choice model domain original pool reference) : verify model domain original pool reference choice.policy.protocol = true := by
  apply (verify_iff model domain original pool reference choice.policy.protocol).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro other generated accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original pool reference other generated accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model domain original pool) (benefit model domain original pool) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_verified_protocol_protects_its_own_actual_full_responsibility
    (reference protocol : Program model.source.code) (referenceGenerated : reference ∈ pool) (protocolGenerated : protocol ∈ pool)
    (checked : verify model domain original pool reference protocol = true)
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (Finite.actualEvaluation model world.val original protocol rival)
      (Finite.actualEvaluation model world.val original reference rival) :=
  (acceptable_iff_every_common_external_opponent model domain original pool reference protocol referenceGenerated protocolGenerated).mp
    ((verify_iff model domain original pool reference protocol).mp checked).1 world rival

theorem strict_improvement_has_an_actual_responsibility_coordinate (old new : Program model.source.code)
    (better : Distributed.Improves (axes model domain original pool) (benefit model domain original pool) old new) :
    ∃ axis ∈ axes model domain original pool, benefit model domain original pool new axis < benefit model domain original pool old axis :=
  ((Distributed.improves_iff (axes model domain original pool) (benefit model domain original pool) old new).mp better).2

/-- Recompute raw evaluations and counterexample rows; certificate proofs are not boolean inputs. -/
def review (reference : Program model.source.code) (outcome : Outcome model domain original pool reference) : Bool :=
  match outcome with
  | .selected choice => verify model domain original pool reference choice.policy.protocol
  | .blocked rejected => pool.attach.all fun protocol =>
      !decide (holds model domain original pool reference protocol.val (rejected protocol.val protocol.property).row)

theorem every_generated_outcome_is_independently_reviewable
    (reference : Program model.source.code) (outcome : Outcome model domain original pool reference) :
    review model domain original pool reference outcome = true := by
  cases outcome with
  | selected choice => exact independently_replayed_choice_is_accepted model domain original pool reference choice
  | blocked rejected =>
    apply List.all_eq_true.mpr
    intro protocol _
    have broken := (rejected protocol.val protocol.property).broken
    simp only [Bool.not_eq_true',decide_eq_false_iff_not]
    exact broken



end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection
