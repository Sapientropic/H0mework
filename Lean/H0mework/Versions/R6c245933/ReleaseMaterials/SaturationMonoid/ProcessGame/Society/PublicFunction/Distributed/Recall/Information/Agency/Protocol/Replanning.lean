import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Synthesis

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Replanning

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

abbrev native (cursor : Cursor model.source.code) : Native.Authority.Bound
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  {model with source := cursor.source}

variable (cursor : Cursor model.source.code) (protocol : Rule model.source.code)

abbrev actualEvaluation (rival : Opponent model.source.code) :=
  evaluate (native model cursor) cursor.entry cursor.cut rfl
    (Cursor.controller cursor protocol rival) (term cursor.source cursor.entry cursor.cut protocol)

abbrev tableController (table : Cut.Table cursor.source cursor.entry cursor.cut) :=
  Future.jointOpponent cursor.source cursor.entry cursor.cut
    (Cursor.controller cursor protocol (Cut.opponent cursor.source cursor.entry cursor.cut table))

abbrev tableEvaluation (table : Cut.Table cursor.source cursor.entry cursor.cut) :=
  evaluate (native model cursor) cursor.entry cursor.cut rfl
    (tableController model cursor protocol table) (term cursor.source cursor.entry cursor.cut protocol)

theorem table_evaluation_is_its_own_actual_protocol
    (table : Cut.Table cursor.source cursor.entry cursor.cut) :
    tableEvaluation model cursor protocol table =
      actualEvaluation model cursor protocol (Cut.opponent cursor.source cursor.entry cursor.cut table) :=
  evaluate_joint (native model cursor) cursor.entry cursor.cut rfl rfl _ _

theorem one_external_restriction_controls_every_inherited_clock
    (rival : Opponent model.source.code) :
    tableController model cursor protocol (externalTable cursor rival) =
      Future.jointOpponent cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival) := by
  funext history past frame
  change (if member : (history,past,frame) ∈ Residual.keys model.source.code
      (Residual.seed cursor.source cursor.entry cursor.cut) (Residual.schedules cursor.source cursor.entry cursor.cut)
    then Cursor.controller cursor protocol (Cut.opponent cursor.source cursor.entry cursor.cut (externalTable cursor rival))
      history past frame else none) = _
  by_cases member : (history,past,frame) ∈ Residual.keys model.source.code
      (Residual.seed cursor.source cursor.entry cursor.cut) (Residual.schedules cursor.source cursor.entry cursor.cut)
  · simp only [dif_pos member,Future.jointOpponent,Residual.respond,Residual.restrict]
    change driver model.source.code cursor.ownerStart protocol (Cut.opponent cursor.source cursor.entry cursor.cut _)
        history past frame = driver model.source.code cursor.ownerStart protocol rival history past frame
    simp only [driver]
    cases ownerAt model.source.code cursor.ownerStart history.length with
    | some site => rfl
    | none => simp only [Cut.opponent,Residual.respond,dif_pos member,externalTable,Residual.restrict]
  · simp only [Future.jointOpponent,Residual.respond,dif_neg member]

theorem one_external_table_preserves_every_actual_full_responsibility
    (rival : Opponent model.source.code) :
    tableEvaluation model cursor protocol (externalTable cursor rival) = actualEvaluation model cursor protocol rival := by
  unfold tableEvaluation
  rw [one_external_restriction_controls_every_inherited_clock]
  exact evaluate_joint (native model cursor) cursor.entry cursor.cut rfl rfl _ _

theorem finite_relation_iff_same_external_adaptive_opponent
    (relation : Evaluation model.source.code → Evaluation model.source.code → Prop)
    (new old : Rule model.source.code) :
    (∀ table ∈ Cut.tables cursor.source cursor.entry cursor.cut,
      relation (tableEvaluation model cursor new table) (tableEvaluation model cursor old table)) ↔
      ∀ rival : Opponent model.source.code,
        relation (actualEvaluation model cursor new rival) (actualEvaluation model cursor old rival) := by
  constructor
  · intro finite rival
    have checked := finite (externalTable cursor rival) (Residual.restriction_is_generated _ _ _ rival)
    rw [one_external_table_preserves_every_actual_full_responsibility model cursor new rival,
      one_external_table_preserves_every_actual_full_responsibility model cursor old rival] at checked
    exact checked
  · intro all table _
    rw [table_evaluation_is_its_own_actual_protocol model cursor new table,
      table_evaluation_is_its_own_actual_protocol model cursor old table]
    exact all _

variable (domain : List (Cursor model.source.code))

abbrev Point := {cursor : Cursor model.source.code // cursor ∈ domain}
abbrev points : List (Point model domain) := domain.attach

theorem every_point_is_source_generated (point : Point model domain) : point ∈ points model domain :=
  List.mem_attach _ _

abbrev TableAt (world : Point model domain) :=
  {table : Cut.Table world.val.source world.val.entry world.val.cut //
    table ∈ Cut.tables world.val.source world.val.entry world.val.cut}

abbrev EconomicAt (world : Point model domain) :=
  {axis : EconomicAxis model.source.code // axis ∈ economicAxes world.val.source world.val.cut}

@[inline] def readTable (world : Point model domain) (protocol : Rule model.source.code) (table : TableAt model domain world) :=
  tableEvaluation model world.val protocol table.val

inductive Test (world : Point model domain) where
  | legal | complete | profile | native
  | economic (axis : EconomicAt model domain world)

def tests (world : Point model domain) : List (Test model domain world) :=
  [.legal,.complete,.profile,.native] ++ (economicAxes world.val.source world.val.cut).attach.map Test.economic

theorem every_test_is_generated (world : Point model domain) (test : Test model domain world) : test ∈ tests model domain world := by
  cases test with
  | legal => simp [tests]
  | complete => simp [tests]
  | profile => simp [tests]
  | native => simp [tests]
  | economic axis => exact List.mem_append_right _ (List.mem_map.mpr ⟨axis,List.mem_attach _ _,rfl⟩)

structure Row where
  world : Point model domain
  table : TableAt model domain world
  test : Test model domain world

def rows : List (Row model domain) := (points model domain).flatMap fun world =>
  (Cut.tables world.val.source world.val.entry world.val.cut).attach.flatMap fun table =>
    (tests model domain world).map fun test => ⟨world,table,test⟩

theorem every_row_is_source_generated (row : Row model domain) : row ∈ rows model domain := by
  rcases row with ⟨world,table,test⟩
  exact List.mem_flatMap.mpr ⟨world,every_point_is_source_generated _ _ _,List.mem_flatMap.mpr
    ⟨table,List.mem_attach _ _,List.mem_map.mpr ⟨test,every_test_is_generated _ _ _ _,rfl⟩⟩⟩

def holds (reference protocol : Rule model.source.code) (row : Row model domain) : Prop :=
  let current := readTable model domain row.world protocol row.table
  let original := readTable model domain row.world reference row.table
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = original.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native original.native
  | .economic axis => current.value axis.val ≤ original.value axis.val

instance (reference protocol : Rule model.source.code) (row : Row model domain) : Decidable (holds model domain reference protocol row) := by
  unfold holds
  cases row.test <;> infer_instance

def acceptable (reference protocol : Rule model.source.code) : Prop :=
  ∀ row ∈ rows model domain, holds model domain reference protocol row

theorem acceptable_iff_every_generated_cursor (reference protocol : Rule model.source.code) :
    acceptable model domain reference protocol ↔ ∀ (world : Point model domain) (table : TableAt model domain world),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (readTable model domain world protocol table) (readTable model domain world reference table) := by
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
  ∀ world ∈ points model domain,
    ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (tableEvaluation model world.val protocol table)
        (tableEvaluation model world.val reference table)

theorem acceptable_iff_packed (reference protocol : Rule model.source.code) :
    acceptable model domain reference protocol ↔ packed model domain reference protocol := by
  rw [acceptable_iff_every_generated_cursor]
  constructor
  · intro all world _ table original
    exact all world ⟨table,original⟩
  · intro all world table
    exact all world (every_point_is_source_generated model domain world) table.val table.property

instance decidableAcceptable (reference protocol : Rule model.source.code) : Decidable (acceptable model domain reference protocol) := by
  letI : Decidable (packed model domain reference protocol) := by unfold packed; infer_instance
  exact decidable_of_iff (packed model domain reference protocol) (acceptable_iff_packed model domain reference protocol).symm

theorem acceptable_trans (first middle last : Rule model.source.code)
    (left : acceptable model domain middle first) (right : acceptable model domain last middle) :
    acceptable model domain last first := by
  apply (acceptable_iff_every_generated_cursor _ _ _ _).mpr
  intro world table
  exact Synthesis.accepts_trans _ _ _ _ _ ((acceptable_iff_every_generated_cursor _ _ _ _).mp left world table)
    ((acceptable_iff_every_generated_cursor _ _ _ _).mp right world table)

theorem acceptable_iff_every_common_external_opponent (reference protocol : Rule model.source.code) :
    acceptable model domain reference protocol ↔ ∀ (world : Point model domain) (rival : Opponent model.source.code),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (actualEvaluation model world.val protocol rival)
        (actualEvaluation model world.val reference rival) := by
  rw [acceptable_iff_every_generated_cursor]
  apply forall_congr'
  intro world
  constructor
  · intro finite
    apply (finite_relation_iff_same_external_adaptive_opponent model world.val
      (Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)) protocol reference).mp
    intro table generated
    exact finite ⟨table,generated⟩
  · intro all table
    have finite := (finite_relation_iff_same_external_adaptive_opponent model world.val
      (Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)) protocol reference).mpr all
    exact finite table.val table.property

inductive Axis where
  | economic (world : Point model domain) (table : TableAt model domain world) (axis : EconomicAt model domain world)
  | native (world : Point model domain) (table : TableAt model domain world) (anchor : Rule model.source.code)

def axes : List (Axis model domain) := (points model domain).flatMap fun world =>
  (Cut.tables world.val.source world.val.entry world.val.cut).attach.flatMap fun table =>
    (economicAxes world.val.source world.val.cut).attach.map (Axis.economic world table) ++
      (rules model.source.code).map (Axis.native world table)

def benefit (protocol : Rule model.source.code) : Axis model domain → ℚ
  | .economic world table axis => (readTable model domain world protocol table).value axis.val
  | .native world table anchor =>
      if (Authority.Trace.Lawful.inventory (readTable model domain world protocol table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (readTable model domain world anchor table).native).due then 0 else 1

theorem acceptance_bounds_every_benefit (reference protocol : Rule model.source.code)
    (accepted : acceptable model domain reference protocol) :
    Distributed.NoWorse (axes model domain) (benefit model domain) protocol reference := by
  intro axis _
  cases axis with
  | economic world table axis =>
    exact ((acceptable_iff_every_generated_cursor _ _ _ _).mp accepted world table).2.2.2.2 axis.val axis.property
  | native world table anchor =>
    have native := ((acceptable_iff_every_generated_cursor _ _ _ _).mp accepted world table).2.2.2.1
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
    by_cases old : (Authority.Trace.Lawful.inventory (readTable model domain world reference table).native).due.Subperm
      (Authority.Trace.Lawful.inventory (readTable model domain world anchor table).native).due
    · have new := native.2.trans old
      simp only [if_pos old,if_pos new,le_refl]
    · split <;> simp_all

structure Candidate (reference : Rule model.source.code) where
  protocol : Rule model.source.code
  accepted : acceptable model domain reference protocol

def check (reference protocol : Rule model.source.code) : Option (Candidate model domain reference) :=
  if accepted : acceptable model domain reference protocol then some ⟨protocol,accepted⟩ else none

def candidates (reference : Rule model.source.code) :=
  (rules model.source.code).filterMap (check model domain reference)

theorem every_accepted_protocol_is_generated (reference protocol : Rule model.source.code)
    (accepted : acceptable model domain reference protocol) :
    ∃ candidate ∈ candidates model domain reference, candidate.protocol = protocol := by
  refine ⟨⟨protocol,accepted⟩,List.mem_filterMap.mpr ⟨protocol,every_rule_is_source_generated _ _,?_⟩,rfl⟩
  simp only [check,dif_pos accepted]

abbrev Choice (reference : Rule model.source.code) := Selected (axes model domain)
  (fun candidate : Candidate model domain reference => benefit model domain candidate.protocol) (candidates model domain reference)

structure Rejection (reference protocol : Rule model.source.code) where
  row : Row model domain
  original : row ∈ rows model domain
  broken : ¬ holds model domain reference protocol row

inductive Outcome (reference : Rule model.source.code) where
  | selected (choice : Choice model domain reference)
  | blocked (rejected : ∀ protocol : Rule model.source.code, Rejection model domain reference protocol)

def compile (reference : Rule model.source.code) : Outcome model domain reference :=
  match result : choose (axes model domain) (fun candidate : Candidate model domain reference => benefit model domain candidate.protocol)
    (candidates model domain reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol => match inspect (holds model domain reference protocol) (rows model domain) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted accepted => False.elim (by
          have witness := every_accepted_protocol_is_generated model domain reference protocol accepted
          rw [choose_none_iff_empty] at result
          obtain ⟨candidate,inside,_⟩ := witness
          simp only [result,List.not_mem_nil] at inside))

def verify (reference protocol : Rule model.source.code) : Bool :=
  decide (acceptable model domain reference protocol ∧ ∀ other ∈ rules model.source.code,
    acceptable model domain reference other →
      ¬ Distributed.Improves (axes model domain) (benefit model domain) protocol other)

theorem selected_has_no_full_responsibility_dominator (reference : Rule model.source.code)
    (choice : Choice model domain reference) (other : Rule model.source.code)
    (accepted : acceptable model domain choice.policy.protocol other) :
    ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol other := by
  have original := acceptable_trans model domain other choice.policy.protocol reference accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain reference other original
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_full_responsibility_improvement_is_realized (reference : Rule model.source.code)
    (choice : Choice model domain reference)
    (available : ∃ other : Rule model.source.code, acceptable model domain reference other ∧
      Distributed.Improves (axes model domain) (benefit model domain) reference other) :
    Distributed.Improves (axes model domain) (benefit model domain) reference choice.policy.protocol := by
  constructor
  · exact acceptance_bounds_every_benefit model domain reference choice.policy.protocol choice.policy.accepted
  · intro backward
    obtain ⟨other,accepted,better⟩ := available
    obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain reference other accepted
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol candidate.protocol at maximal
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
    verify model domain reference protocol = true ↔ acceptable model domain reference protocol ∧
      ∀ other : Rule model.source.code, acceptable model domain reference other →
        ¬ Distributed.Improves (axes model domain) (benefit model domain) protocol other := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (every_rule_is_source_generated _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem independently_replayed_choice_is_accepted (reference : Rule model.source.code)
    (choice : Choice model domain reference) : verify model domain reference choice.policy.protocol = true := by
  apply (verify_iff model domain reference choice.policy.protocol).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro other accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain reference other accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_verified_protocol_protects_its_own_actual_full_responsibility
    (reference protocol : Rule model.source.code) (checked : verify model domain reference protocol = true)
    (world : Point model domain) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (actualEvaluation model world.val protocol rival)
      (actualEvaluation model world.val reference rival) :=
  (acceptable_iff_every_common_external_opponent model domain reference protocol).mp
    ((verify_iff model domain reference protocol).mp checked).1 world rival

theorem strict_improvement_has_an_actual_responsibility_coordinate (old new : Rule model.source.code)
    (better : Distributed.Improves (axes model domain) (benefit model domain) old new) :
    ∃ axis ∈ axes model domain, benefit model domain new axis < benefit model domain old axis :=
  ((Distributed.improves_iff (axes model domain) (benefit model domain) old new).mp better).2

/-- Recompute raw evaluations and counterexample rows; certificate proofs are not boolean inputs. -/
def review (reference : Rule model.source.code) (outcome : Outcome model domain reference) : Bool :=
  match outcome with
  | .selected choice => verify model domain reference choice.policy.protocol
  | .blocked rejected => (rules model.source.code).all fun protocol =>
      !decide (holds model domain reference protocol (rejected protocol).row)

theorem every_generated_outcome_is_independently_reviewable
    (reference : Rule model.source.code) (outcome : Outcome model domain reference) :
    review model domain reference outcome = true := by
  cases outcome with
  | selected choice => exact independently_replayed_choice_is_accepted model domain reference choice
  | blocked rejected =>
    apply List.all_eq_true.mpr
    intro protocol _
    have broken := (rejected protocol).broken
    simp only [Bool.not_eq_true',decide_eq_false_iff_not]
    exact broken



end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Replanning
