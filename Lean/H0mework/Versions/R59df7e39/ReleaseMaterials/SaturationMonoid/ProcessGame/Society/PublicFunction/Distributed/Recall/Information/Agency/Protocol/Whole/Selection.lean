import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Selection

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)

@[inline] def readTable (world : Replanning.Point model domain) (program : Program model.source.code fuel)
    (table : Replanning.TableAt model domain world) :=
  tableEvaluation model world.val original program table.val

def holds (reference protocol : Program model.source.code fuel) (row : Replanning.Row model domain) : Prop :=
  let current := readTable model domain original row.world protocol row.table
  let original := readTable model domain original row.world reference row.table
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = original.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native original.native
  | .economic axis => current.value axis.val ≤ original.value axis.val

instance (reference protocol : Program model.source.code fuel) (row : Replanning.Row model domain) : Decidable (holds model domain original reference protocol row) := by
  unfold holds
  cases row.test <;> infer_instance

def acceptable (reference protocol : Program model.source.code fuel) : Prop :=
  ∀ row ∈ Replanning.rows model domain, holds model domain original reference protocol row

theorem acceptable_iff_every_generated_cursor (reference protocol : Program model.source.code fuel) :
    acceptable model domain original reference protocol ↔ ∀ (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (readTable model domain original world protocol table) (readTable model domain original world reference table) := by
  constructor
  · intro all world table
    refine ⟨all ⟨world,table,.legal⟩ (Replanning.every_row_is_source_generated _ _ _),
      all ⟨world,table,.complete⟩ (Replanning.every_row_is_source_generated _ _ _),
      all ⟨world,table,.profile⟩ (Replanning.every_row_is_source_generated _ _ _),
      all ⟨world,table,.native⟩ (Replanning.every_row_is_source_generated _ _ _),?_⟩
    intro axis inside
    exact all ⟨world,table,.economic ⟨axis,inside⟩⟩ (Replanning.every_row_is_source_generated _ _ _)
  · intro all row _
    rcases row with ⟨world,table,test⟩
    cases test with
    | legal => exact (all world table).1
    | complete => exact (all world table).2.1
    | profile => exact (all world table).2.2.1
    | native => exact (all world table).2.2.2.1
    | economic axis => exact (all world table).2.2.2.2 axis.val axis.property


/-- Generate each complete evaluation once per world/table pair before testing its fields. -/
def packed (reference protocol : Program model.source.code fuel) : Prop :=
  ∀ world ∈ Replanning.points model domain,
    ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (tableEvaluation model world.val original protocol table)
        (tableEvaluation model world.val original reference table)

theorem acceptable_iff_packed (reference protocol : Program model.source.code fuel) :
    acceptable model domain original reference protocol ↔ packed model domain original reference protocol := by
  rw [acceptable_iff_every_generated_cursor]
  constructor
  · intro all world _ table original
    exact all world ⟨table,original⟩
  · intro all world table
    exact all world (Replanning.every_point_is_source_generated model domain world) table.val table.property

instance decidableAcceptable (reference protocol : Program model.source.code fuel) : Decidable (acceptable model domain original reference protocol) := by
  letI : Decidable (packed model domain original reference protocol) := by unfold packed; infer_instance
  exact decidable_of_iff (packed model domain original reference protocol) (acceptable_iff_packed model domain original reference protocol).symm

theorem acceptable_trans (first middle last : Program model.source.code fuel)
    (left : acceptable model domain original middle first) (right : acceptable model domain original last middle) :
    acceptable model domain original last first := by
  apply (acceptable_iff_every_generated_cursor _ _ _ _ _).mpr
  intro world table
  exact Synthesis.accepts_trans _ _ _ _ _ ((acceptable_iff_every_generated_cursor _ _ _ _ _).mp left world table)
    ((acceptable_iff_every_generated_cursor _ _ _ _ _).mp right world table)

theorem acceptable_iff_every_common_external_opponent (reference protocol : Program model.source.code fuel) :
    acceptable model domain original reference protocol ↔ ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code),
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (actualEvaluation model world.val original protocol rival)
        (actualEvaluation model world.val original reference rival) := by
  rw [acceptable_iff_every_generated_cursor]
  apply forall_congr'
  intro world
  constructor
  · intro finite
    apply (finite_relation_iff_the_same_full_adaptive_opponent model world.val original
      (Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)) protocol reference).mp
    intro table generated
    exact finite ⟨table,generated⟩
  · intro all table
    have finite := (finite_relation_iff_the_same_full_adaptive_opponent model world.val original
      (Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)) protocol reference).mpr all
    exact finite table.val table.property

inductive Axis where
  | economic (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world) (axis : Replanning.EconomicAt model domain world)
  | native (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world) (anchor : Program model.source.code fuel)

def axes : List (Axis (fuel := fuel) model domain) := (Replanning.points model domain).flatMap fun world =>
  (Cut.tables world.val.source world.val.entry world.val.cut).attach.flatMap fun table =>
    (economicAxes world.val.source world.val.cut).attach.map (Axis.economic world table) ++
      (programs model.source.code fuel).map (Axis.native world table)

def benefit (protocol : Program model.source.code fuel) : Axis (fuel := fuel) model domain → ℚ
  | .economic world table axis => (readTable model domain original world protocol table).value axis.val
  | .native world table anchor =>
      if (Authority.Trace.Lawful.inventory (readTable model domain original world protocol table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (readTable model domain original world anchor table).native).due then 0 else 1

theorem acceptance_bounds_every_benefit (reference protocol : Program model.source.code fuel)
    (accepted : acceptable model domain original reference protocol) :
    Distributed.NoWorse (axes (fuel := fuel) model domain) (benefit model domain original) protocol reference := by
  intro axis _
  cases axis with
  | economic world table axis =>
    exact ((acceptable_iff_every_generated_cursor _ _ _ _ _).mp accepted world table).2.2.2.2 axis.val axis.property
  | native world table anchor =>
    have native := ((acceptable_iff_every_generated_cursor _ _ _ _ _).mp accepted world table).2.2.2.1
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
    by_cases old : (Authority.Trace.Lawful.inventory (readTable model domain original world reference table).native).due.Subperm
      (Authority.Trace.Lawful.inventory (readTable model domain original world anchor table).native).due
    · have new := native.2.trans old
      simp only [if_pos old,if_pos new,le_refl]
    · split <;> simp_all

structure Candidate (reference : Program model.source.code fuel) where
  protocol : Program model.source.code fuel
  accepted : acceptable model domain original reference protocol

def check (reference protocol : Program model.source.code fuel) : Option (Candidate model domain original reference) :=
  if accepted : acceptable model domain original reference protocol then some ⟨protocol,accepted⟩ else none

def candidates (reference : Program model.source.code fuel) :=
  (programs model.source.code fuel).filterMap (check model domain original reference)

theorem every_accepted_protocol_is_generated (reference protocol : Program model.source.code fuel)
    (accepted : acceptable model domain original reference protocol) :
    ∃ candidate ∈ candidates model domain original reference, candidate.protocol = protocol := by
  refine ⟨⟨protocol,accepted⟩,List.mem_filterMap.mpr ⟨protocol,every_bounded_program_is_source_generated _ _ _,?_⟩,rfl⟩
  simp only [check,dif_pos accepted]

abbrev Choice (reference : Program model.source.code fuel) := Selected (axes (fuel := fuel) model domain)
  (fun candidate : Candidate model domain original reference => benefit model domain original candidate.protocol) (candidates model domain original reference)

structure Rejection (reference protocol : Program model.source.code fuel) where
  row : Replanning.Row model domain
  generated : row ∈ Replanning.rows model domain
  broken : ¬ holds model domain original reference protocol row

inductive Outcome (reference : Program model.source.code fuel) where
  | selected (choice : Choice model domain original reference)
  | blocked (rejected : ∀ protocol : Program model.source.code fuel, Rejection model domain original reference protocol)

def compile (reference : Program model.source.code fuel) : Outcome model domain original reference :=
  match result : choose (axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference => benefit model domain original candidate.protocol)
    (candidates model domain original reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol => match inspect (holds model domain original reference protocol) (Replanning.rows model domain) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted accepted => False.elim (by
          have witness := every_accepted_protocol_is_generated model domain original reference protocol accepted
          rw [choose_none_iff_empty] at result
          obtain ⟨candidate,inside,_⟩ := witness
          simp only [result,List.not_mem_nil] at inside))

def verify (reference protocol : Program model.source.code fuel) : Bool :=
  decide (acceptable model domain original reference protocol ∧ ∀ other ∈ programs model.source.code fuel,
    acceptable model domain original reference other →
      ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) protocol other)

theorem selected_has_no_full_responsibility_dominator (reference : Program model.source.code fuel)
    (choice : Choice model domain original reference) (other : Program model.source.code fuel)
    (accepted : acceptable model domain original choice.policy.protocol other) :
    ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) choice.policy.protocol other := by
  have through := acceptable_trans model domain original other choice.policy.protocol reference accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original reference other through
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_full_responsibility_improvement_is_realized (reference : Program model.source.code fuel)
    (choice : Choice model domain original reference)
    (available : ∃ other : Program model.source.code fuel, acceptable model domain original reference other ∧
      Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) reference other) :
    Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) reference choice.policy.protocol := by
  constructor
  · exact acceptance_bounds_every_benefit model domain original reference choice.policy.protocol choice.policy.accepted
  · intro backward
    obtain ⟨other,accepted,better⟩ := available
    obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original reference other accepted
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) choice.policy.protocol candidate.protocol at maximal
    rw [same] at maximal
    apply maximal
    constructor
    · intro axis member
      exact (better.1 axis member).trans (backward axis member)
    · intro reverse
      apply better.2
      intro axis member
      exact (backward axis member).trans (reverse axis member)


theorem verify_iff (reference protocol : Program model.source.code fuel) :
    verify model domain original reference protocol = true ↔ acceptable model domain original reference protocol ∧
      ∀ other : Program model.source.code fuel, acceptable model domain original reference other →
        ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) protocol other := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (every_bounded_program_is_source_generated _ _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem independently_replayed_choice_is_accepted (reference : Program model.source.code fuel)
    (choice : Choice model domain original reference) : verify model domain original reference choice.policy.protocol = true := by
  apply (verify_iff model domain original reference choice.policy.protocol).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro other accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain original reference other accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_verified_protocol_protects_its_own_actual_full_responsibility
    (reference protocol : Program model.source.code fuel) (checked : verify model domain original reference protocol = true)
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (actualEvaluation model world.val original protocol rival)
      (actualEvaluation model world.val original reference rival) :=
  (acceptable_iff_every_common_external_opponent model domain original reference protocol).mp
    ((verify_iff model domain original reference protocol).mp checked).1 world rival

theorem strict_improvement_has_an_actual_responsibility_coordinate (old new : Program model.source.code fuel)
    (better : Distributed.Improves (axes (fuel := fuel) model domain) (benefit model domain original) old new) :
    ∃ axis ∈ axes (fuel := fuel) model domain, benefit model domain original new axis < benefit model domain original old axis :=
  ((Distributed.improves_iff (axes (fuel := fuel) model domain) (benefit model domain original) old new).mp better).2

/-- Recompute raw evaluations and counterexample rows; certificate proofs are not boolean inputs. -/
def review (reference : Program model.source.code fuel) (outcome : Outcome model domain original reference) : Bool :=
  match outcome with
  | .selected choice => verify model domain original reference choice.policy.protocol
  | .blocked rejected => (programs model.source.code fuel).all fun protocol =>
      !decide (holds model domain original reference protocol (rejected protocol).row)

theorem every_generated_outcome_is_independently_reviewable
    (reference : Program model.source.code fuel) (outcome : Outcome model domain original reference) :
    review model domain original reference outcome = true := by
  cases outcome with
  | selected choice => exact independently_replayed_choice_is_accepted model domain original reference choice
  | blocked rejected =>
    apply List.all_eq_true.mpr
    intro protocol _
    have broken := (rejected protocol).broken
    simp only [Bool.not_eq_true',decide_eq_false_iff_not]
    exact broken



end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Selection
