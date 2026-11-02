import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Search

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev actualEvaluation (cursor : Cursor model.source.code) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (rival : Opponent model.source.code) := Window.evaluate model cursor protocol rival
abbrev tableEvaluation (cursor : Cursor model.source.code) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (table : Cut.Table cursor.source cursor.entry cursor.cut) :=
  Window.evaluate model cursor protocol (Cut.opponent cursor.source cursor.entry cursor.cut table)

abbrev finite_relation_iff_same_external_adaptive_opponent := @Window.finite_relation_iff_the_same_full_adaptive_opponent

variable (domain : List (Cursor model.source.code))
abbrev Point := Replanning.Point model domain
abbrev points := Replanning.points model domain
abbrev TableAt := Replanning.TableAt model domain
abbrev EconomicAt := Replanning.EconomicAt model domain
abbrev Row := Replanning.Row model domain
abbrev rows := Replanning.rows model domain
abbrev every_point_is_source_generated := @Replanning.every_point_is_source_generated
abbrev every_row_is_source_generated := @Replanning.every_row_is_source_generated
@[inline] def readTable (world : Point model domain) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (table : TableAt model domain world) :=
  tableEvaluation model world.val protocol table.val

theorem value_is_the_unchanged_original_table_value (world : Point model domain)
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (table : TableAt model domain world) :
    (readTable model domain world protocol table).value = (Replanning.readTable model domain world protocol table).value := by
  rw [Replanning.readTable,Replanning.table_evaluation_is_its_own_actual_protocol]
  rfl

theorem native_is_the_unchanged_original_table_manifest (world : Point model domain)
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (table : TableAt model domain world) :
    (readTable model domain world protocol table).native = (Replanning.readTable model domain world protocol table).native := by
  rw [Replanning.readTable,Replanning.table_evaluation_is_its_own_actual_protocol]
  rfl

def holds (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (row : Row model domain) : Prop :=
  let current := readTable model domain row.world protocol row.table
  let original := readTable model domain row.world reference row.table
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = original.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native original.native
  | .economic axis => current.value axis.val ≤ original.value axis.val

instance (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (row : Row model domain) : Decidable (holds model domain reference protocol row) := by
  unfold holds
  cases row.test <;> infer_instance

def acceptable (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  ∀ row ∈ rows model domain, holds model domain reference protocol row

theorem acceptable_iff_every_generated_cursor (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
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
def packed (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  ∀ world ∈ points model domain,
    ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (tableEvaluation model world.val protocol table)
        (tableEvaluation model world.val reference table)

theorem acceptable_iff_packed (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    acceptable model domain reference protocol ↔ packed model domain reference protocol := by
  rw [acceptable_iff_every_generated_cursor]
  constructor
  · intro all world _ table original
    exact all world ⟨table,original⟩
  · intro all world table
    exact all world (every_point_is_source_generated model domain world) table.val table.property


theorem acceptable_trans (first middle last : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (left : acceptable model domain middle first) (right : acceptable model domain last middle) :
    acceptable model domain last first := by
  apply (acceptable_iff_every_generated_cursor _ _ _ _).mpr
  intro world table
  exact Synthesis.accepts_trans _ _ _ _ _ ((acceptable_iff_every_generated_cursor _ _ _ _).mp left world table)
    ((acceptable_iff_every_generated_cursor _ _ _ _).mp right world table)

theorem acceptable_iff_every_common_external_opponent (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
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

/-- Whole-source controller equality permits one actual representative, not a
smaller adversary assumption. All other sources retain their complete table. -/
def compactPacked (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  if PublicDomain.quiet (code := model.source.code) then
    ∀ world ∈ points model domain,
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
        (Window.evaluate model world.val protocol PublicDomain.silent)
        (Window.evaluate model world.val reference PublicDomain.silent)
  else packed model domain reference protocol

theorem compactPacked_iff (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    compactPacked model domain reference protocol ↔ acceptable model domain reference protocol := by
  unfold compactPacked
  split
  · rename_i quiet
    rw [acceptable_iff_every_common_external_opponent]
    constructor
    · intro all world rival
      dsimp only [actualEvaluation]
      rw [Window.a_source_proved_quiet_domain_has_one_actual_full_evaluation model world.val protocol rival quiet,
        Window.a_source_proved_quiet_domain_has_one_actual_full_evaluation model world.val reference rival quiet]
      exact all world (every_point_is_source_generated _ _ world)
    · intro all world _
      exact all world _
  · exact (acceptable_iff_packed model domain reference protocol).symm

instance decidableAcceptable (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    Decidable (acceptable model domain reference protocol) := by
  letI : Decidable (compactPacked model domain reference protocol) := by
    unfold compactPacked
    split
    · infer_instance
    · unfold packed
      infer_instance
  exact decidable_of_iff (compactPacked model domain reference protocol) (compactPacked_iff model domain reference protocol)

abbrev axes := Replanning.axes model domain
abbrev benefit := Replanning.benefit model domain

theorem acceptance_bounds_every_benefit (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (accepted : acceptable model domain reference protocol) :
    Distributed.NoWorse (axes model domain) (benefit model domain) protocol reference := by
  intro axis _
  cases axis with
  | economic world table axis =>
    have bound := ((acceptable_iff_every_generated_cursor _ _ _ _).mp accepted world table).2.2.2.2 axis.val axis.property
    simpa only [value_is_the_unchanged_original_table_value,benefit,Replanning.benefit] using bound
  | native world table anchor =>
    have native := ((acceptable_iff_every_generated_cursor _ _ _ _).mp accepted world table).2.2.2.1
    rw [native_is_the_unchanged_original_table_manifest,native_is_the_unchanged_original_table_manifest] at native
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
    by_cases old : (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world reference table).native).due.Subperm
      (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world anchor table).native).due
    · have new := native.2.trans old
      simp only [if_pos old,if_pos new,le_refl]
    · split <;> simp_all

structure Candidate (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) where
  protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code
  accepted : acceptable model domain reference protocol

def check (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Option (Candidate model domain reference) :=
  if accepted : acceptable model domain reference protocol then some ⟨protocol,accepted⟩ else none

def candidates (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :=
  (rules model.source.code).filterMap (check model domain reference)

theorem every_accepted_protocol_is_generated (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (accepted : acceptable model domain reference protocol) :
    ∃ candidate ∈ candidates model domain reference, candidate.protocol = protocol := by
  refine ⟨⟨protocol,accepted⟩,List.mem_filterMap.mpr ⟨protocol,every_rule_is_source_generated _ _,?_⟩,rfl⟩
  simp only [check,dif_pos accepted]

abbrev Choice (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) := Selected (axes model domain)
  (fun candidate : Candidate model domain reference => benefit model domain candidate.protocol) (candidates model domain reference)

structure Rejection (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) where
  row : Row model domain
  original : row ∈ rows model domain
  broken : ¬ holds model domain reference protocol row

inductive Outcome (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) where
  | selected (choice : Choice model domain reference)
  | blocked (rejected : ∀ protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code, Rejection model domain reference protocol)

def compile (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Outcome model domain reference :=
  match result : Distributed.choose (axes model domain) (fun candidate : Candidate model domain reference => benefit model domain candidate.protocol)
    (candidates model domain reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol => match Distributed.inspect (holds model domain reference protocol) (rows model domain) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted accepted => False.elim (by
          have witness := every_accepted_protocol_is_generated model domain reference protocol accepted
          rw [choose_none_iff_empty] at result
          obtain ⟨candidate,inside,_⟩ := witness
          simp only [result,List.not_mem_nil] at inside))

def verify (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Bool :=
  decide (acceptable model domain reference protocol ∧ ∀ other ∈ rules model.source.code,
    acceptable model domain reference other →
      ¬ Distributed.Improves (axes model domain) (benefit model domain) protocol other)

theorem selected_has_no_full_responsibility_dominator (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (choice : Choice model domain reference) (other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (accepted : acceptable model domain choice.policy.protocol other) :
    ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol other := by
  have original := acceptable_trans model domain other choice.policy.protocol reference accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_protocol_is_generated model domain reference other original
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (axes model domain) (benefit model domain) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_full_responsibility_improvement_is_realized (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (choice : Choice model domain reference)
    (available : ∃ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code, acceptable model domain reference other ∧
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


theorem verify_iff (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    verify model domain reference protocol = true ↔ acceptable model domain reference protocol ∧
      ∀ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code, acceptable model domain reference other →
        ¬ Distributed.Improves (axes model domain) (benefit model domain) protocol other := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (every_rule_is_source_generated _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem independently_replayed_choice_is_accepted (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
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
    (reference protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (checked : verify model domain reference protocol = true)
    (world : Point model domain) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (actualEvaluation model world.val protocol rival)
      (actualEvaluation model world.val reference rival) :=
  (acceptable_iff_every_common_external_opponent model domain reference protocol).mp
    ((verify_iff model domain reference protocol).mp checked).1 world rival

theorem strict_improvement_has_an_actual_responsibility_coordinate (old new : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (better : Distributed.Improves (axes model domain) (benefit model domain) old new) :
    ∃ axis ∈ axes model domain, benefit model domain new axis < benefit model domain old axis :=
  ((Distributed.improves_iff (axes model domain) (benefit model domain) old new).mp better).2

/-- Recompute raw evaluations and counterexample rows; certificate proofs are not boolean inputs. -/
def review (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (outcome : Outcome model domain reference) : Bool :=
  match outcome with
  | .selected choice => verify model domain reference choice.policy.protocol
  | .blocked rejected => (rules model.source.code).all fun protocol =>
      !decide (holds model domain reference protocol (rejected protocol).row)

theorem every_generated_outcome_is_independently_reviewable
    (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (outcome : Outcome model domain reference) :
    review model domain reference outcome = true := by
  cases outcome with
  | selected choice => exact independently_replayed_choice_is_accepted model domain reference choice
  | blocked rejected =>
    apply List.all_eq_true.mpr
    intro protocol _
    have broken := (rejected protocol).broken
    simp only [Bool.not_eq_true',decide_eq_false_iff_not]
    exact broken



end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Search
