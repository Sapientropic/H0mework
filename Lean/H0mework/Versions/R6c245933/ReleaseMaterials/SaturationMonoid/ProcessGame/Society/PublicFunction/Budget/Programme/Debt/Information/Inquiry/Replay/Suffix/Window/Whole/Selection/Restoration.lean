import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tensor
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Window.Whole.Restoration
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

structure Row where
  world : Replanning.Point model domain
  table : Replanning.TableAt model domain world

def rows : List (Row model domain) := (Replanning.points model domain).flatMap fun world =>
  (Cut.tables world.val.source world.val.entry world.val.cut).attach.map fun table => ⟨world,table⟩

theorem every_row_is_generated (row : Row model domain) : row ∈ rows model domain := by
  apply List.mem_flatMap.mpr
  refine ⟨row.world,Replanning.every_point_is_source_generated _ _ _,List.mem_map.mpr ?_⟩
  exact ⟨row.table,List.mem_attach _ _,by cases row;rfl⟩

def holds (reference protocol : Program model.source.code fuel) (row : Row model domain) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Prop :=
  accepts (requested := requested) model row.world.val
    (tableTensor (tariff := tariff) model row.world.val original protocol row.table.val)
    (tableTensor (tariff := tariff) model row.world.val original reference row.table.val)

instance {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) (row : Row model domain) :
    Decidable (holds (tariff := tariff) (requested := requested) model domain original reference protocol row) := by unfold holds;infer_instance

def acceptable (reference protocol : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Prop :=
  ∀ row ∈ rows model domain,holds (tariff := tariff) (requested := requested) model domain original reference protocol row


theorem retains_original_acceptance {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) : Selection.acceptable model domain original reference protocol := by
  apply (Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mpr
  intro world table
  exact (accepted ⟨world,table⟩ (every_row_is_generated _ _ _)).1

theorem acceptable_iff_every_same_full_opponent {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) :
    acceptable (tariff := tariff) (requested := requested) model domain original reference protocol ↔ ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code),
      accepts (requested := requested) model world.val (actualTensor (tariff := tariff) model world.val original protocol rival) (actualTensor (tariff := tariff) model world.val original reference rival) := by
  constructor
  · intro all world
    apply (the_same_opponent_compares_present_and_every_registered_future (tariff := tariff) (requested := requested) model world.val original protocol reference).mp
    intro table inside
    exact all ⟨world,⟨table,inside⟩⟩ (every_row_is_generated _ _ _)
  · intro all row _
    exact (the_same_opponent_compares_present_and_every_registered_future (tariff := tariff) (requested := requested) model row.world.val original protocol reference).mpr
      (all row.world) row.table.val row.table.property


theorem original_self_admission_is_exact {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (program : Program model.source.code fuel) :
    Selection.acceptable model domain original program program ↔ acceptable (tariff := tariff) (requested := requested) model domain original program program := by
  constructor
  · intro before row _
    refine ⟨(Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mp before row.world row.table,?_,fun _ _ yes => yes⟩
    intro word inside
    obtain ⟨actual,generated⟩ := Window.Whole.Restoration.every_required_report_is_generated (tariff := tariff) model row.world.val
      (Continuation.Whole.controller row.world.val original program
        (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val))
      (Continuation.Whole.schedule row.world.val original program) requested word inside
    change Window.Whole.Restoration.futureNoWorse model row.world.val
      (Window.Whole.Restoration.report (tariff := tariff) model row.world.val _ _ word) (Window.Whole.Restoration.report (tariff := tariff) model row.world.val _ _ word)
    rw [generated]
    exact Native.Future.Recovery.Assessment.noWorse_refl _ _ _
  · exact retains_original_acceptance (tariff := tariff) (requested := requested) _ _ _ _ _

/-- All external tables in a quiet source are restrictions of this same actual tensor. -/
def compactPacked (reference protocol : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Prop :=
  if PublicDomain.quiet (code := model.source.code) then
    ∀ world ∈ Replanning.points model domain,
      accepts (requested := requested) model world.val (actualTensor (tariff := tariff) model world.val original protocol PublicDomain.silent)
        (actualTensor (tariff := tariff) model world.val original reference PublicDomain.silent)
  else acceptable (tariff := tariff) (requested := requested) model domain original reference protocol

theorem compactPacked_iff {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) :
    compactPacked (tariff := tariff) (requested := requested) model domain original reference protocol ↔ acceptable (tariff := tariff) (requested := requested) model domain original reference protocol := by
  unfold compactPacked
  split
  · rename_i quiet
    rw [acceptable_iff_every_same_full_opponent (tariff := tariff) (requested := requested)]
    constructor
    · intro all world rival
      rw [quiet_tensor (tariff := tariff) model world.val original protocol quiet rival,
        quiet_tensor (tariff := tariff) model world.val original reference quiet rival]
      exact all world (Replanning.every_point_is_source_generated _ _ _)
    · intro all world _
      exact all world _
  · rfl

instance {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) :
    Decidable (acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) := by
  letI : Decidable (compactPacked (tariff := tariff) (requested := requested) model domain original reference protocol) := by
    unfold compactPacked
    split
    · infer_instance
    · unfold acceptable;infer_instance
  exact decidable_of_iff (compactPacked (tariff := tariff) (requested := requested) model domain original reference protocol)
    (compactPacked_iff (tariff := tariff) (requested := requested) model domain original reference protocol)

theorem acceptable_trans {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (first middle last : Program model.source.code fuel)
    (left : acceptable (tariff := tariff) (requested := requested) model domain original middle first) (right : acceptable (tariff := tariff) (requested := requested) model domain original last middle) :
    acceptable (tariff := tariff) (requested := requested) model domain original last first := fun row inside =>
  accepts_trans _ _ (left row inside) (right row inside)

theorem accepted_self {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) : acceptable (tariff := tariff) (requested := requested) model domain original protocol protocol :=
  fun row inside => accepted_is_self_acceptable _ _ (accepted row inside)

/-- Source anchors encode the full transitive responsibility order without adding a welfare weight. -/
def benefit (protocol anchor : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : ℚ :=
  if acceptable (tariff := tariff) (requested := requested) model domain original anchor protocol then 0 else 1

def axes := programs model.source.code fuel

theorem acceptance_bounds_benefit {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) :
    Distributed.NoWorse (axes (fuel := fuel) model) (benefit (tariff := tariff) (requested := requested) model domain original) protocol reference := by
  intro anchor _
  change (if acceptable (tariff := tariff) (requested := requested) model domain original anchor protocol then (0 : ℚ) else 1) ≤
    (if acceptable (tariff := tariff) (requested := requested) model domain original anchor reference then 0 else 1)
  by_cases prior : acceptable (tariff := tariff) (requested := requested) model domain original anchor reference
  · have next := acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ accepted prior
    simp only [if_pos prior,if_pos next,le_refl]
  · split <;> simp_all

theorem benefit_order_is_exact {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (self : acceptable (tariff := tariff) (requested := requested) model domain original reference reference) :
    Distributed.NoWorse (axes (fuel := fuel) model) (benefit (tariff := tariff) (requested := requested) model domain original) protocol reference ↔
      acceptable (tariff := tariff) (requested := requested) model domain original reference protocol := by
  refine ⟨?_,acceptance_bounds_benefit (tariff := tariff) (requested := requested) _ _ _ _ _⟩
  intro bounded
  have atReference := bounded reference (every_bounded_program_is_source_generated _ _ _)
  change (if acceptable (tariff := tariff) (requested := requested) model domain original reference protocol then (0 : ℚ) else 1) ≤
    (if acceptable (tariff := tariff) (requested := requested) model domain original reference reference then 0 else 1) at atReference
  by_contra absent
  norm_num only [if_neg absent,if_pos self] at atReference

structure Candidate (reference : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  originalCandidate : Selection.Candidate model domain original reference
  accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference originalCandidate.protocol

abbrev Candidate.protocol {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} {reference : Program model.source.code fuel} (candidate : Candidate (tariff := tariff) (requested := requested) model domain original reference) :=
  candidate.originalCandidate.protocol

def refineCandidate (reference : Program model.source.code fuel) (candidate : Selection.Candidate model domain original reference) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) :
    Option (Candidate (tariff := tariff) (requested := requested) model domain original reference) :=
  if accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference candidate.protocol then some ⟨candidate,accepted⟩ else none

def candidates (reference : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) :=
  (Selection.candidates model domain original reference).filterMap (refineCandidate (tariff := tariff) (requested := requested) model domain original reference)

theorem every_acceptable_program_is_generated {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (accepted : acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) :
    ∃ candidate ∈ candidates (tariff := tariff) (requested := requested) model domain original reference,candidate.protocol = protocol := by
  obtain ⟨old,inside,same⟩ := Selection.every_accepted_protocol_is_generated model domain original reference protocol
    (retains_original_acceptance (tariff := tariff) (requested := requested) _ _ _ _ _ accepted)
  have accepted' : acceptable (tariff := tariff) (requested := requested) model domain original reference old.protocol := same.symm ▸ accepted
  refine ⟨⟨old,accepted'⟩,List.mem_filterMap.mpr ⟨old,inside,?_⟩,same⟩
  simp only [refineCandidate,dif_pos accepted']

abbrev Choice (reference : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) := Distributed.Selected (axes (fuel := fuel) model)
  (fun candidate : Candidate (tariff := tariff) (requested := requested) model domain original reference => benefit (tariff := tariff) (requested := requested) model domain original candidate.protocol)
  (candidates (tariff := tariff) (requested := requested) model domain original reference)

structure Rejection (reference protocol : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  row : Row model domain
  generated : row ∈ rows model domain
  broken : ¬ holds (tariff := tariff) (requested := requested) model domain original reference protocol row

def Rejection.cause {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)}
    {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)}
    {reference protocol : Program model.source.code fuel}
    (rejected : Rejection (tariff := tariff) (requested := requested) model domain original reference protocol) :=
  Window.Whole.Restoration.explain model rejected.row.world.val
    (tableTensor (tariff := tariff) model rejected.row.world.val original protocol rejected.row.table.val)
    (tableTensor (tariff := tariff) model rejected.row.world.val original reference rejected.row.table.val)
    requested rejected.broken

/-- A quiet obstruction is generated at the source's silent restriction, without enumerating equivalent tables. -/
def rejectionFrom {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel)
    (denied : ¬ acceptable (tariff := tariff) (requested := requested) model domain original reference protocol) : Rejection (tariff := tariff) (requested := requested) model domain original reference protocol :=
  if quiet : PublicDomain.quiet (code := model.source.code) = true then
    match Distributed.inspect (fun world : Replanning.Point model domain =>
        accepts (requested := requested) model world.val (actualTensor (tariff := tariff) model world.val original protocol PublicDomain.silent)
          (actualTensor (tariff := tariff) model world.val original reference PublicDomain.silent)) (Replanning.points model domain) with
    | .rejected world _ broken =>
        let row : Row model domain := ⟨world,⟨externalTable world.val PublicDomain.silent,
          Residual.restriction_is_generated _ _ _ PublicDomain.silent⟩⟩
        ⟨row,every_row_is_generated _ _ _,by
          intro valid
          change accepts (requested := requested) model world.val (tableTensor (tariff := tariff) model world.val original protocol (externalTable world.val PublicDomain.silent))
            (tableTensor (tariff := tariff) model world.val original reference (externalTable world.val PublicDomain.silent)) at valid
          rw [one_common_external_table_generates_the_same_complete_restoration_tensor (tariff := tariff),
            one_common_external_table_generates_the_same_complete_restoration_tensor (tariff := tariff)] at valid
          exact broken valid⟩
    | .accepted all => False.elim (denied ((compactPacked_iff (tariff := tariff) (requested := requested) _ _ _ _ _).mp (by
        simp only [compactPacked,if_pos quiet];exact all)))
  else match Distributed.inspect (holds (tariff := tariff) (requested := requested) model domain original reference protocol) (rows model domain) with
    | .rejected row generated broken => ⟨row,generated,broken⟩
    | .accepted all => False.elim (denied all)

inductive Outcome (reference : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  | selected (choice : Choice (tariff := tariff) (requested := requested) model domain original reference)
  | blocked (rejected : ∀ protocol : Program model.source.code fuel,Rejection (tariff := tariff) (requested := requested) model domain original reference protocol)

def compile (reference : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Outcome (tariff := tariff) (requested := requested) model domain original reference :=
  match result : Distributed.choose (axes (fuel := fuel) model)
      (fun candidate : Candidate (tariff := tariff) (requested := requested) model domain original reference => benefit (tariff := tariff) (requested := requested) model domain original candidate.protocol)
      (candidates (tariff := tariff) (requested := requested) model domain original reference) with
  | some choice => .selected choice
  | none => .blocked fun protocol => rejectionFrom (tariff := tariff) (requested := requested) model domain original reference protocol (by
      intro accepted
      obtain ⟨candidate,inside,_⟩ := every_acceptable_program_is_generated (tariff := tariff) (requested := requested) _ _ _ _ _ accepted
      rw [Distributed.choose_none_iff_empty] at result
      simp only [result,List.not_mem_nil] at inside)

def strict (reference protocol : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Prop :=
  acceptable (tariff := tariff) (requested := requested) model domain original reference protocol ∧ ¬ acceptable (tariff := tariff) (requested := requested) model domain original protocol reference

instance {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) : Decidable (strict (tariff := tariff) (requested := requested) model domain original reference protocol) := by
  unfold strict;infer_instance

theorem selected_has_no_full_present_and_future_dominator {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference : Program model.source.code fuel)
    (choice : Choice (tariff := tariff) (requested := requested) model domain original reference) (other : Program model.source.code fuel) :
    ¬ strict (tariff := tariff) (requested := requested) model domain original choice.policy.protocol other := by
  intro better
  have through := acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ better.1 choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_acceptable_program_is_generated (tariff := tariff) (requested := requested) _ _ _ _ _ through
  apply choice.maximal candidate inside
  change Distributed.Improves (axes (fuel := fuel) model) (benefit (tariff := tariff) (requested := requested) model domain original) choice.policy.protocol candidate.protocol
  rw [same]
  refine ⟨acceptance_bounds_benefit (tariff := tariff) (requested := requested) _ _ _ _ _ better.1,?_⟩
  intro backward
  exact better.2 ((benefit_order_is_exact (tariff := tariff) (requested := requested) _ _ _ _ _ (accepted_self (tariff := tariff) (requested := requested) _ _ _ _ _ through)).mp backward)

theorem every_available_strict_improvement_is_selected {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference : Program model.source.code fuel)
    (choice : Choice (tariff := tariff) (requested := requested) model domain original reference)
    (available : ∃ other : Program model.source.code fuel,strict (tariff := tariff) (requested := requested) model domain original reference other) :
    strict (tariff := tariff) (requested := requested) model domain original reference choice.policy.protocol := by
  refine ⟨choice.policy.accepted,?_⟩
  intro backward
  obtain ⟨other,forward,notBackward⟩ := available
  apply selected_has_no_full_present_and_future_dominator (tariff := tariff) (requested := requested) _ _ _ _ choice other
  refine ⟨acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ forward backward,?_⟩
  intro reverse
  exact notBackward (acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ backward reverse)

def verify (reference protocol : Program model.source.code fuel) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Bool :=
  decide (acceptable (tariff := tariff) (requested := requested) model domain original reference protocol ∧
    ∀ other ∈ programs model.source.code fuel,¬ strict (tariff := tariff) (requested := requested) model domain original protocol other)

theorem verify_iff {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference protocol : Program model.source.code fuel) :
    verify (tariff := tariff) (requested := requested) model domain original reference protocol = true ↔
    acceptable (tariff := tariff) (requested := requested) model domain original reference protocol ∧ ∀ other : Program model.source.code fuel,¬ strict (tariff := tariff) (requested := requested) model domain original protocol other := by
  simp only [verify,decide_eq_true_eq]
  exact ⟨fun checked => ⟨checked.1,fun other => checked.2 other (every_bounded_program_is_source_generated _ _ _)⟩,
    fun checked => ⟨checked.1,fun other _ => checked.2 other⟩⟩

theorem selected_independently_verifies {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (reference : Program model.source.code fuel)
    (choice : Choice (tariff := tariff) (requested := requested) model domain original reference) : verify (tariff := tariff) (requested := requested) model domain original reference choice.policy.protocol = true :=
  (verify_iff (tariff := tariff) (requested := requested) _ _ _ _ _).mpr ⟨choice.policy.accepted,selected_has_no_full_present_and_future_dominator (tariff := tariff) (requested := requested) _ _ _ _ choice⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration
