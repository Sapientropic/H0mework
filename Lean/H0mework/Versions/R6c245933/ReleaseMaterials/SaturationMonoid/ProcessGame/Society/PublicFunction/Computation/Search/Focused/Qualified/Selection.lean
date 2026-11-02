import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Work

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Segmented.Publication Segmented.Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (announcements : List (Rule model.source.code))
  (point : View (code := model.source.code)) (send : Rule model.source.code)

abbrev Choice := Prefix.Choice model domain original (past model original worker quote quotas) reference
abbrev eligible (candidate : Candidate model domain original reference worker quote quotas) :=
  Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate

def undominated (candidate other : Candidate model domain original reference worker quote quotas) : Prop :=
  ¬ Review.improves model domain original candidate.protocol other.protocol
instance (candidate other : Candidate model domain original reference worker quote quotas) :
    Decidable (undominated model domain original reference worker quote quotas candidate other) := by
  unfold undominated
  infer_instance

variable (room : (past model original worker quote quotas).length ≤ horizon domain)
  (global : Sparse.Work model domain original (past model original worker quote quotas) reference)
  (globalComplete : global.todo = [])
  (qualified : Work model domain original reference worker receiver quote quotas announcements)

private theorem inspect_accepts {Row : Type} (holds : Row → Prop) [DecidablePred holds]
    (rows : List Row) (checked : ∀ row ∈ rows,holds row) :
    Distributed.inspect holds rows = .accepted checked := by
  cases generated : Distributed.inspect holds rows with
  | accepted passed => rfl
  | rejected row inside broken => exact False.elim (broken (checked row inside))

private theorem improves_map_iff {A B Axis : Type} (axes : List Axis)
    (cost : B → Axis → ℚ) (project : A → B) (old next : A) :
    Distributed.Improves axes (fun proposal axis => cost (project proposal) axis) old next ↔
      Distributed.Improves axes cost (project old) (project next) := Iff.rfl

private theorem improves_right_congr {Policy Axis : Type} (axes : List Axis)
    (cost : Policy → Axis → ℚ) (old first second : Policy)
    (same : cost first = cost second) :
    Distributed.Improves axes cost old first ↔ Distributed.Improves axes cost old second := by
  simp only [Distributed.Improves,Distributed.NoWorse,same]

include room globalComplete in
private theorem cached_comparison_protects_every_original_candidate
    (candidate : Candidate model domain original reference worker quote quotas)
    (checked : ∀ other ∈ Sparse.pool model domain original (past model original worker quote quotas) reference global,
      undominated model domain original reference worker quote quotas candidate other) :
    ∀ other ∈ Prefix.candidates model domain original (past model original worker quote quotas) reference,
      ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
        (fun proposal : Candidate model domain original reference worker quote quotas => Selection.benefit model domain original proposal.protocol)
        candidate other := by
  intro other _ better
  let representative := Sparse.representative model domain original (past model original worker quote quotas) reference room other
  have compared : ¬ Review.improves model domain original candidate.protocol representative.protocol :=
    checked representative (Sparse.every_original_accepted_candidate_has_a_paid_sparse_representative model domain original
      (past model original worker quote quotas) reference room global globalComplete other)
  have programBetter := (improves_map_iff (Selection.axes (fuel := horizon domain) model domain)
    (Selection.benefit model domain original) (fun proposal : Candidate model domain original reference worker quote quotas => proposal.protocol)
    candidate other).mp better
  have preserved := Sparse.representative_preserves_every_original_benefit model domain original
    (past model original worker quote quotas) reference room other
  have representativeBetter := (improves_right_congr (Selection.axes (fuel := horizon domain) model domain)
    (Selection.benefit model domain original) candidate.protocol representative.protocol other.protocol preserved).mpr programBetter
  exact compared ((Review.improves_iff model domain original candidate.protocol representative.protocol).mpr representativeBetter)

private theorem every_original_global_choice_passes_the_cached_comparison
    (choice : Choice model domain original reference worker quote quotas) :
    ∀ other ∈ Sparse.pool model domain original (past model original worker quote quotas) reference global,
      undominated model domain original reference worker quote quotas choice.policy other := by
  intro other inside better
  have programBetter := (Review.improves_iff model domain original choice.policy.protocol other.protocol).mp better
  have improved := (improves_map_iff (Selection.axes (fuel := horizon domain) model domain)
    (Selection.benefit model domain original) (fun proposal : Candidate model domain original reference worker quote quotas => proposal.protocol)
    choice.policy other).mpr programBetter
  exact choice.maximal other (Sparse.every_cached_candidate_belongs_to_the_original_full_pool model domain original
    (past model original worker quote quotas) reference global other inside) improved

/-- Qualification restricts the output, never the domination comparison. -/
def admit (candidate : {proposal // proposal ∈ pool model domain original reference worker receiver quote quotas announcements qualified}) :
    Option {choice : Choice model domain original reference worker quote quotas //
      eligible model domain original reference worker receiver quote quotas announcements point send choice.policy = true} :=
  if suitable : eligible model domain original reference worker receiver quote quotas announcements point send candidate.val = true then
    match Distributed.inspect (undominated model domain original reference worker quote quotas candidate.val)
        (Sparse.pool model domain original (past model original worker quote quotas) reference global) with
    | .rejected .. => none
    | .accepted checked => some ⟨⟨candidate.val,
        every_cached_candidate_belongs_to_the_original_full_pool model domain original reference worker quote quotas candidate.val,
        cached_comparison_protects_every_original_candidate model domain original reference worker quote quotas room global globalComplete candidate.val checked⟩,suitable⟩
  else none

def choices := (pool model domain original reference worker receiver quote quotas announcements qualified).attach.filterMap
  (admit model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified)

/-- Stop after the first globally checked qualified output; no later output is needed. -/
def choose := (pool model domain original reference worker receiver quote quotas announcements qualified).attach.findSome?
  (admit model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified)

theorem first_match_is_exactly_the_original_complete_output_head :
    choose model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified =
      (choices model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified).head? :=
  List.head?_filterMap.symm

theorem every_original_eligible_global_choice_has_a_cached_selected_representative
    (complete : qualified.todo = []) (member : point.point ∈ domain)
    (choice : Choice model domain original reference worker quote quotas)
    (suitable : eligible model domain original reference worker receiver quote quotas announcements point send choice.policy = true) :
    (⟨Guarded.globalChoice model domain original reference worker receiver quote quotas point send announcements choice suitable,
      Guarded.normalization_keeps_original_eligibility model domain original reference worker receiver quote quotas point send announcements member choice.policy suitable⟩ :
      {choice : Choice model domain original reference worker quote quotas //
        eligible model domain original reference worker receiver quote quotas announcements point send choice.policy = true}) ∈
      choices model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified := by
  let next := Guarded.globalChoice model domain original reference worker receiver quote quotas point send announcements choice suitable
  have cached : next.policy ∈ pool model domain original reference worker receiver quote quotas announcements qualified :=
    every_original_eligible_candidate_has_a_cached_qualified_representative model domain original reference worker receiver quote quotas announcements
      qualified complete point send choice.policy suitable
  have valid : eligible model domain original reference worker receiver quote quotas announcements point send next.policy = true :=
    Guarded.normalization_keeps_original_eligibility model domain original reference worker receiver quote quotas point send announcements member choice.policy suitable
  apply List.mem_filterMap.mpr
  refine ⟨⟨next.policy,cached⟩,List.mem_attach _ _,?_⟩
  have checked := every_original_global_choice_passes_the_cached_comparison model domain original reference worker quote quotas global next
  have inspected := inspect_accepts (undominated model domain original reference worker quote quotas next.policy)
    (Sparse.pool model domain original (past model original worker quote quotas) reference global) checked
  unfold admit
  rw [dif_pos valid,inspected]

theorem absence_rejects_every_original_eligible_global_choice
    (complete : qualified.todo = []) (member : point.point ∈ domain)
    (absent : choose model domain original reference worker receiver quote quotas announcements point send room global globalComplete qualified = none)
    (choice : Choice model domain original reference worker quote quotas) :
    eligible model domain original reference worker receiver quote quotas announcements point send choice.policy ≠ true := by
  intro suitable
  have cached := every_original_eligible_global_choice_has_a_cached_selected_representative model domain original reference worker receiver quote quotas announcements
    point send room global globalComplete qualified complete member choice suitable
  have same := first_match_is_exactly_the_original_complete_output_head model domain original reference worker receiver quote quotas announcements
    point send room global globalComplete qualified
  have empty := List.head?_eq_none_iff.mp (same.symm.trans absent)
  rw [empty] at cached
  cases cached

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
