import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Cut
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.AtomicDeficiency
import Mathlib.Order.WithBot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable (agenda : Agenda Party Good TaskId)
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (script : List (Option (Compile.RawInput Party Good Port Technology Instrument)))

private theorem due_value_is_an_original_cut (id : TaskId) (present : id ∈ agenda.atomic ++ agenda.fragments) :
    (agenda.task id).deadline ∈ cuts agenda :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨id, present, rfl⟩)

private theorem same_mature_tasks_give_the_same_service_condition {earlier later : ℚ}
    (same : ∀ id ∈ agenda.atomic ++ agenda.fragments, (agenda.task id).deadline ≤ earlier ↔ (agenda.task id).deadline ≤ later) :
    ServedThrough agenda source script earlier ↔ ServedThrough agenda source script later := by
  have whole : (atomicAt agenda earlier).toFinset = (atomicAt agenda later).toFinset := by
    ext id
    simp only [List.mem_toFinset, atomicAt, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨present, before⟩ => ⟨present, (same id (List.mem_append_left _ present)).mp before⟩,
      fun ⟨present, after⟩ => ⟨present, (same id (List.mem_append_left _ present)).mpr after⟩⟩
  have fractional : keepAt agenda earlier = keepAt agenda later := by
    funext line
    apply decide_eq_decide.mpr
    exact same line.1.1.val (List.mem_append_right _ (List.mem_toFinset.mp line.1.1.property))
  unfold ServedThrough ChoiceAt
  rw [whole, fractional]

private theorem no_mature_tasks_are_served (time : ℚ) (none : ∀ cut ∈ cuts agenda, ¬ cut ≤ time) :
    ServedThrough agenda source script time := by
  have empty : (atomicAt agenda time).toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro id original
    obtain ⟨present, mature⟩ := List.mem_filter.mp (List.mem_toFinset.mp original)
    exact none _ (due_value_is_an_original_cut agenda id (List.mem_append_left _ present)) (of_decide_eq_true mature)
  let geom := Clock.Window.Shared.geometry source (∅ : Finset TaskId) agenda.task script
  have assignment : WholeChoice source script ∅ agenda.task := by
    refine ⟨∅, ?_, ?_⟩
    · classical
      change ∅ ∈ geom.matchings
      unfold CanonicalBipartiteFeasibility.matchings
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), geom.empty_isMatching⟩
    · simp [Clock.Window.Shared.geometry]
  let chosen : ChoiceAt agenda source script time := by
    change WholeChoice source script (atomicAt agenda time).toFinset agenda.task
    rw [empty]
    exact assignment
  refine ⟨chosen, fun _ _ => 0, (base agenda source script chosen.reserved).zero_is_admissible, fun line mature => ?_⟩
  exact (none _ (due_value_is_an_original_cut agenda line.1.1.val
    (List.mem_append_right _ (List.mem_toFinset.mp line.1.1.property))) (of_decide_eq_true mature)).elim

private theorem a_blocked_prefix_has_an_original_maturity (time : ℚ)
    (blocked : ¬ ServedThrough agenda source script time) :
    ∃ cut ∈ cuts agenda, cut ≤ time ∧ ¬ ServedThrough agenda source script cut := by
  let due := (cuts agenda).filter fun cut => cut ≤ time
  by_cases any : due.Nonempty
  · let last := due.max' any
    have present := Finset.mem_filter.mp (Finset.max'_mem due any)
    refine ⟨last, present.1, present.2, fun served => blocked ?_⟩
    apply (same_mature_tasks_give_the_same_service_condition agenda source script ?_).mp served
    intro id original
    exact ⟨fun earlier => earlier.trans present.2, fun mature =>
      Finset.le_max' due _ (Finset.mem_filter.mpr ⟨due_value_is_an_original_cut agenda id original, mature⟩)⟩
  · exact (blocked (no_mature_tasks_are_served agenda source script time
      fun cut original mature => any ⟨cut, Finset.mem_filter.mpr ⟨original, mature⟩⟩)).elim

inductive FailureAt (time : ℚ)
  | atomic (issue : Clock.Window.Shared.Deficiency source (atomicAt agenda time).toFinset agenda.task script)
  | fragments (whole : ChoiceAt agenda source script time)
      (forEveryAssignment : ∀ choice, NamedCut (networkAt agenda source script time choice))

def nameFailure (time : ℚ) (inspected : ResidualSearch (networkAt agenda source script time))
    (unavailable : inspected.hasAllocation = false) : FailureAt agenda source script time :=
  match inspected with
  | .noWhole absent => .atomic (atomicDeficiency source script _ agenda.task (atomicAt agenda time) rfl
      fun ⟨matching, original, full⟩ => absent ⟨matching, original, full⟩)
  | .short choice cuts => .fragments choice cuts
  | .available .. => (Bool.noConfusion unavailable : False).elim

theorem FailureAt.refutes {time : ℚ} (issue : FailureAt agenda source script time) :
    ¬ ServedThrough agenda source script time := by
  rintro ⟨choice, paid⟩
  cases issue with
  | atomic short => exact short.refutes choice.has_its_own_atomic_settlement
  | fragments _ cuts =>
    have complete := ((base agenda source script choice.reserved).restriction_is_exact_for_the_original_due_rows
      (keepAt agenda time)).mpr paid
    exact (((cuts choice).receipt.gap_pos_iff_no_complete).mp (cuts choice).positive) complete

structure FirstFailure where
  time : ℚ
  original : time ∈ cuts agenda
  cause : FailureAt agenda source script time
  earlier : ∀ horizon < time, ServedThrough agenda source script horizon

theorem FirstFailure.safe_iff (first : FirstFailure agenda source script) (horizon : ℚ) :
    ServedThrough agenda source script horizon ↔ horizon < first.time := by
  refine ⟨fun paid => lt_of_not_ge (fun late => ?_), first.earlier horizon⟩
  exact first.cause.refutes agenda source script (served_through_is_downward agenda source script late paid)

inductive Frontier
  | clear (every : ∀ horizon, ServedThrough agenda source script horizon)
  | blocked (first : FirstFailure agenda source script)

/-- Every failure is named at the earliest original maturity. No terminal
ledger or future submission is needed for this earlier-cut calculation. -/
def inspectFrontier : Frontier agenda source script := by
  let tested := inspectAt agenda source script
  let failed := (cuts agenda).filter fun time => (tested time).hasAllocation = false
  have included (time : ℚ) (mature : time ∈ cuts agenda) (unavailable : ¬ ServedThrough agenda source script time) :
      time ∈ failed := by
    apply Finset.mem_filter.mpr
    refine ⟨mature, ?_⟩
    cases recorded : (tested time).hasAllocation
    · rfl
    · exact (unavailable ((inspectAt_pays_exactly_the_original_due_prefix agenda source script time).mp recorded)).elim
  if any : failed.Nonempty then
    let first := failed.min' any
    have found := Finset.mem_filter.mp (Finset.min'_mem failed any)
    refine .blocked ⟨first, found.1, nameFailure agenda source script first (tested first) found.2, fun horizon prior => ?_⟩
    by_contra stopped
    obtain ⟨cut, original, within, blocked⟩ := a_blocked_prefix_has_an_original_maturity agenda source script horizon stopped
    exact (not_le_of_gt prior) ((Finset.min'_le failed cut (included cut original blocked)).trans within)
  else
    refine .clear fun horizon => ?_
    by_contra stopped
    obtain ⟨cut, original, _, blocked⟩ := a_blocked_prefix_has_an_original_maturity agenda source script horizon stopped
    exact any ⟨cut, included cut original blocked⟩

def serviceBoundary : Frontier agenda source script → WithTop ℚ
  | .clear _ => ⊤
  | .blocked first => first.time

theorem serviceBoundary_exact (frontier : Frontier agenda source script) (time : ℚ) :
    ServedThrough agenda source script time ↔ (time : WithTop ℚ) < serviceBoundary agenda source script frontier := by
  cases frontier with
  | clear every => simp [serviceBoundary, every time]
  | blocked first => simpa only [serviceBoundary, WithTop.coe_lt_coe] using first.safe_iff agenda source script time

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
