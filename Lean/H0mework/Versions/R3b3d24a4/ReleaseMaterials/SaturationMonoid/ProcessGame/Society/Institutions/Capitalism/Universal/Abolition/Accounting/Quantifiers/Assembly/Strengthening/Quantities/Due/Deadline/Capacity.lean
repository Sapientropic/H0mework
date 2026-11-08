import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Restrict

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline

open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {Row Item : Type*} [Fintype Row] [Fintype Item]

def dueBy (deadline : Row → ℚ) (time : ℚ) (row : Row) : Bool :=
  decide (deadline row ≤ time)

abbrev ServedThrough (network : Network Row Item) (deadline : Row → ℚ) (time : ℚ) :=
  network.PaysWhere (dueBy deadline time)

theorem served_through_is_downward (network : Network Row Item) (deadline : Row → ℚ)
    {earlier later : ℚ} (order : earlier ≤ later) :
    ServedThrough network deadline later → ServedThrough network deadline earlier :=
  network.original_rows_can_be_restricted_to_any_earlier_due_prefix fun _ due =>
    decide_eq_true ((of_decide_eq_true due).trans order)

def originalCuts (deadline : Row → ℚ) : Finset ℚ :=
  Finset.univ.image deadline

private theorem a_failure_has_an_original_due_cut (network : Network Row Item) (deadline : Row → ℚ)
    (time : ℚ) (blocked : ¬ ServedThrough network deadline time) :
    ∃ cut ∈ originalCuts deadline, cut ≤ time ∧ ¬ ServedThrough network deadline cut := by
  let due := (originalCuts deadline).filter fun cut => cut ≤ time
  by_cases anyDue : due.Nonempty
  · let last := due.max' anyDue
    have original := Finset.mem_filter.mp (Finset.max'_mem due anyDue)
    refine ⟨last, original.1, original.2, fun cleared => blocked ?_⟩
    apply network.original_rows_can_be_restricted_to_any_earlier_due_prefix (later := dueBy deadline last) _ cleared
    intro row paid
    apply decide_eq_true
    exact Finset.le_max' due _ (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩, of_decide_eq_true paid⟩)
  · exfalso
    apply blocked
    refine ⟨fun _ _ => 0, network.zero_is_admissible, fun row present => ?_⟩
    exact (anyDue ⟨deadline row, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩, of_decide_eq_true present⟩⟩).elim

variable [DecidableEq Row] [DecidableEq Item]

def atCut (network : Network Row Item) (deadline : Row → ℚ)
    (rows : List Row) (items : List Item) (allRows : ∀ row, row ∈ rows) (allItems : ∀ item, item ∈ items)
    (time : ℚ) : (network.restrict (dueBy deadline time)).Certificate :=
  (network.restrict (dueBy deadline time)).solveListed rows items allRows allItems

structure FirstShortage (network : Network Row Item) (deadline : Row → ℚ) where
  time : ℚ
  original : time ∈ originalCuts deadline
  certificate : (network.restrict (dueBy deadline time)).Certificate
  positive : 0 < (network.restrict (dueBy deadline time)).gap certificate.group
  before : ∀ earlier < time, ServedThrough network deadline earlier

omit [DecidableEq Item] in
theorem FirstShortage.safe_iff {network : Network Row Item} {deadline : Row → ℚ}
    (failure : FirstShortage network deadline) (time : ℚ) :
    ServedThrough network deadline time ↔ time < failure.time := by
  refine ⟨fun paid => lt_of_not_ge (fun past => ?_), failure.before time⟩
  exact ((network.restricted_certificate_reports_exact_original_failure _ failure.certificate).mp failure.positive)
    (served_through_is_downward network deadline past paid)

inductive Frontier (network : Network Row Item) (deadline : Row → ℚ)
  | clear (all : ∀ time, ServedThrough network deadline time)
  | short (first : FirstShortage network deadline)

/-- Compare only original maturity cuts. At each cut a single allocation
covers the entire due prefix, and a missed prefix can never be backdated. -/
def inspect (network : Network Row Item) (deadline : Row → ℚ)
    (rows : List Row) (items : List Item) (allRows : ∀ row, row ∈ rows) (allItems : ∀ item, item ∈ items) :
    Frontier network deadline := by
  let solved := atCut network deadline rows items allRows allItems
  let failed := (originalCuts deadline).filter fun time =>
    0 < (network.restrict (dueBy deadline time)).gap (solved time).group
  have exact (time : ℚ) :=
    network.restricted_certificate_reports_exact_original_failure (dueBy deadline time) (solved time)
  have included (time : ℚ) (sourceCut : time ∈ originalCuts deadline)
      (unavailable : ¬ ServedThrough network deadline time) : time ∈ failed :=
    Finset.mem_filter.mpr ⟨sourceCut, (exact time).mpr unavailable⟩
  if nonempty : failed.Nonempty then
    let first := failed.min' nonempty
    have original := Finset.mem_filter.mp (Finset.min'_mem failed nonempty)
    refine .short ⟨first, original.1, solved first, original.2, fun earlier before => ?_⟩
    by_contra blocked
    obtain ⟨cut, sourceCut, timely, unavailable⟩ := a_failure_has_an_original_due_cut network deadline earlier blocked
    exact (not_le_of_gt before) ((Finset.min'_le failed cut (included cut sourceCut unavailable)).trans timely)
  else
    refine .clear fun time => ?_
    by_contra blocked
    obtain ⟨cut, sourceCut, _, unavailable⟩ := a_failure_has_an_original_due_cut network deadline time blocked
    exact nonempty ⟨cut, included cut sourceCut unavailable⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline
