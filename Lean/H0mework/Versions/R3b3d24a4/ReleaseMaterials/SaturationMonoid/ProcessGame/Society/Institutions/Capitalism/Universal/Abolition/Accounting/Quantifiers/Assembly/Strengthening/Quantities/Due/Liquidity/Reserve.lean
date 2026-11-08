import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Ledger
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile

variable {Address Row Item : Type*}
variable [Fintype Row] [Fintype Item]

/-- Original maturity times and original commit times, from the live start onward. -/
def cuts (view : Profile Address Row Item) : Finset ℚ :=
  (({view.start} ∪ Finset.univ.image view.deadline) ∪ Finset.univ.image view.commit).filter (view.start ≤ ·)

theorem start_mem_cuts (view : Profile Address Row Item) : view.start ∈ view.cuts := by
  simp [cuts]

theorem start_le_of_mem_cuts (view : Profile Address Row Item) {time : ℚ} (listed : time ∈ view.cuts) :
    view.start ≤ time :=
  (Finset.mem_filter.mp listed).2

def lastCut (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time) : ℚ :=
  (view.cuts.filter (· ≤ time)).max' ⟨view.start, Finset.mem_filter.mpr ⟨view.start_mem_cuts, reached⟩⟩

theorem lastCut_mem (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time) :
    view.lastCut time reached ∈ view.cuts :=
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).1

theorem lastCut_le (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time) :
    view.lastCut time reached ≤ time := by
  have listed : view.lastCut time reached ∈ view.cuts.filter (· ≤ time) := Finset.max'_mem _ _
  exact (Finset.mem_filter.mp listed).2

private theorem event_in_lastCut (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time)
    (day : ℚ) (listed : day ∈ ({view.start} ∪ Finset.univ.image view.deadline) ∪ Finset.univ.image view.commit) :
    day ≤ view.lastCut time reached ↔ day ≤ time := by
  refine ⟨fun before => before.trans (view.lastCut_le time reached), fun before => ?_⟩
  by_cases afterStart : view.start ≤ day
  · exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨listed, afterStart⟩, before⟩)
  · have atStart : view.start ≤ view.lastCut time reached :=
      view.start_le_of_mem_cuts (view.lastCut_mem time reached)
    exact (le_of_not_ge afterStart).trans atStart

theorem commit_le_lastCut_iff (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time)
    (item : Item) : view.commit item ≤ view.lastCut time reached ↔ view.commit item ≤ time :=
  view.event_in_lastCut time reached (view.commit item)
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ item)))

variable [DecidableEq Address]

theorem gap_at_lastCut (view : Profile Address Row Item) (time : ℚ) (reached : view.start ≤ time)
    (address : Address) : view.gap (view.lastCut time reached) address = view.gap time address := by
  have deadline (row : Row) := view.event_in_lastCut time reached (view.deadline row)
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ row))))
  have commit (item : Item) := view.commit_le_lastCut_iff time reached item
  simp only [gap, outstandingDue, paidThrough, actualStock, credited, debited, deadline, commit]

/-- Exact extra opening stock for this address across the original cuts through the horizon. -/
def reserveThrough (view : Profile Address Row Item) (horizon : ℚ) (address : Address) : ℚ :=
  (insert 0 ((view.cuts.filter (· ≤ horizon)).image (fun time => view.gap time address))).max'
    ⟨0, Finset.mem_insert_self _ _⟩

theorem reserveThrough_fits_iff (view : Profile Address Row Item) (horizon : ℚ) (address : Address)
    (reserve : ℚ) :
    view.reserveThrough horizon address ≤ reserve ↔
      0 ≤ reserve ∧ ∀ time, view.start ≤ time → time ≤ horizon → view.gap time address ≤ reserve := by
  let values := insert 0 ((view.cuts.filter (· ≤ horizon)).image (fun time => view.gap time address))
  have nonempty : values.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  change values.max' nonempty ≤ reserve ↔ _
  refine (Finset.max'_le_iff values nonempty).trans ?_
  constructor
  · intro bound
    refine ⟨bound _ (Finset.mem_insert_self _ _), fun time reached within => ?_⟩
    rw [← view.gap_at_lastCut time reached address]
    apply bound
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
      ⟨view.lastCut_mem time reached, (view.lastCut_le time reached).trans within⟩)
  · rintro ⟨zero, bound⟩ value listed
    rcases Finset.mem_insert.mp listed with rfl | listed
    · exact zero
    · obtain ⟨time, actual, rfl⟩ := Finset.mem_image.mp listed
      exact bound time (view.start_le_of_mem_cuts (Finset.mem_filter.mp actual).1)
        (Finset.mem_filter.mp actual).2

theorem reserveThrough_attained (view : Profile Address Row Item) (horizon : ℚ) (address : Address)
    (positive : 0 < view.reserveThrough horizon address) :
    ∃ time ∈ view.cuts, time ≤ horizon ∧ view.reserveThrough horizon address = view.gap time address := by
  have listed := Finset.max'_mem
    (insert 0 ((view.cuts.filter (· ≤ horizon)).image (fun time => view.gap time address)))
    ⟨0, Finset.mem_insert_self _ _⟩
  change view.reserveThrough horizon address ∈ _ at listed
  rcases Finset.mem_insert.mp listed with zero | witness
  · exact ((ne_of_gt positive) zero).elim
  obtain ⟨time, cutoff, exactGap⟩ := Finset.mem_image.mp witness
  exact ⟨time, (Finset.mem_filter.mp cutoff).1, (Finset.mem_filter.mp cutoff).2, exactGap.symm⟩

theorem reserveThrough_funded (view : Profile Address Row Item) (horizon : ℚ) (address : Address) :
    0 ≤ view.reserveThrough horizon address ∧ ∀ time, view.start ≤ time → time ≤ horizon →
      view.gap time address ≤ view.reserveThrough horizon address :=
  (view.reserveThrough_fits_iff horizon address _).mp le_rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile
