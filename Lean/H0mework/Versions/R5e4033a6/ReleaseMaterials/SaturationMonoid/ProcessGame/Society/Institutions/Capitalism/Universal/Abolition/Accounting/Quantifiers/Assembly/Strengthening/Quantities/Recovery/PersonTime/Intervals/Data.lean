import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals

open scoped BigOperators

/-- A half-open interval of the original rational clock. -/
structure Span where
  start : ℚ
  finish : ℚ
  ordered : start ≤ finish

def Span.Contains (span : Span) (time : ℚ) : Prop :=
  span.start ≤ time ∧ time < span.finish

instance (span : Span) (time : ℚ) : Decidable (span.Contains time) := by
  unfold Span.Contains
  infer_instance

def endpoints (spans : List Span) : Finset ℚ :=
  (spans.flatMap fun span => [span.start, span.finish]).toFinset

theorem start_mem_endpoints {spans : List Span} {span : Span} (listed : span ∈ spans) :
    span.start ∈ endpoints spans := by
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨span, listed, by simp⟩)

theorem finish_mem_endpoints {spans : List Span} {span : Span} (listed : span ∈ spans) :
    span.finish ∈ endpoints spans := by
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨span, listed, by simp⟩)

def present (spans : List Span) (time : ℚ) : Bool :=
  spans.any fun span => decide (span.Contains time)

theorem present_iff (spans : List Span) (time : ℚ) :
    present spans time = true ↔ ∃ span ∈ spans, span.Contains time := by
  simp [present, List.any_eq_true]

/-- The right edge of a cell is the least original endpoint strictly to
its right. The last endpoint contributes a zero-width cell. -/
def following (points : Finset ℚ) (left : ℚ) : ℚ :=
  let later := points.filter fun point => left < point
  if nonempty : later.Nonempty then later.min' nonempty else left

theorem following_ge (points : Finset ℚ) (left : ℚ) : left ≤ following points left := by
  unfold following
  dsimp only
  split
  · rename_i nonempty
    exact (Finset.mem_filter.mp (Finset.min'_mem _ nonempty)).2.le
  · exact le_rfl

theorem following_spec {points : Finset ℚ} {left right : ℚ}
    (inside : right ∈ points) (later : left < right) :
    left < following points left ∧ following points left ∈ points ∧ following points left ≤ right := by
  have rightLater := Finset.mem_filter.mpr ⟨inside, later⟩
  have existsLater : (points.filter fun point => left < point).Nonempty := ⟨right, rightLater⟩
  unfold following
  dsimp only
  rw [dif_pos existsLater]
  have member := Finset.mem_filter.mp (Finset.min'_mem _ existsLater)
  exact ⟨member.2, member.1, Finset.min'_le _ _ rightLater⟩

def active (points : Finset ℚ) (spans : List Span) : Finset ℚ :=
  points.filter fun left => present spans left = true

def lengthOn (points : Finset ℚ) (spans : List Span) : ℚ :=
  ∑ left ∈ active points spans, (following points left - left)

def length (spans : List Span) : ℚ :=
  lengthOn (endpoints spans) spans

theorem lengthOn_nonnegative (points : Finset ℚ) (spans : List Span) : 0 ≤ lengthOn points spans :=
  Finset.sum_nonneg fun left _ => sub_nonneg.mpr (following_ge points left)

theorem length_nonnegative (spans : List Span) : 0 ≤ length spans :=
  lengthOn_nonnegative _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals
