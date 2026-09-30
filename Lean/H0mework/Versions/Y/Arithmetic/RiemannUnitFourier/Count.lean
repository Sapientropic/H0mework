import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.UnitResponseSource

/-! The original unit-tail source emits its exact finite Dirichlet channels and its own reciprocal mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
def burnolRadiusUnitTailRaw (coordinate : ℂ) (radius x : ℝ) : ℂ :=
  if radius < |x| then -((|x| : ℝ) : ℂ) ^ (-coordinate) else 0

def burnolUnitTailDirichletChannels (radius x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈|x| / radius⌉₊

theorem burnolRadiusUnitTail_source_term (coordinate : ℂ) (radius x : ℝ)
    (positive : 0 < radius) (n : ℕ+) :
    (((n : ℕ) : ℂ)⁻¹) * burnolRadiusUnitTailRaw coordinate radius (x / (n : ℕ)) =
      if (n : ℕ) ∈ burnolUnitTailDirichletChannels radius x
      then -((|x| : ℝ) : ℂ) ^ (-coordinate) * ((n : ℕ) : ℂ) ^ (coordinate - 1) else 0 := by
  have nPositive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have nNonzero : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have incidence : radius < |x / (n : ℕ)| ↔
      (n : ℕ) ∈ burnolUnitTailDirichletChannels radius x := by
    simp only [burnolUnitTailDirichletChannels, Finset.mem_Ico, Nat.lt_ceil,
      Nat.succ_le_iff, n.pos, true_and, abs_div, abs_of_pos nPositive, lt_div_iff₀ nPositive,
      lt_div_iff₀ positive]
    constructor <;> intro h <;> nlinarith
  unfold burnolRadiusUnitTailRaw
  simp only [incidence]
  split_ifs
  · rw [abs_div, abs_of_pos nPositive, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) nPositive.le,
      Complex.cpow_sub _ _ nNonzero, Complex.cpow_one]
    simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv, inv_inv]
    ring
  · exact mul_zero _

theorem burnolRadiusUnitTail_finiteCoSum (coordinate : ℂ) (radius x : ℝ)
    (positive : 0 < radius) :
    burnolInnerGapForward (burnolRadiusUnitTailRaw coordinate radius) x =
      -((|x| : ℝ) : ℂ) ^ (-coordinate) *
        ∑ n ∈ burnolUnitTailDirichletChannels radius x, (n : ℂ) ^ (coordinate - 1) := by
  classical
  let term : ℕ → ℂ := fun n =>
    if n ∈ burnolUnitTailDirichletChannels radius x
    then -((|x| : ℝ) : ℂ) ^ (-coordinate) * (n : ℂ) ^ (coordinate - 1) else 0
  have support : Function.support term ⊆ {n : ℕ | 0 < n} := by
    intro n active
    have belongs : n ∈ burnolUnitTailDirichletChannels radius x := by
      by_contra outside
      exact active (if_neg outside)
    exact (Finset.mem_Ico.mp belongs).1
  calc
    _ = ∑' n : ℕ+, term (n : ℕ) := by
      apply tsum_congr
      exact burnolRadiusUnitTail_source_term coordinate radius x positive
    _ = ∑' n : ℕ, term n := tsum_subtype_eq_of_support_subset support
    _ = ∑ n ∈ burnolUnitTailDirichletChannels radius x, term n :=
      tsum_eq_sum (fun n outside => if_neg outside)
    _ = _ := by simp only [term, Finset.sum_ite_mem, Finset.inter_self, Finset.mul_sum]

theorem burnolRadiusUnitTail_reciprocalMean (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * burnolRadiusUnitTailRaw coordinate.value radius x) =
      -(radius : ℂ) ^ (-coordinate.value) / coordinate.value := by
  have read : (fun x : ℝ => (Ioi (0 : ℝ)).indicator
      (fun x => (x : ℂ)⁻¹ * burnolRadiusUnitTailRaw coordinate.value radius x) x) =
      (Ioi radius).indicator (fun x : ℝ => -(x : ℂ) ^ (-coordinate.value - 1)) := by
    funext x
    by_cases xPositive : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from xPositive)]
      simp only [burnolRadiusUnitTailRaw, abs_of_pos xPositive, indicator_apply, mem_Ioi]
      split_ifs
      · rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr xPositive.ne'), Complex.cpow_one]
        ring
      · exact mul_zero _
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from xPositive),
        indicator_of_notMem (show x ∉ Ioi radius from fun h => xPositive (positive.trans h))]
  rw [← integral_indicator measurableSet_Ioi, read, integral_indicator measurableSet_Ioi,
    integral_neg, integral_Ioi_cpow_of_lt (show (-coordinate.value - 1).re < -1 by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith [coordinate.rightHalf]) positive]
  rw [show -coordinate.value - 1 + 1 = -coordinate.value by ring]
  simp only [div_neg, neg_neg]

def burnolUnitTailDirichletRaw (coordinate : ℂ) (radius x : ℝ) : ℂ :=
  (radius : ℂ) ^ (-coordinate) / coordinate -
    ((|x| : ℝ) : ℂ) ^ (-coordinate) *
      ∑ n ∈ burnolUnitTailDirichletChannels radius x, (n : ℂ) ^ (coordinate - 1)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
