import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Count

/-! The actual Tate box of a reciprocal step unfolds into a finite harmonic channel sum and its own logarithmic mean. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolTateStepBoxRaw (lower upper : ℝ) (x : ℝ) : ℂ :=
  if lower ≤ |x| ∧ |x| < upper then 1 else 0

/-- The actual positive integer channels of the Tate box co-sum. -/
def burnolHarmonicStepChannels (lower upper x : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊|x| / upper⌋₊ ⌊|x| / lower⌋₊

theorem burnolTateStepBox_term (lower upper x : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (n : ℕ+) :
    (((n : ℕ) : ℂ)⁻¹) * burnolTateStepBoxRaw lower upper (x / (n : ℕ)) =
      if (n : ℕ) ∈ burnolHarmonicStepChannels lower upper x then (((n : ℕ) : ℂ)⁻¹) else 0 := by
  have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have nonzero : (n : ℕ) ≠ 0 := n.pos.ne'
  have incidence : lower ≤ |x / (n : ℕ)| ∧ |x / (n : ℕ)| < upper ↔
      (n : ℕ) ∈ burnolHarmonicStepChannels lower upper x := by
    simp only [abs_div, abs_of_pos positive, burnolHarmonicStepChannels, Finset.mem_Ioc,
      Nat.floor_lt' nonzero, Nat.le_floor_iff' nonzero,
      le_div_iff₀ positive, div_lt_iff₀ positive,
      div_lt_iff₀ upperPositive, le_div_iff₀ lowerPositive]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
  unfold burnolTateStepBoxRaw
  simp only [incidence]
  split_ifs <;> simp

theorem burnolTateStepBox_finiteCoSum (lower upper x : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) :
    burnolInnerGapForward (burnolTateStepBoxRaw lower upper) x =
      ∑ n ∈ burnolHarmonicStepChannels lower upper x, ((n : ℂ)⁻¹) := by
  classical
  let term : ℕ → ℂ := fun n =>
    if n ∈ burnolHarmonicStepChannels lower upper x then ((n : ℂ)⁻¹) else 0
  have support : Function.support term ⊆ {n : ℕ | 0 < n} := by
    intro n active
    have belongs : n ∈ burnolHarmonicStepChannels lower upper x := by
      by_contra outside
      exact active (if_neg outside)
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp belongs).1
  calc
    _ = ∑' n : ℕ+, term (n : ℕ) := by
      apply tsum_congr
      exact burnolTateStepBox_term lower upper x lowerPositive upperPositive
    _ = ∑' n : ℕ, term n := tsum_subtype_eq_of_support_subset support
    _ = ∑ n ∈ burnolHarmonicStepChannels lower upper x, term n :=
      tsum_eq_sum (fun n outside => if_neg outside)
    _ = _ := by simp only [term, Finset.sum_ite_mem, Finset.inter_self]

def burnolHarmonicStepWaveRaw (lower upper x : ℝ) : ℂ :=
  (∑ n ∈ burnolHarmonicStepChannels lower upper x, ((n : ℂ)⁻¹)) - (Real.log (upper / lower) : ℂ)

theorem burnolTateStepBox_reciprocalMean (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * burnolTateStepBoxRaw lower upper x) =
      (Real.log (upper / lower) : ℂ) := by
  have upperPositive := lowerPositive.trans_le ordered
  have read : (fun x : ℝ => (Ioi (0 : ℝ)).indicator
      (fun x => (x : ℂ)⁻¹ * burnolTateStepBoxRaw lower upper x) x) =
      (Ico lower upper).indicator (fun x : ℝ => (x : ℂ)⁻¹) := by
    funext x
    by_cases positive : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from positive)]
      simp only [burnolTateStepBoxRaw, abs_of_pos positive, indicator_apply, mem_Ico]
      split_ifs <;> simp
    · have outside : x ∉ Ico lower upper := by intro h; exact positive (lowerPositive.trans_le h.1)
      rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from positive), indicator_of_notMem outside]
  rw [← integral_indicator measurableSet_Ioi, read, integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le ordered]
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos lowerPositive upperPositive]
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
