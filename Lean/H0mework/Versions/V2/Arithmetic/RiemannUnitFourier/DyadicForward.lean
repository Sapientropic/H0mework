import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.DyadicSource

/-! The actual dyadic power shell emits its finite Dirichlet co-sum and reciprocal mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def burnolUnitDyadicChannels (x : ℝ) : Finset ℕ :=
  Finset.Ico ⌈|x|⌉₊ ⌈2 * |x|⌉₊

private theorem dyadicTate_term (s : ℂ) (x : ℝ) (n : ℕ+) :
    (((n : ℕ) : ℂ)⁻¹) * burnolUnitDyadicTateRaw s (x / (n : ℕ)) =
      if (n : ℕ) ∈ burnolUnitDyadicChannels x then
        ((|x| : ℝ) : ℂ) ^ (s - 1) * ((n : ℕ) : ℂ) ^ (-s) else 0 := by
  have np : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have nn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have incidence : (1 / 2 : ℝ) < |x / (n : ℕ)| ∧ |x / (n : ℕ)| ≤ 1 ↔
      (n : ℕ) ∈ burnolUnitDyadicChannels x := by
    simp only [burnolUnitDyadicChannels, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil,
      abs_div, abs_of_pos np, lt_div_iff₀ np, div_le_iff₀ np]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
  unfold burnolUnitDyadicTateRaw
  simp only [incidence]
  split_ifs
  · rw [abs_div, abs_of_pos np, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) np.le]
    simp only [Complex.ofReal_natCast]
    rw [Complex.cpow_sub _ _ nn, Complex.cpow_one, Complex.cpow_neg]
    field_simp
  · exact mul_zero _

private theorem dyadicTate_forward (s : ℂ) (x : ℝ) :
    burnolInnerGapForward (burnolUnitDyadicTateRaw s) x =
      ((|x| : ℝ) : ℂ) ^ (s - 1) * ∑ n ∈ burnolUnitDyadicChannels x, (n : ℂ) ^ (-s) := by
  classical
  by_cases zero : x = 0
  · subst x
    norm_num [burnolInnerGapForward, burnolUnitDyadicTateRaw, burnolUnitDyadicChannels]
  let term : ℕ → ℂ := fun n => if n ∈ burnolUnitDyadicChannels x
    then ((|x| : ℝ) : ℂ) ^ (s - 1) * (n : ℂ) ^ (-s) else 0
  have support : Function.support term ⊆ {n : ℕ | 0 < n} := by
    intro n active
    have belongs : n ∈ burnolUnitDyadicChannels x := by
      by_contra outside
      exact active (if_neg outside)
    exact (Nat.ceil_pos.mpr (abs_pos.mpr zero)).trans_le (Finset.mem_Ico.mp belongs).1
  calc
    _ = ∑' n : ℕ+, term (n : ℕ) := by apply tsum_congr; exact dyadicTate_term s x
    _ = ∑' n : ℕ, term n := tsum_subtype_eq_of_support_subset support
    _ = ∑ n ∈ burnolUnitDyadicChannels x, term n := tsum_eq_sum (fun n outside => if_neg outside)
    _ = _ := by simp only [term, Finset.sum_ite_mem, Finset.inter_self, Finset.mul_sum]

def burnolUnitDyadicMean (s : ℂ) : ℂ :=
  (1 - (1 / 2 : ℂ) ^ (s - 1)) / (s - 1)

private theorem dyadicTate_mean (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * burnolUnitDyadicTateRaw coordinate.value x) =
      burnolUnitDyadicMean coordinate.value := by
  have read : (fun x : ℝ => (Ioi (0 : ℝ)).indicator
      (fun x => (x : ℂ)⁻¹ * burnolUnitDyadicTateRaw coordinate.value x) x) =
      (Ioc (1 / 2 : ℝ) 1).indicator (fun x : ℝ => (x : ℂ) ^ (coordinate.value - 2)) := by
    funext x
    by_cases positive : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from positive)]
      simp only [burnolUnitDyadicTateRaw, abs_of_pos positive, indicator_apply, mem_Ioc]
      split_ifs
      · rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
        congr 1
        ring
      · exact mul_zero _
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from positive),
        indicator_of_notMem (show x ∉ Ioc (1 / 2 : ℝ) 1 from fun h => positive (lt_trans (by norm_num) h.1))]
  rw [← integral_indicator measurableSet_Ioi, read, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have exponent : coordinate.value - 2 ≠ -1 := by
    intro equal
    have realPart := congrArg Complex.re equal
    norm_num at realPart
    linarith [coordinate.belowOne]
  rw [integral_cpow (Or.inr ⟨exponent, by norm_num [Set.uIcc]⟩)]
  unfold burnolUnitDyadicMean
  norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.one_cpow]
  rw [show coordinate.value - 2 + 1 = coordinate.value - 1 by ring]

def burnolUnitDyadicWaveRaw (s : ℂ) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (s - 1) * ∑ n ∈ burnolUnitDyadicChannels x, (n : ℂ) ^ (-s) - burnolUnitDyadicMean s

theorem burnolUnitDyadicFourierShell_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (burnolUnitTailResponse coordinate 2 - burnolUnitTailResponse coordinate 1) : ℝ → ℂ)
      =ᵐ[volume] burnolUnitDyadicWaveRaw coordinate.value := by
  let source := burnolUnitDyadicTateShell coordinate
  let value := fourierL2 (burnolUnitTailResponse coordinate 2 - burnolUnitTailResponse coordinate 1)
  have represents : (source : ℝ → ℂ) =ᵐ[volume] burnolUnitDyadicTateRaw coordinate.value := burnolUnitDyadicTateShell_coeFn coordinate
  have even : reflectL2 source = source := burnolReflectL2_eq_of_even_raw source _ represents
    (fun x => by simp only [burnolUnitDyadicTateRaw, abs_neg])
  have gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae represents,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x read inside
    rw [read]
    apply if_neg
    intro active
    linarith [active.1, abs_le.mpr inside]
  have realization (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead source test = ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolUnitDyadicTateShell_realizes coordinate test
  obtain ⟨raw, rawRep, _, valueRep⟩ := burnolRemainderSourceRead_realization_ae source value even gap realization
  have same := rawRep.symm.trans represents
  have forward := burnolInnerGapForward_ae_congr raw (burnolUnitDyadicTateRaw coordinate.value) same
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = burnolUnitDyadicMean coordinate.value := by
    rw [← dyadicTate_mean coordinate]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae same] with x hx
    rw [hx]
  filter_upwards [valueRep, forward] with x read coSum
  rw [read, coSum, mean, dyadicTate_forward]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
