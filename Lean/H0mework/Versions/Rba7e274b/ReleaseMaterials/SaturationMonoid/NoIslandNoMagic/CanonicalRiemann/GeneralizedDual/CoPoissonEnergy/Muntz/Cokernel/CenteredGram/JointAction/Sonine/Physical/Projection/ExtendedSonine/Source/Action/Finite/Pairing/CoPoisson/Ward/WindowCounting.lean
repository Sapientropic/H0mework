import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmallScaleLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.WindowCounting

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def windowSource (N : ℕ) (state : BurnolQuarterIntervalL2) : BurnolQuarterIntervalL2 :=
  burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension state))

private theorem counting_eq (scale : ℝ) (state : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension state)) =
      InverseAction.countingWindow scale state := by
  simp only [ContinuousChannels.channel, InverseAction.countingWindow, neg_one_mul, map_smul]

private theorem counting_integrable (upper : ℝ) (state : BurnolQuarterIntervalL2) :
    IntegrableOn (fun scale : ℝ => InverseAction.countingWindow scale state) (Ioc 0 upper) := by
  simpa only [counting_eq] using! burnolQuarterRestriction.integrable_comp
    (ContinuousChannels.channel_integrable (-1) upper (burnolQuarterZeroExtension state))

private theorem average_eq (upper : ℝ) (state : BurnolQuarterIntervalL2) :
    (∫ scale : ℝ in Ioc 0 upper, InverseAction.countingWindow scale state) =
      burnolQuarterRestriction (ContinuousChannels.normalization upper (burnolQuarterZeroExtension state)) := by
  simpa only [counting_eq, ContinuousChannels.normalization] using!
    burnolQuarterRestriction.integral_comp_comm
      (ContinuousChannels.channel_integrable (-1) upper (burnolQuarterZeroExtension state))

theorem windowSource_as_counting (N : ℕ) (state : BurnolQuarterIntervalL2) :
    windowSource N state =
      (∑ n ∈ Finset.Ico 1 N, InverseAction.countingWindow n state) -
        ∫ scale : ℝ in Ioc 0 (N : ℝ), InverseAction.countingWindow scale state := by
  unfold windowSource FiniteForcing.source
  rw [map_sub, map_sum, ← average_eq]
  simp only [Channels.sourceChannel, InverseAction.countingWindow, map_smul]

private theorem split_average (N : ℕ) (positive : 0 < N) (state : BurnolQuarterIntervalL2) :
    (∫ scale : ℝ in Ioc 0 (N : ℝ), InverseAction.countingWindow scale state) =
      burnolQuarterRestriction (ContinuousChannels.normalization 1 (burnolQuarterZeroExtension state)) +
        ∫ scale : ℝ in Ioc 1 (N : ℝ), InverseAction.countingWindow scale state := by
  have after : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have integrable := counting_integrable N state
  rw [← average_eq, ← Ioc_union_Ioc_eq_Ioc zero_le_one after]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (integrable.mono_set (Ioc_subset_Ioc le_rfl after))
    (integrable.mono_set (Ioc_subset_Ioc zero_le_one le_rfl))

def harmonicCoefficient (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ)⁻¹) - (Real.log (N : ℝ) : ℂ)

private theorem integral_inverse (N : ℕ) (positive : 0 < N) :
    (∫ scale : ℝ in Ioc 1 (N : ℝ), (scale : ℂ)⁻¹) = (Real.log (N : ℝ) : ℂ) := by
  have after : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have regular : ContinuousOn (fun scale : ℝ => (scale : ℂ)⁻¹) (Icc 1 (N : ℝ)) :=
    Complex.continuous_ofReal.continuousOn.inv₀
      (fun scale inside => Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le inside.1).ne')
  have derivative (scale : ℝ) (inside : scale ∈ uIcc 1 (N : ℝ)) :
      HasDerivAt (fun value : ℝ => Complex.log (value : ℂ)) (scale : ℂ)⁻¹ scale := by
    have located : scale ∈ Icc 1 (N : ℝ) := by simpa only [uIcc_of_le after] using inside
    exact (Complex.hasDerivAt_log (Complex.ofReal_mem_slitPlane.mpr
      (zero_lt_one.trans_le located.1))).comp_ofReal
  have primitive := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    (regular.intervalIntegrable_of_Icc after)
  rw [← intervalIntegral.integral_of_le after, primitive, Complex.ofReal_one, log_one, sub_zero,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ N)]

/-- The unprojected constant source retains both its harmonic scalar and its genuine logarithmic profile. -/
theorem constant_source (N : ℕ) (positive : 0 < N) :
    windowSource N (intervalConstant q) = harmonicCoefficient N • intervalConstant q + SmallScaleLog.logL2 := by
  rw [windowSource_as_counting, split_average N positive, SmallScaleLog.constant_normalization_window]
  have large : (∫ scale : ℝ in Ioc 1 (N : ℝ), InverseAction.countingWindow scale (intervalConstant q)) =
      (Real.log (N : ℝ) : ℂ) • intervalConstant q := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun scale inside =>
      SingularCounting.counting_constant scale inside.1.le), integral_smul_const, integral_inverse N positive]
  have integers : (∑ n ∈ Finset.Ico 1 N, InverseAction.countingWindow n (intervalConstant q)) =
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ)⁻¹) • intervalConstant q := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro n inside
    simpa only [Complex.ofReal_natCast] using SingularCounting.counting_constant n
      (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  rw [large, integers]
  unfold harmonicCoefficient
  module

/-- The singular source is read in the full original interval carrier, retaining its constant slot. -/
theorem power_source (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    windowSource N (SingularCounting.powerL2 coordinate) =
      FiniteForcing.coefficient (star coordinate.value) N • SingularCounting.powerL2 coordinate +
      ((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q := by
  rw [windowSource_as_counting, split_average N positive, SmallScaleLog.power_normalization_window]
  have after : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have large : (∫ scale : ℝ in Ioc 1 (N : ℝ),
      InverseAction.countingWindow scale (SingularCounting.powerL2 coordinate)) =
      (((N : ℂ) ^ (1 - star coordinate.value) - 1) / (1 - star coordinate.value)) •
        SingularCounting.powerL2 coordinate := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun scale inside =>
      SingularCounting.counting_power coordinate scale inside.1.le), integral_smul_const,
      ← intervalIntegral.integral_of_le after]
    congr 1
    have exponent : -1 < (-star coordinate.value).re := by
      simpa only [neg_re, star_def, conj_re] using neg_lt_neg coordinate.belowOne
    rw [integral_cpow (Or.inl exponent), show -star coordinate.value + 1 = 1 - star coordinate.value by ring,
      Complex.ofReal_natCast, Complex.ofReal_one, one_cpow]
  have integers : (∑ n ∈ Finset.Ico 1 N, InverseAction.countingWindow n (SingularCounting.powerL2 coordinate)) =
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-star coordinate.value)) • SingularCounting.powerL2 coordinate := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro n inside
    simpa only [Complex.ofReal_natCast] using SingularCounting.counting_power coordinate n
      (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  rw [large, integers]
  unfold FiniteForcing.coefficient
  rw [sub_div]
  module

private theorem inverse_sum (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 (N + 1), (n : ℂ)⁻¹) = (harmonic N : ℂ) := by
  induction N with
  | zero => simp
  | succ N previous =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N + 1), previous, harmonic_succ]
    push_cast
    rfl

theorem harmonicCoefficient_limit :
    Tendsto harmonicCoefficient atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have original := Complex.continuous_ofReal.tendsto Real.eulerMascheroniConstant |>.comp
    Real.tendsto_eulerMascheroniSeq
  convert! original using 1
  funext N
  simp only [Function.comp_apply, harmonicCoefficient, inverse_sum, Real.eulerMascheroniSeq, Complex.ofReal_sub]
  norm_cast

theorem constant_limit :
    Tendsto (fun N : ℕ => windowSource N (intervalConstant q)) atTop
      (𝓝 ((Real.eulerMascheroniConstant : ℂ) • intervalConstant q + SmallScaleLog.logL2)) := by
  apply ((harmonicCoefficient_limit.smul_const (intervalConstant q)).add_const SmallScaleLog.logL2).congr'
  filter_upwards [eventually_ge_atTop 1] with N after
  exact (constant_source N (Nat.lt_of_lt_of_le (by decide : 0 < 1) after)).symm

theorem power_limit_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => windowSource N (SingularCounting.powerL2 coordinate)) atTop
      (𝓝 (((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q)) := by
  have arithmetic := ((DirichletCoefficient.original_coefficient_limits coordinate zero).1.smul_const
    (SingularCounting.powerL2 coordinate)).add_const
      (((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q)
  simp only [zero_smul, zero_add] at arithmetic
  apply arithmetic.congr'
  filter_upwards [eventually_ge_atTop 1] with N after
  exact (power_source coordinate N (Nat.lt_of_lt_of_le (by decide : 0 < 1) after)).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.WindowCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
