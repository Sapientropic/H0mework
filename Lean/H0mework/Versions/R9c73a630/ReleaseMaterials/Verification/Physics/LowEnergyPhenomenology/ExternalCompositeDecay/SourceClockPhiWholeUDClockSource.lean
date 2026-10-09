import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiUDFirstCurrentPayment
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiCombinedScalePressure SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiNormalizedScalarBudget SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource
open FinitePhysicalSource MeasureTheory Filter Set
open scoped ContDiff Topology InnerProductSpace
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
private abbrev C := SourceScalarDoubleCurrent.bracket diagonalAction A
private abbrev n : ℝ := sourceTime 0
private abbrev config := GaussHistoryHilbert.configurationMeasure
attribute [local irreducible] diagonalAction embed
private def potentialKernel (T : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  if hT : 0 < T then densityPair (A f) (gaussianProfileWeight T hT (-2/3) (A f)) z else 0
private theorem weighted_density (T : ℝ) (hT : 0 < T) (f : QuantumTest) (z : SourceCoordinateSlice) :
    potentialKernel T f z = (((forwardRatio T z)^(-2/3:ℝ):ℝ):ℂ)*densityPair (A f) (A f) z := by
  rw [potentialKernel,dif_pos hT,gaussianProfileWeight,densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (A f z word)*((((forwardRatio T z)^(-2/3:ℝ):ℝ):ℂ)*A f z word)=_
  ring
private theorem potential_bound (T : ℝ) (hT : 0 < T) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ‖potentialKernel T f z‖ ≤ ‖densityPair (A f) (A f) z‖ := by
  rw [weighted_density T hT f z]
  by_cases hz : z ∈ physicalChart
  · have hr : 1 ≤ forwardRatio T z := by
      unfold forwardRatio
      rw [le_div_iff₀ (volume_pos ⟨z,hz⟩)]
      nlinarith
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ forwardRatio T z) _)]
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num))
      (norm_nonneg _)).trans_eq (one_mul _)
  · have hf : A f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz ((A f).tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,mul_zero,norm_zero,le_refl]
private theorem potential_point_limit (f : QuantumTest) (z : SourceCoordinateSlice) :
    Tendsto (fun T => potentialKernel T f z) atTop (𝓝 0) := by
  by_cases hz : z ∈ physicalChart
  · have hr : Tendsto (fun T => forwardRatio T z) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop ((b*volume z-volume z)/18)] with T hT
      unfold forwardRatio
      rw [le_div_iff₀ (volume_pos ⟨z,hz⟩)]
      nlinarith
    have hp : Tendsto (fun T => (forwardRatio T z)^(-2/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,Function.comp_def] using! (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/3)).comp hr
    have hc := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hp
    have h := hc.mul_const (densityPair (A f) (A f) z)
    simp only [Complex.ofReal_zero,zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact (weighted_density T hT f z).symm
  · have hf : A f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz ((A f).tsupport_subset h))
    have he (T : ℝ) : potentialKernel T f z = 0 := by
      unfold potentialKernel
      split_ifs <;> simp only [densityPair,hf,map_zero,inner_zero_left]
    simp_rw [he]
    exact tendsto_const_nhds

/-- The original source density removes the entire auxiliary-clock endpoint, without a tail witness. -/
theorem actual_clock_potential_vanishes (f : QuantumTest) :
    Tendsto (fun T : ℝ => if hT : 0 < T then clockPotential T hT f else 0) atTop (𝓝 0) := by
  have hm : ∀ᶠ T : ℝ in atTop, AEStronglyMeasurable (potentialKernel T f) config := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have he : potentialKernel T f = densityPair (A f) (gaussianProfileWeight T hT (-2/3) (A f)) := by
      funext z
      exact dif_pos hT
    rw [he]
    exact (densityPair_integrable (A f) (gaussianProfileWeight T hT (-2/3) (A f))).aestronglyMeasurable
  have hb : ∀ᶠ T : ℝ in atTop, ∀ᵐ z ∂config, ‖potentialKernel T f z‖ ≤ ‖densityPair (A f) (A f) z‖ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact Eventually.of_forall (potential_bound T hT f)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖densityPair (A f) (A f) z‖) hm hb
    (densityPair_integrable (A f) (A f)).norm
    (Eventually.of_forall (potential_point_limit f))
  simp only [integral_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  simp only [dif_pos hT,clockPotential,sourcePair_integral,potentialKernel]

/-- The entire original positive clock pays exactly one twelfth of the original A-square. -/
theorem actual_whole_clock_UD_payment (ξ η : ℝ) (f : QuantumTest) :
    IntegrableOn (fun s => actualClockUDSquare s ξ η f) (Ioi (0:ℝ)) MeasureTheory.volume ∧
    12*(∫ s in Ioi (0:ℝ), actualClockUDSquare s ξ η f) = ‖embed (A f)‖^2 := by
  have hn (s : ℝ) : 0 ≤ actualClockUDSquare s ξ η f := by
    unfold actualClockUDSquare
    split_ifs <;> positivity
  have hp := (Complex.continuous_re.tendsto (0:ℂ)).comp (actual_clock_potential_vanishes f)
  have hi : Tendsto (fun T : ℝ => ∫ s in (0:ℝ)..T, actualClockUDSquare s ξ η f)
      atTop (𝓝 (‖embed (A f)‖^2/12)) := by
    have h := ((tendsto_const_nhds (x := ‖embed (A f)‖^2)).sub hp).div_const 12
    simp only [Complex.zero_re,sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simp only [Function.comp_apply,dif_pos hT]
    have he := (actual_finite_clock_UD_payment T hT ξ η f).2
    linarith only [he]
  have hfi (T : ℝ) : IntegrableOn (fun s => actualClockUDSquare s ξ η f) (Ioc (0:ℝ) T) MeasureTheory.volume := by
    by_cases hT : 0 < T
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
        (actual_finite_clock_UD_payment T hT ξ η f).1
    · rw [Ioc_eq_empty hT]
      exact integrableOn_empty
  have hiN : Tendsto (fun T : ℝ => ∫ s in (0:ℝ)..T, ‖actualClockUDSquare s ξ η f‖)
      atTop (𝓝 (‖embed (A f)‖^2/12)) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _)] using hi
  have hall := integrableOn_Ioi_of_intervalIntegral_norm_tendsto (‖embed (A f)‖^2/12) 0 hfi tendsto_id hiN
  refine ⟨hall,?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hall tendsto_id
  have he := tendsto_nhds_unique hlim hi
  linarith only [he]

/-- The full clock UD payment cancels the normalized first-current A price with no endpoint term. -/
theorem actual_normalized_first_current_whole_clock_payment
    (ξ η : ℝ) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let f := normalizedForcing m ell F z hz g
    firstCurrentJointRemainder m ell F z hz g -
      (n/96)*(∫ s in Ioi (0:ℝ), actualClockUDSquare s ξ η w) =
      (576/n)*(sourcePair w (conditionalHamiltonianSquare w)).re -
      (n/1152)*‖embed (A w)-((1152/n:ℝ):ℂ) • embed (C w)‖^2 +
      matchedField w + (432/n)*‖embed f‖^2 -
      (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2 -
      (n/96)*‖embed (U (D w))‖^2 := by
  dsimp only
  have hfinite := actual_normalized_first_current_clock_payment 1 (by norm_num) ξ η m ell F z hz g
  have hT := (actual_finite_clock_UD_payment 1 (by norm_num) ξ η (normalizedState m ell F z hz g)).2
  have hwhole := (actual_whole_clock_UD_payment ξ η (normalizedState m ell F z hz g)).2
  dsimp only at hfinite
  linear_combination (norm:=ring) hfinite - (n/1152)*(hwhole-hT)
end LowEnergy.FirstCurrentPayer
