import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiUDClockSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn
open SourceClockPhiCombinedScalePressure SourceClockPhiHeatLocalNativeGaussian ClockPhiHeatCorrectedCovarianceSource
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget FinitePhysicalSource
open MeasureTheory Filter Set
open scoped ContDiff Topology InnerProductSpace
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
private abbrev H0 := diagonalAction
private abbrev config := GaussHistoryHilbert.configurationMeasure
attribute [local irreducible] diagonalAction embed

private theorem density_multiply (b : SourceCoordinateSlice → ℝ)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val)
    (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair f (multiply b hb g) z = (b z:ℂ)*densityPair f g z := by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (f z word)*((b z:ℂ)*g z word)=_
  ring
private theorem density_left_multiply (b : SourceCoordinateSlice → ℝ)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val)
    (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair (multiply b hb f) g z = (b z:ℂ)*densityPair f g z := by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star ((b z:ℂ)*f z word)*g z word=_
  simp only [map_mul,Complex.star_def,Complex.conj_ofReal]
  ring
private theorem density_offchart (f g : QuantumTest) (z : SourceCoordinateSlice)
    (hz : z ∉ physicalChart) : densityPair f g z = 0 := by
  have hf : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
  simp only [densityPair,hf,map_zero,inner_zero_left]
private theorem ratio_ge_one (s : ℝ) (hs : 0 ≤ s) (z : physicalChart) :
    1 ≤ forwardRatio s z.val := by
  unfold forwardRatio
  rw [le_div_iff₀ (volume_pos z)]
  nlinarith
private theorem ratio_deriv (a s : ℝ) (hs : 0 ≤ s) (z : physicalChart) :
    HasDerivAt (fun t : ℝ => (forwardRatio t z.val)^a)
      ((18*reciprocalVolume z.val)*a*(forwardRatio s z.val)^(a-1)) s := by
  have he (t : ℝ) : forwardRatio t z.val = 1+(18*reciprocalVolume z.val)*t := by
    unfold forwardRatio reciprocalVolume
    field_simp [(volume_pos z).ne']
  have hb := ((hasDerivAt_id s).const_mul (18*reciprocalVolume z.val)).const_add 1
  have hr := hb.rpow_const (p:=a) (Or.inl (by rw [←he]; exact (forward_ratio_pos s hs z).ne'))
  simp_rw [he]
  simpa only [mul_one,id_eq] using hr
private theorem ratio_integral (T : ℝ) (hT : 0 ≤ T) (z : physicalChart) :
    (∫ s in (0:ℝ)..T, (forwardRatio s z.val)^(-5/3:ℝ)) =
      volume z.val/12*(1-(forwardRatio T z.val)^(-2/3:ℝ)) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      HasDerivAt (fun t : ℝ => -(volume z.val/12)*(forwardRatio t z.val)^(-2/3:ℝ))
        ((forwardRatio s z.val)^(-5/3:ℝ)) s := by
    have h := (ratio_deriv (-2/3) s hs.1 z).const_mul (-(volume z.val/12))
    convert! h using 1
    norm_num
    unfold reciprocalVolume
    field_simp [(volume_pos z).ne']
    ring
  have hi : IntervalIntegrable (fun s : ℝ => (forwardRatio s z.val)^(-5/3:ℝ)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun s hs => (ratio_deriv (-5/3) s hs.1 z).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le hT] using hs)) hi
  have hz : forwardRatio 0 z.val = 1 := by
    unfold forwardRatio
    simp only [mul_zero,add_zero,div_self (volume_pos z).ne']
  rw [h,hz,Real.one_rpow]
  ring

private def clockKernel (f : QuantumTest) (p : ℝ × SourceCoordinateSlice) : ℂ :=
  if 0 ≤ p.1 then (((forwardRatio p.1 p.2)^(-5/3:ℝ):ℝ):ℂ)*densityPair (U (D f)) (U (D f)) p.2 else 0
private theorem power_measurable (a : ℝ) : Measurable (fun x : ℝ => x^a) :=
  measurable_of_continuousOn_compl_singleton 0 (fun x hx =>
    (Real.continuousAt_rpow_const x a (.inl (by simpa only [mem_compl_iff,mem_singleton_iff] using hx))).continuousWithinAt)
private theorem kernel_measurable (T : ℝ) (f : QuantumTest) :
    AEStronglyMeasurable (clockKernel f) ((MeasureTheory.volume.restrict (Ioc (0:ℝ) T)).prod config) := by
  have hv : Measurable (fun p : ℝ × SourceCoordinateSlice => volume p.2) :=
    volume_smooth.continuous.measurable.comp measurable_snd
  have hr : Measurable (fun p : ℝ × SourceCoordinateSlice => forwardRatio p.1 p.2) :=
    (hv.add (measurable_const.mul measurable_fst)).div hv
  have hm := ((Complex.continuous_ofReal.measurable.comp ((power_measurable (-5/3)).comp hr)).aestronglyMeasurable).mul
      ((densityPair_integrable (U (D f)) (U (D f))).aestronglyMeasurable.comp_snd
        (μ := MeasureTheory.volume.restrict (Ioc (0:ℝ) T)))
  exact hm.indicator (measurable_fst measurableSet_Ici)
private theorem kernel_bound (f : QuantumTest) (p : ℝ × SourceCoordinateSlice) :
    ‖clockKernel f p‖ ≤ ‖densityPair (U (D f)) (U (D f)) p.2‖ := by
  unfold clockKernel
  split_ifs with hs
  · by_cases hz : p.2 ∈ physicalChart
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (forward_ratio_pos p.1 hs ⟨p.2,hz⟩).le _)]
      exact (mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos
        (ratio_ge_one p.1 hs ⟨p.2,hz⟩) (by norm_num)) (norm_nonneg _)).trans_eq (one_mul _)
    · rw [density_offchart _ _ _ hz,mul_zero,norm_zero]
  · simpa only [norm_zero] using norm_nonneg (densityPair (U (D f)) (U (D f)) p.2)
private theorem kernel_integrable (T : ℝ) (f : QuantumTest) :
    Integrable (clockKernel f) ((MeasureTheory.volume.restrict (Ioc (0:ℝ) T)).prod config) := by
  have hi := (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ))
    (MeasureTheory.volume.restrict (Ioc (0:ℝ) T))).mul_prod
    (densityPair_integrable (U (D f)) (U (D f))).norm
  simp only [one_mul] at hi
  exact hi.mono' (kernel_measurable T f) (Eventually.of_forall (kernel_bound f))

private theorem kernel_time_integral (T : ℝ) (hT : 0 < T) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (∫ s in Ioc (0:ℝ) T, clockKernel f (s,z)) =
      (1/12:ℂ)*(densityPair (A f) (A f) z -
        densityPair (A f) (gaussianProfileWeight T hT (-2/3) (A f)) z) := by
  rw [←intervalIntegral.integral_of_le hT.le]
  have he : (∫ s in (0:ℝ)..T, clockKernel f (s,z)) =
      (∫ s in (0:ℝ)..T, (((forwardRatio s z)^(-5/3:ℝ):ℝ):ℂ))*densityPair (U (D f)) (U (D f)) z := by
    rw [←intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le hT.le] using hs : s ∈ Icc (0:ℝ) T).1
    simp only [clockKernel,if_pos hs0]
  rw [he,intervalIntegral.integral_ofReal]
  by_cases hz : z ∈ physicalChart
  · rw [ratio_integral T hT.le ⟨z,hz⟩]
    change _ = (1/12:ℂ)*(densityPair (inverseRootAction (D f)) (inverseRootAction (D f)) z -
      densityPair (inverseRootAction (D f)) (gaussianProfileWeight T hT (-2/3) (inverseRootAction (D f))) z)
    simp only [U,inverseVolumeAction,inverseRootAction,gaussianProfileWeight,density_multiply,density_left_multiply]
    have ha : inverseRootVolume z * inverseRootVolume z = reciprocalVolume z := by
      unfold inverseRootVolume reciprocalVolume
      rw [←mul_inv,Real.mul_self_sqrt (volume_pos ⟨z,hz⟩).le]
    have hu : volume z * reciprocalVolume z = 1 := by
      exact mul_inv_cancel₀ (volume_pos ⟨z,hz⟩).ne'
    push_cast
    have hc : (inverseRootVolume z:ℂ)*(inverseRootVolume z:ℂ) = (reciprocalVolume z:ℂ) := by exact_mod_cast ha
    have hcU : (volume z:ℂ)*(reciprocalVolume z:ℂ) = 1 := by exact_mod_cast hu
    linear_combination (norm:=ring) (1/12:ℂ)*(1-(((forwardRatio T z)^(-2/3:ℝ):ℝ):ℂ))*
      densityPair (D f) (D f) z * ((reciprocalVolume z:ℂ)*hcU-hc)
  · simp only [density_offchart _ _ _ hz,mul_zero,sub_zero]

def actualClockUDSquare (s ξ η : ℝ) (f : QuantumTest) : ℝ :=
  if hs : 0 < s then ‖embed (U (D (correctedCompleteCore s hs ξ η f)))‖^2 else 0

private theorem kernel_config_integral (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f : QuantumTest) :
    (∫ z, clockKernel f (s,z) ∂config) = (actualClockUDSquare s ξ η f : ℂ) := by
  rw [actualClockUDSquare,dif_pos hs]
  have hnorm : clockUDDensity s hs f = (‖embed (U (D (correctedCompleteCore s hs ξ η f)))‖^2 : ℝ) := by
    simpa only [Complex.ofReal_pow] using actual_corrected_UD_clock_density s hs ξ η f
  rw [←hnorm]
  unfold clockUDDensity
  rw [sourcePair_integral]
  apply integral_congr_ae
  refine Eventually.of_forall fun z => ?_
  by_cases hz : z ∈ physicalChart
  · have hp : (forwardRatio s z)^(-2/3:ℝ) = (forwardRatio s z)^(-5/3:ℝ)*forwardRatio s z := by
      calc _ = (forwardRatio s z)^((-5/3:ℝ)+1) := by norm_num
           _ = _ := by rw [Real.rpow_add (forward_ratio_pos s hs.le ⟨z,hz⟩),Real.rpow_one]
    have hu : forwardU s z*forwardRatio s z = reciprocalVolume z := by
      unfold forwardU forwardRatio reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne',ne_of_gt (by linarith [volume_pos ⟨z,hz⟩] : 0 < volume z+18*s)]
    have ha : inverseRootVolume z*inverseRootVolume z = reciprocalVolume z := by
      unfold inverseRootVolume reciprocalVolume
      rw [←mul_inv,Real.mul_self_sqrt (volume_pos ⟨z,hz⟩).le]
    change clockKernel f (s,z) = densityPair (forwardUAction s hs.le (inverseRootAction (D f)))
      (gaussianProfileWeight s hs (-2/3) (inverseRootAction (D f))) z
    simp only [clockKernel,if_pos hs.le,U,inverseVolumeAction,forwardUAction,inverseRootAction,
      gaussianProfileWeight,density_multiply,density_left_multiply]
    rw [hp]
    push_cast
    have hc : (inverseRootVolume z:ℂ)*(inverseRootVolume z:ℂ) = (reciprocalVolume z:ℂ) := by exact_mod_cast ha
    have hcU : (forwardU s z:ℂ)*(forwardRatio s z:ℂ) = (reciprocalVolume z:ℂ) := by exact_mod_cast hu
    linear_combination (norm:=ring) -(((forwardRatio s z)^(-5/3:ℝ):ℝ):ℂ)*densityPair (D f) (D f) z *
      ((forwardU s z:ℂ)*(forwardRatio s z:ℂ)*hc+(reciprocalVolume z:ℂ)*hcU)
  · simp only [clockKernel,if_pos hs.le,density_offchart _ _ _ hz,mul_zero]

/-- Finite auxiliary clock consumes the same actual corrected source in both noise coordinates. -/
theorem actual_finite_clock_UD_payment (T : ℝ) (hT : 0 < T) (ξ η : ℝ) (f : QuantumTest) :
    IntervalIntegrable (fun s => actualClockUDSquare s ξ η f) MeasureTheory.volume 0 T ∧
    12 * (∫ s in (0:ℝ)..T, actualClockUDSquare s ξ η f) =
      ‖embed (A f)‖^2 - (clockPotential T hT f).re := by
  have hk := kernel_integrable T f
  have he : (fun s => ∫ z, clockKernel f (s,z) ∂config) =ᵐ[MeasureTheory.volume.restrict (Ioc (0:ℝ) T)]
      (fun s => (actualClockUDSquare s ξ η f : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact kernel_config_integral s hs.1 ξ η f
  have hiC : Integrable (fun s => (actualClockUDSquare s ξ η f : ℂ))
      (MeasureTheory.volume.restrict (Ioc (0:ℝ) T)) := hk.integral_prod_left.congr he
  have hiR : IntegrableOn (fun s => actualClockUDSquare s ξ η f) (Ioc (0:ℝ) T) MeasureTheory.volume := by
    simpa only [IntegrableOn,RCLike.re_eq_complex_re,Complex.ofReal_re] using! hiC.re
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hiR,?_⟩
  have heq : (∫ s in Ioc (0:ℝ) T, (actualClockUDSquare s ξ η f : ℂ)) =
      (1/12:ℂ)*(sourcePair (A f) (A f)-clockPotential T hT f) := by
    rw [←integral_congr_ae he,integral_integral_swap (f := fun s z => clockKernel f (s,z)) hk]
    simp_rw [kernel_time_integral T hT f]
    rw [integral_const_mul,integral_sub (densityPair_integrable _ _) (densityPair_integrable _ _),
      ←sourcePair_integral,←sourcePair_integral]
    rfl
  rw [integral_complex_ofReal] at heq
  have hre := congrArg Complex.re heq
  have hn : (sourcePair (A f) (A f)).re = ‖embed (A f)‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜:=ℂ) (embed (A f))).symm
  norm_num [Complex.mul_re,Complex.sub_re,hn] at hre
  rw [intervalIntegral.integral_of_le hT.le]
  linarith only [hre]
end LowEnergy.FirstCurrentPayer
