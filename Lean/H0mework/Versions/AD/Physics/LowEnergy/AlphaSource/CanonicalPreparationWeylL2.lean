import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylDecay
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylOperator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDecay
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumWeylOperator
open CanonicalPreparationSquareCutoff GaussDensityCore
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ENNReal BigOperators

theorem original_midpoint_growth (xi eta : PhysicalMomentum) :
    ‖physicalMidpoint xi eta‖≤2*Real.pi*(1+‖xi-eta‖)*(1+‖eta‖) := by
  rw [physicalMidpoint,norm_smul,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have triangle : ‖xi+eta‖≤‖xi-eta‖+2*‖eta‖ := by
    have same : xi+eta=(xi-eta)+(eta+eta) := by abel
    rw [same]
    exact (norm_add_le _ _).trans (by nlinarith [norm_add_le eta eta])
  have radius : ‖xi-eta‖+2*‖eta‖≤2*(1+‖xi-eta‖)*(1+‖eta‖) := by
    nlinarith [norm_nonneg (xi-eta),norm_nonneg eta,mul_nonneg (norm_nonneg (xi-eta)) (norm_nonneg eta)]
  exact (mul_le_mul_of_nonneg_left (triangle.trans radius) Real.pi_pos.le).trans_eq (by ring)

theorem frequency_peetre (xi eta : PhysicalMomentum) :
    1+‖xi‖≤(1+‖xi-eta‖)*(1+‖eta‖) := by
  have triangle : ‖xi‖≤‖xi-eta‖+‖eta‖ := by
    convert norm_add_le (xi-eta) eta using 1; simp
  nlinarith [mul_nonneg (norm_nonneg (xi-eta)) (norm_nonneg eta)]

theorem weighted_kernel_bound (xi eta : PhysicalMomentum) :
    (1+‖xi‖)^51*‖weylKernel xi eta‖≤2*Real.pi*sourceRapidBound*(1+‖eta‖)^52 := by
  have rapid := partialFourier_rapid_bound (physicalMidpoint xi eta) (xi-eta)
  change (1+‖xi-eta‖)^102*‖weylKernel xi eta‖≤ sourceRapidBound*‖physicalMidpoint xi eta‖ at rapid
  have rpos : 0<1+‖xi-eta‖ := by positivity
  have hundredone : (1+‖xi-eta‖)^101*‖weylKernel xi eta‖≤
      2*Real.pi*sourceRapidBound*(1+‖eta‖) := by
    have midpoint := mul_le_mul_of_nonneg_left (original_midpoint_growth xi eta) sourceRapidBound_nonnegative
    have total := rapid.trans midpoint
    have rearranged : (1+‖xi-eta‖)*((1+‖xi-eta‖)^101*‖weylKernel xi eta‖)≤
        (1+‖xi-eta‖)*(2*Real.pi*sourceRapidBound*(1+‖eta‖)) := by
      calc
        _ = (1+‖xi-eta‖)^102*‖weylKernel xi eta‖ := by ring
        _ ≤ sourceRapidBound*(2*Real.pi*(1+‖xi-eta‖)*(1+‖eta‖)) := total
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ rpos).mp rearranged
  have small : (1+‖xi-eta‖)^51≤(1+‖xi-eta‖)^101 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg (xi-eta)]) (by norm_num)
  have peetre : (1+‖xi‖)^51≤(1+‖xi-eta‖)^51*(1+‖eta‖)^51 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) (frequency_peetre xi eta) 51
  calc
    _ ≤ ((1+‖xi-eta‖)^51*(1+‖eta‖)^51)*‖weylKernel xi eta‖ :=
      mul_le_mul_of_nonneg_right peetre (norm_nonneg _)
    _ ≤ ((1+‖xi-eta‖)^101*(1+‖eta‖)^51)*‖weylKernel xi eta‖ := by
      gcongr
    _ = (1+‖eta‖)^51*((1+‖xi-eta‖)^101*‖weylKernel xi eta‖) := by ring
    _ ≤ (1+‖eta‖)^51*(2*Real.pi*sourceRapidBound*(1+‖eta‖)) :=
      mul_le_mul_of_nonneg_left hundredone (by positivity)
    _ = _ := by ring

def inputMoment52 (f : 𝓢(PhysicalMomentum,ℂ)) : ℝ :=
  ∫ eta : PhysicalMomentum,(1+‖eta‖)^52*‖f eta‖

theorem inputMoment52_integrable (f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun eta : PhysicalMomentum => (1+‖eta‖)^52*‖f eta‖) := by
  have integrable : Integrable (fun eta : PhysicalMomentum => 2^51*(‖f eta‖+‖eta‖^52*‖f eta‖)) :=
    (f.integrable.norm.add (f.integrable_pow_mul volume 52)).const_mul _
  have measured : AEStronglyMeasurable
      (fun eta : PhysicalMomentum => (1+‖eta‖)^52*‖f eta‖) volume := by fun_prop
  apply integrable.mono measured
  filter_upwards with eta
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have bound := mul_le_mul_of_nonneg_right
    (add_pow_le (by norm_num : (0 : ℝ)≤1) (norm_nonneg eta) 52) (norm_nonneg (f eta))
  simp only [one_pow] at bound
  exact bound.trans_eq (by ring)

theorem inputMoment52_nonnegative (f : 𝓢(PhysicalMomentum,ℂ)) : 0 ≤ inputMoment52 f :=
  integral_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))

def sourceL2OutputBound (f : 𝓢(PhysicalMomentum,ℂ)) : ℝ :=
  2*Real.pi*sourceRapidBound*inputMoment52 f

theorem sourceL2OutputBound_nonnegative (f : 𝓢(PhysicalMomentum,ℂ)) : 0≤ sourceL2OutputBound f :=
  mul_nonneg (mul_nonneg (by positivity) sourceRapidBound_nonnegative) (inputMoment52_nonnegative f)

theorem fourierAction_weighted_bound (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    (1+‖xi‖)^51*‖fourierAction f xi‖≤ sourceL2OutputBound f := by
  have integrable : Integrable (fun eta : PhysicalMomentum => (1+‖xi‖)^51*‖weylKernel xi eta*f eta‖) :=
    (kernel_test_integrable f xi).norm.const_mul _
  calc
    _ ≤ (1+‖xi‖)^51*(∫ eta : PhysicalMomentum,‖weylKernel xi eta*f eta‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ eta : PhysicalMomentum,(1+‖xi‖)^51*‖weylKernel xi eta*f eta‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ eta : PhysicalMomentum,(2*Real.pi*sourceRapidBound)*((1+‖eta‖)^52*‖f eta‖) := by
      apply integral_mono integrable ((inputMoment52_integrable f).const_mul _)
      intro eta
      change (1+‖xi‖)^51*‖weylKernel xi eta*f eta‖≤
        (2*Real.pi*sourceRapidBound)*((1+‖eta‖)^52*‖f eta‖)
      rw [norm_mul]
      have bound := mul_le_mul_of_nonneg_right (weighted_kernel_bound xi eta) (norm_nonneg (f eta))
      simpa only [mul_assoc] using bound
    _ = sourceL2OutputBound f := by rw [integral_const_mul]; rfl

def decay51 (xi : PhysicalMomentum) : ℝ := (1+‖xi‖)^(-51 : ℝ)

theorem decay51_memLp : MemLp decay51 2 (volume : Measure PhysicalMomentum) := by
  have base : Continuous (fun xi : PhysicalMomentum => (1+‖xi‖ : ℝ)) :=
    continuous_const.add continuous_norm
  have continuous : Continuous decay51 :=
    base.rpow_const (fun xi => Or.inl (by positivity : (1+‖xi‖ : ℝ)≠0))
  apply (memLp_two_iff_integrable_sq continuous.aestronglyMeasurable).mpr
  have dimension : (Module.finrank ℝ PhysicalMomentum : ℝ)<102 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have integrable := integrable_one_add_norm (μ := (volume : Measure PhysicalMomentum)) dimension
  apply integrable.congr
  filter_upwards with xi
  change (1+‖xi‖)^(-102 : ℝ)=((1+‖xi‖)^(-51 : ℝ))^2
  rw [←Real.rpow_mul_natCast (by positivity : (0 : ℝ)≤1+‖xi‖) (-51) 2]
  norm_num

theorem fourierAction_decay51 (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    ‖fourierAction f xi‖≤ sourceL2OutputBound f*decay51 xi := by
  rw [decay51,Real.rpow_neg (by positivity)]
  have castPower : (1+‖xi‖)^(51 : ℝ)=(1+‖xi‖)^(51 : ℕ) := Real.rpow_natCast _ _
  rw [castPower,←div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using fourierAction_weighted_bound f xi

theorem fourierAction_memLp (f : 𝓢(PhysicalMomentum,ℂ)) :
    MemLp (fourierAction f) 2 (volume : Measure PhysicalMomentum) :=
  (decay51_memLp.const_mul (sourceL2OutputBound f)).mono'
    (fourierAction_measurable f).aestronglyMeasurable
      (Eventually.of_forall (fourierAction_decay51 f))

def fourierActionLp (f : 𝓢(PhysicalMomentum,ℂ)) : FourierHilbert :=
  (fourierAction_memLp f).toLp (fourierAction f)

theorem fourierActionLp_readback (f : 𝓢(PhysicalMomentum,ℂ)) :
    fourierActionLp f=ᵐ[volume] fourierAction f := (fourierAction_memLp f).coeFn_toLp

theorem fourierActionLp_tempered_readback (f : 𝓢(PhysicalMomentum,ℂ)) :
    Lp.toTemperedDistribution (fourierActionLp f)=temperedAction f := by
  ext g
  rw [Lp.toTemperedDistribution_apply,temperedAction_readback]
  apply integral_congr_ae
  filter_upwards [fourierActionLp_readback f] with xi hxi
  simp only [hxi,smul_eq_mul]

def fourierActionLpLinear : 𝓢(PhysicalMomentum,ℂ) →ₗ[ℂ] FourierHilbert where
  toFun := fourierActionLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fourierActionLp_readback (f+g),fourierActionLp_readback f,
      fourierActionLp_readback g,Lp.coeFn_add (fourierActionLp f) (fourierActionLp g)]
      with xi hsum hf hg hout
    rw [hsum,hout]
    simp only [Pi.add_apply]
    rw [hf,hg,fourierAction_add]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [fourierActionLp_readback (c • f),fourierActionLp_readback f,
      Lp.coeFn_smul c (fourierActionLp f)] with xi hc hf hout
    simp only [RingHom.id_apply]
    rw [hc,hout]
    simp only [Pi.smul_apply]
    rw [hf,fourierAction_smul]
    rfl

def actualVacuumWeylL2 : ScalarTest →ₗ[ℂ] FourierHilbert :=
  (Lp.fourierTransformₗᵢ PhysicalMomentum ℂ).symm.toLinearMap.comp
    (fourierActionLpLinear.comp sourceVacuumFrequencyLinear)

theorem actualVacuumWeylL2_readback (f : ScalarTest) :
    Lp.toTemperedDistribution (actualVacuumWeylL2 f)=actualVacuumWeyl f := by
  change Lp.toTemperedDistribution (𝓕⁻ (fourierActionLp (sourceVacuumInputFrequency f)))= _
  rw [←Lp.fourierInv_toTemperedDistribution_eq,fourierActionLp_tempered_readback]
  rfl

end LowEnergy.PreparationVacuumWeylDecay
