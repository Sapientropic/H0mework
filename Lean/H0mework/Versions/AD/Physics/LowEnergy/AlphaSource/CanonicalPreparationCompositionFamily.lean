import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylDecay
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylWeakForm
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumRemainder
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumWeylDomain
open CanonicalPreparationSquareCutoff PreparationActualFactor
open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

-- Physical frequencies are 2π times Mathlib frequencies; their two Jacobians
-- cancel the original (2π)^(-200). The source symbol and its shifts stay fixed.
def compositionIntegrand (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  𝐞 ⟪z,w.1+w.2⟫ •
    (partialFourier (p+(t*Real.pi) • w.2) w.1 *
      partialFourier (p-(t*Real.pi) • w.1) w.2)

def compositionFamily (t : ℝ) (z p : PhysicalMomentum) : ℂ :=
  ∫ w : PhysicalMomentum × PhysicalMomentum,compositionIntegrand t z p w ∂volume.prod volume

def frequencyDecay101 (k : PhysicalMomentum) : ℝ := (1+‖k‖)^(-101 : ℝ)

theorem frequencyDecay101_nonnegative (k : PhysicalMomentum) : 0 ≤ frequencyDecay101 k := by
  unfold frequencyDecay101
  positivity

theorem frequencyDecay101_integrable :
    Integrable frequencyDecay101 (volume : Measure PhysicalMomentum) := by
  have dimension : (Module.finrank ℝ PhysicalMomentum : ℝ)<101 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  exact integrable_one_add_norm (μ := (volume : Measure PhysicalMomentum)) dimension

theorem partialFourier_joint_measurable :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => partialFourier w.1 w.2) := by
  let left : PhysicalMomentum × PhysicalMomentum → PhysicalMomentum :=
    fun w => (2*Real.pi)⁻¹ • w.1+(1/2 : ℝ) • w.2
  let right : PhysicalMomentum × PhysicalMomentum → PhysicalMomentum :=
    fun w => (2*Real.pi)⁻¹ • w.1-(1/2 : ℝ) • w.2
  have leftCont : Continuous left :=
    (continuous_fst.const_smul (2*Real.pi)⁻¹).add (continuous_snd.const_smul (1/2 : ℝ))
  have rightCont : Continuous right :=
    (continuous_fst.const_smul (2*Real.pi)⁻¹).sub (continuous_snd.const_smul (1/2 : ℝ))
  have measurable : Measurable (fun w => (left w,right w)) := (leftCont.prodMk rightCont).measurable
  have same : (fun w : PhysicalMomentum × PhysicalMomentum => partialFourier w.1 w.2)=
      (fun w => weylKernel (left w) (right w)) := by
    ext w
    have sum : left w+right w=(2 : ℝ) • ((2*Real.pi)⁻¹ • w.1) := by
      dsimp [left,right]
      rw [two_smul ℝ]
      abel
    have difference : left w-right w=w.2 := by
      dsimp [left,right]
      rw [show (2*Real.pi)⁻¹ • w.1+(1/2 : ℝ) • w.2-
          ((2*Real.pi)⁻¹ • w.1-(1/2 : ℝ) • w.2)=
          (1/2 : ℝ) • w.2+(1/2 : ℝ) • w.2 by abel,←add_smul]
      norm_num
    have midpoint : physicalMidpoint (left w) (right w)=w.1 := by
      rw [physicalMidpoint,sum,smul_smul,smul_smul]
      have coefficient : Real.pi*2*(2*Real.pi)⁻¹=1 := by
        field_simp [Real.pi_ne_zero]
      rw [coefficient,one_smul]
    rw [weylKernel,midpoint,difference]
  rw [same]
  exact kernel_stronglyMeasurable.comp_measurable measurable

theorem compositionIntegrand_measurable (t : ℝ) (z p : PhysicalMomentum) :
    StronglyMeasurable (compositionIntegrand t z p) := by
  have left : Measurable
      (fun w : PhysicalMomentum × PhysicalMomentum => (p+(t*Real.pi) • w.2,w.1)) :=
    ((continuous_const.add (continuous_snd.const_smul (t*Real.pi))).prodMk continuous_fst).measurable
  have right : Measurable
      (fun w : PhysicalMomentum × PhysicalMomentum => (p-(t*Real.pi) • w.1,w.2)) :=
    ((continuous_const.sub (continuous_fst.const_smul (t*Real.pi))).prodMk continuous_snd).measurable
  have phase : Continuous (fun w : PhysicalMomentum × PhysicalMomentum => ⟪z,w.1+w.2⟫) :=
    continuous_const.inner (continuous_fst.add continuous_snd)
  exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)).stronglyMeasurable.smul
    ((partialFourier_joint_measurable.comp_measurable left).mul
      (partialFourier_joint_measurable.comp_measurable right))

def sourceCompositionBound (p : PhysicalMomentum) : ℝ :=
  (sourceRapidBound*(‖p‖+Real.pi))^2

theorem sourceCompositionBound_nonnegative (p : PhysicalMomentum) : 0 ≤ sourceCompositionBound p :=
  sq_nonneg _

def compositionMajorant (p : PhysicalMomentum) (w : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  sourceCompositionBound p*(frequencyDecay101 w.1*frequencyDecay101 w.2)

theorem compositionMajorant_integrable (p : PhysicalMomentum) :
    Integrable (compositionMajorant p) (volume.prod volume) :=
  (frequencyDecay101_integrable.mul_prod frequencyDecay101_integrable).const_mul _

theorem shifted_momentum_bound (t : ℝ) (p k : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    ‖p+(t*Real.pi) • k‖ ≤ (‖p‖+Real.pi)*(1+‖k‖) := by
  have coeff : |t*Real.pi| ≤ Real.pi := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    simpa using mul_le_mul_of_nonneg_right unitInterval Real.pi_pos.le
  have triangle : ‖p+(t*Real.pi) • k‖ ≤ ‖p‖+Real.pi*‖k‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    gcongr
  apply triangle.trans
  nlinarith [Real.pi_pos,norm_nonneg p,norm_nonneg k,mul_nonneg (norm_nonneg p) (norm_nonneg k)]

theorem compositionIntegrand_weighted_bound (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    ((1+‖w.1‖)^101*(1+‖w.2‖)^101)*‖compositionIntegrand t z p w‖ ≤ sourceCompositionBound p := by
  have left := (partialFourier_rapid_bound (p+(t*Real.pi) • w.2) w.1).trans
    (mul_le_mul_of_nonneg_left (shifted_momentum_bound t p w.2 unitInterval) sourceRapidBound_nonnegative)
  have negInterval : |-t| ≤ 1 := by simpa only [abs_neg] using unitInterval
  have shiftRight : ‖p-(t*Real.pi) • w.1‖ ≤ (‖p‖+Real.pi)*(1+‖w.1‖) := by
    simpa only [neg_mul,neg_smul,sub_eq_add_neg] using shifted_momentum_bound (-t) p w.1 negInterval
  have right := (partialFourier_rapid_bound (p-(t*Real.pi) • w.1) w.2).trans
    (mul_le_mul_of_nonneg_left shiftRight sourceRapidBound_nonnegative)
  have combined := mul_le_mul left right (mul_nonneg (by positivity) (norm_nonneg _))
    (mul_nonneg sourceRapidBound_nonnegative (by positivity))
  have product : ((1+‖w.1‖)*(1+‖w.2‖))*
      (((1+‖w.1‖)^101*(1+‖w.2‖)^101)*‖compositionIntegrand t z p w‖) ≤
      ((1+‖w.1‖)*(1+‖w.2‖))*sourceCompositionBound p := by
    calc
      _ = ((1+‖w.1‖)^102*‖partialFourier (p+(t*Real.pi) • w.2) w.1‖)*
          ((1+‖w.2‖)^102*‖partialFourier (p-(t*Real.pi) • w.1) w.2‖) := by
        simp only [compositionIntegrand,Circle.norm_smul,norm_mul]
        rw [show (1+‖w.1‖)^102=(1+‖w.1‖)^101*(1+‖w.1‖) from pow_succ _ 101,
          show (1+‖w.2‖)^102=(1+‖w.2‖)^101*(1+‖w.2‖) from pow_succ _ 101]
        ac_rfl
      _ ≤ (sourceRapidBound*((‖p‖+Real.pi)*(1+‖w.2‖)))*
          (sourceRapidBound*((‖p‖+Real.pi)*(1+‖w.1‖))) := combined
      _ = _ := by rw [sourceCompositionBound]; ring
  exact (mul_le_mul_iff_right₀ (by positivity : 0<(1+‖w.1‖)*(1+‖w.2‖))).mp product

theorem compositionIntegrand_norm_bound (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    ‖compositionIntegrand t z p w‖ ≤ compositionMajorant p w := by
  rw [compositionMajorant,frequencyDecay101,frequencyDecay101,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+‖w.1‖),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+‖w.2‖)]
  have pow1 : (1+‖w.1‖)^(101 : ℝ)=(1+‖w.1‖)^(101 : ℕ) := Real.rpow_natCast _ _
  have pow2 : (1+‖w.2‖)^(101 : ℝ)=(1+‖w.2‖)^(101 : ℕ) := Real.rpow_natCast _ _
  rw [pow1,pow2,←mul_inv,←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using compositionIntegrand_weighted_bound t z p w unitInterval

theorem compositionIntegrand_integrable (t : ℝ) (z p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    Integrable (compositionIntegrand t z p) (volume.prod volume) :=
  (compositionMajorant_integrable p).mono (compositionIntegrand_measurable t z p).aestronglyMeasurable
    (Eventually.of_forall (fun w => (compositionIntegrand_norm_bound t z p w unitInterval).trans (le_abs_self _)))

theorem compositionFamily_norm_bound (t : ℝ) (z p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    ‖compositionFamily t z p‖ ≤ sourceCompositionBound p*(∫ k : PhysicalMomentum,frequencyDecay101 k)^2 := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ w : PhysicalMomentum × PhysicalMomentum,compositionMajorant p w ∂volume.prod volume :=
      integral_mono (compositionIntegrand_integrable t z p unitInterval).norm (compositionMajorant_integrable p)
        (fun w => compositionIntegrand_norm_bound t z p w unitInterval)
    _ = _ := by
      change (∫ w : PhysicalMomentum × PhysicalMomentum,
        sourceCompositionBound p*(frequencyDecay101 w.1*frequencyDecay101 w.2) ∂volume.prod volume)=_
      rw [integral_const_mul,integral_prod_mul]
      simp only [pow_two]

end LowEnergy.PreparationVacuumRemainder
