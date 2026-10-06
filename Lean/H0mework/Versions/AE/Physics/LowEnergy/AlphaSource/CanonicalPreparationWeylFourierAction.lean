import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylInput

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOperator
open PreparationVacuumWeyl PreparationVacuumWeylDomain CanonicalPreparationSquareCutoff
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ComplexConjugate

def zerothMoment (f : 𝓢(PhysicalMomentum,ℂ)) : ℝ := ∫ eta : PhysicalMomentum,‖f eta‖

def firstMoment (f : 𝓢(PhysicalMomentum,ℂ)) : ℝ := ∫ eta : PhysicalMomentum,‖eta‖*‖f eta‖

theorem zerothMoment_nonnegative (f : 𝓢(PhysicalMomentum,ℂ)) : 0≤zerothMoment f :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem firstMoment_nonnegative (f : 𝓢(PhysicalMomentum,ℂ)) : 0≤firstMoment f :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

def actionMajorant (f : 𝓢(PhysicalMomentum,ℂ)) (xi eta : PhysicalMomentum) : ℝ :=
  (sourceKernelBound*Real.pi)*(‖xi‖*‖f eta‖+‖eta‖*‖f eta‖)

theorem actionMajorant_integrable (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    Integrable (actionMajorant f xi) := by
  have wf : Integrable (fun eta : PhysicalMomentum => ‖eta‖*‖f eta‖) := by
    simpa only [pow_one] using f.integrable_pow_mul volume 1
  exact ((f.integrable.norm.const_mul ‖xi‖).add wf).const_mul _

theorem kernel_test_norm (f : 𝓢(PhysicalMomentum,ℂ)) (xi eta : PhysicalMomentum) :
    ‖weylKernel xi eta*f eta‖≤actionMajorant f xi eta := by
  rw [norm_mul]
  calc
    _ ≤ (sourceKernelBound*Real.pi*(‖xi‖+‖eta‖))*‖f eta‖ :=
      mul_le_mul_of_nonneg_right (weylKernel_sum_bound xi eta) (norm_nonneg _)
    _ = _ := by rw [actionMajorant]; ring

theorem kernel_test_integrable (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    Integrable (fun eta : PhysicalMomentum => weylKernel xi eta*f eta) := by
  have measurable : StronglyMeasurable
      (fun eta : PhysicalMomentum => weylKernel xi eta*f eta) :=
    (kernel_stronglyMeasurable.comp_measurable
      (show Measurable (fun eta : PhysicalMomentum => (xi,eta)) from by fun_prop)).mul
        f.continuous.stronglyMeasurable
  exact (actionMajorant_integrable f xi).mono measurable.aestronglyMeasurable
    (Eventually.of_forall (fun eta => (kernel_test_norm f xi eta).trans (le_abs_self _)))

def fourierAction (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) : ℂ :=
  ∫ eta : PhysicalMomentum,weylKernel xi eta*f eta

theorem fourierAction_measurable (f : 𝓢(PhysicalMomentum,ℂ)) : StronglyMeasurable (fourierAction f) :=
  (kernel_stronglyMeasurable.mul
    (f.continuous.comp continuous_snd).stronglyMeasurable).integral_prod_right

theorem fourierAction_source_growth (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    ‖fourierAction f xi‖ ≤ sourceKernelBound*Real.pi*(‖xi‖*zerothMoment f+firstMoment f) := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ eta : PhysicalMomentum,actionMajorant f xi eta :=
      integral_mono (kernel_test_integrable f xi).norm (actionMajorant_integrable f xi)
        (kernel_test_norm f xi)
    _ = _ := by
      unfold actionMajorant
      rw [integral_const_mul,integral_add (f.integrable.norm.const_mul ‖xi‖)
        (by simpa only [pow_one] using f.integrable_pow_mul volume 1),integral_const_mul]
      rfl

theorem weakWeylForm_actual_action (g f : 𝓢(PhysicalMomentum,ℂ)) :
    weakWeylForm g f=∫ xi : PhysicalMomentum,conj (g xi)*fourierAction f xi := by
  rw [weakWeylForm,integral_prod _ (weakIntegrand_integrable g f)]
  congr 1
  ext xi
  simp only [weakIntegrand,mul_assoc]
  rw [integral_const_mul]
  rfl

theorem fourierAction_add (f g : 𝓢(PhysicalMomentum,ℂ)) :
    fourierAction (f+g)=fourierAction f+fourierAction g := by
  ext xi
  simp only [fourierAction,add_apply,mul_add,Pi.add_apply]
  rw [integral_add (kernel_test_integrable f xi) (kernel_test_integrable g xi)]

theorem fourierAction_smul (c : ℂ) (f : 𝓢(PhysicalMomentum,ℂ)) :
    fourierAction (c • f)=c • fourierAction f := by
  ext xi
  simp only [fourierAction,smul_apply,smul_eq_mul,Pi.smul_apply]
  simp_rw [mul_left_comm (weylKernel xi _) c]
  exact integral_const_mul c _

def actualVacuumFactorAction (f : GaussDensityCore.ScalarTest) : PhysicalMomentum → ℂ :=
  fourierAction (sourceVacuumInputFrequency f)

theorem actualVacuumFactorAction_readback (g : 𝓢(PhysicalMomentum,ℂ))
    (f : GaussDensityCore.ScalarTest) :
    actualVacuumFactorPair g f=∫ xi : PhysicalMomentum,conj (g xi)*actualVacuumFactorAction f xi :=
  weakWeylForm_actual_action _ _

end LowEnergy.PreparationVacuumWeylOperator
