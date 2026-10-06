import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylKernel

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDomain
open PreparationVacuumWeyl CanonicalPreparationSquareCutoff PreparationActualFactor
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform RealInnerProductSpace ComplexConjugate

def weakIntegrand (g f : 𝓢(PhysicalMomentum,ℂ)) (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g w.1)*weylKernel w.1 w.2*f w.2

def weakMajorant (g f : 𝓢(PhysicalMomentum,ℂ)) (w : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  (sourceKernelBound*Real.pi)*
    ((‖w.1‖*‖g w.1‖)*‖f w.2‖+‖g w.1‖*(‖w.2‖*‖f w.2‖))

theorem kernel_stronglyMeasurable :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => weylKernel w.1 w.2) := by
  have cont : Continuous (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
      𝐞 (-inner ℝ w.2 (w.1.1-w.1.2)) •
        symbolSlice (physicalMidpoint w.1.1 w.1.2) w.2) := by
    apply Continuous.smul
    · have phase : Continuous
          (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
            -inner ℝ w.2 (w.1.1-w.1.2)) := by fun_prop
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)
    · unfold symbolSlice physicalMidpoint
      apply Complex.continuous_ofReal.comp
      apply b1_continuous.comp
      exact (flatPosition.continuous.comp continuous_snd).prodMk (by fun_prop)
  exact cont.stronglyMeasurable.integral_prod_right

theorem weylKernel_sum_bound (xi eta : PhysicalMomentum) :
    ‖weylKernel xi eta‖ ≤ sourceKernelBound*Real.pi*(‖xi‖+‖eta‖) := by
  apply (weylKernel_order_one xi eta).trans
  rw [physicalMidpoint,norm_smul,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ sourceKernelBound*(Real.pi*(‖xi‖+‖eta‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_add_le xi eta)
        Real.pi_pos.le) sourceKernelBound_nonnegative
    _ = _ := by ring

theorem weakIntegrand_measurable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    StronglyMeasurable (weakIntegrand g f) :=
  ((Complex.continuous_conj.comp (g.continuous.comp continuous_fst)).stronglyMeasurable.mul
    kernel_stronglyMeasurable).mul
    (f.continuous.comp continuous_snd).stronglyMeasurable

theorem weakMajorant_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (weakMajorant g f) (volume.prod volume) := by
  have wg : Integrable (fun x : PhysicalMomentum => ‖x‖*‖g x‖) := by
    simpa only [pow_one] using g.integrable_pow_mul volume 1
  have wf : Integrable (fun x : PhysicalMomentum => ‖x‖*‖f x‖) := by
    simpa only [pow_one] using f.integrable_pow_mul volume 1
  exact ((wg.mul_prod f.integrable.norm).add (g.integrable.norm.mul_prod wf)).const_mul _

theorem weakIntegrand_norm_bound (g f : 𝓢(PhysicalMomentum,ℂ))
    (w : PhysicalMomentum × PhysicalMomentum) : ‖weakIntegrand g f w‖≤weakMajorant g f w := by
  simp only [weakIntegrand,norm_mul,Complex.norm_conj]
  calc
    _ ≤ ‖g w.1‖*(sourceKernelBound*Real.pi*(‖w.1‖+‖w.2‖))*‖f w.2‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (weylKernel_sum_bound w.1 w.2) (norm_nonneg _)) (norm_nonneg _)
    _ = weakMajorant g f w := by rw [weakMajorant]; ring

theorem weakIntegrand_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (weakIntegrand g f) (volume.prod volume) :=
  (weakMajorant_integrable g f).mono (weakIntegrand_measurable g f).aestronglyMeasurable
    (Eventually.of_forall (fun w => (weakIntegrand_norm_bound g f w).trans (le_abs_self _)))

def weakWeylForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ w : PhysicalMomentum × PhysicalMomentum,weakIntegrand g f w ∂volume.prod volume

theorem weakWeylForm_norm_bound (g f : 𝓢(PhysicalMomentum,ℂ)) :
    ‖weakWeylForm g f‖≤∫ w,weakMajorant g f w ∂volume.prod volume :=
  (norm_integral_le_integral_norm _).trans
    (integral_mono (weakIntegrand_integrable g f).norm (weakMajorant_integrable g f)
      (weakIntegrand_norm_bound g f))

theorem weakWeylForm_add_right (g f h : 𝓢(PhysicalMomentum,ℂ)) :
    weakWeylForm g (f+h)=weakWeylForm g f+weakWeylForm g h := by
  have same : weakIntegrand g (f+h)=weakIntegrand g f+weakIntegrand g h := by
    ext w
    simp [weakIntegrand,mul_add]
  rw [weakWeylForm,same]
  simp only [Pi.add_apply]
  rw [integral_add (weakIntegrand_integrable g f) (weakIntegrand_integrable g h)]
  rfl

theorem weakWeylForm_smul_right (g f : 𝓢(PhysicalMomentum,ℂ)) (c : ℂ) :
    weakWeylForm g (c • f)=c*weakWeylForm g f := by
  have same : weakIntegrand g (c • f)=c • weakIntegrand g f := by
    ext w
    simp [weakIntegrand,mul_left_comm]
  rw [weakWeylForm,same]
  simp only [Pi.smul_apply]
  rw [integral_smul,smul_eq_mul]
  rfl

theorem weakWeylForm_hermitian (g f : 𝓢(PhysicalMomentum,ℂ)) :
    conj (weakWeylForm f g)=weakWeylForm g f := by
  rw [weakWeylForm,←integral_conj]
  have same : (fun w : PhysicalMomentum × PhysicalMomentum => conj (weakIntegrand f g w))=
      (weakIntegrand g f ∘ Prod.swap) := by
    ext w
    simp only [weakIntegrand,Function.comp_apply,Prod.swap,map_mul,
      Complex.conj_conj,weylKernel_hermitian]
    ring
  rw [same]
  change (∫ w : PhysicalMomentum × PhysicalMomentum,
    weakIntegrand g f (Prod.swap w) ∂volume.prod volume)=weakWeylForm g f
  rw [integral_prod_swap]
  rfl

end LowEnergy.PreparationVacuumWeylDomain
