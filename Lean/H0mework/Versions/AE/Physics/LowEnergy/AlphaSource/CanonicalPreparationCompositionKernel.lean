import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionPhysical
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumRemainder
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumWeylDomain
open CanonicalPreparationSquareCutoff PreparationActualFactor MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

theorem frequencyDecay101_le_one (k : PhysicalMomentum) : frequencyDecay101 k ≤ 1 := by
  unfold frequencyDecay101
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+‖k‖)]
  apply inv_le_one_of_one_le₀
  exact Real.one_le_rpow (by linarith [norm_nonneg k]) (by norm_num)

theorem original_kernel_decay101 (xi eta : PhysicalMomentum) :
    ‖weylKernel xi eta‖ ≤ 2*Real.pi*sourceRapidBound*(1+‖eta‖)*frequencyDecay101 (xi-eta) := by
  have rapid : (1+‖xi-eta‖)^102*‖weylKernel xi eta‖ ≤ sourceRapidBound*‖physicalMidpoint xi eta‖ := by
    simpa only [weylKernel] using partialFourier_rapid_bound (physicalMidpoint xi eta) (xi-eta)
  have total := rapid.trans
    (mul_le_mul_of_nonneg_left (original_midpoint_growth xi eta) sourceRapidBound_nonnegative)
  have rearranged : (1+‖xi-eta‖)*((1+‖xi-eta‖)^101*‖weylKernel xi eta‖) ≤
      (1+‖xi-eta‖)*(2*Real.pi*sourceRapidBound*(1+‖eta‖)) := by
    calc
      _ = (1+‖xi-eta‖)^102*‖weylKernel xi eta‖ := by
        rw [show (1+‖xi-eta‖)^102=(1+‖xi-eta‖)^101*(1+‖xi-eta‖) from pow_succ _ 101]
        ac_rfl
      _ ≤ sourceRapidBound*(2*Real.pi*(1+‖xi-eta‖)*(1+‖eta‖)) := total
      _ = _ := by ring
  have bound := (mul_le_mul_iff_right₀ (by positivity : 0<1+‖xi-eta‖)).mp rearranged
  rw [frequencyDecay101,Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+‖xi-eta‖)]
  have power : (1+‖xi-eta‖)^(101 : ℝ)=(1+‖xi-eta‖)^(101 : ℕ) := Real.rpow_natCast _ _
  rw [power,←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using bound

def actualProductIntegrand (xi eta nu : PhysicalMomentum) : ℂ :=
  weylKernel xi nu*weylKernel nu eta

def sourceProductKernelBound (xi eta : PhysicalMomentum) : ℝ :=
  (2*Real.pi*sourceRapidBound)^2*(1+‖xi‖)*(1+‖eta‖)

theorem sourceProductKernelBound_nonnegative (xi eta : PhysicalMomentum) :
    0 ≤ sourceProductKernelBound xi eta := by
  unfold sourceProductKernelBound
  positivity

theorem actualProductIntegrand_norm_bound (xi eta nu : PhysicalMomentum) :
    ‖actualProductIntegrand xi eta nu‖ ≤ sourceProductKernelBound xi eta*frequencyDecay101 (nu-xi) := by
  have left : ‖weylKernel xi nu‖ ≤
      2*Real.pi*sourceRapidBound*(1+‖xi‖)*frequencyDecay101 (nu-xi) := by
    have same : ‖weylKernel xi nu‖=‖weylKernel nu xi‖ := by
      rw [←weylKernel_hermitian xi nu,Complex.norm_conj]
    rw [same]
    exact original_kernel_decay101 nu xi
  have right : ‖weylKernel nu eta‖ ≤ 2*Real.pi*sourceRapidBound*(1+‖eta‖) :=
    (original_kernel_decay101 nu eta).trans
      (mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (by positivity) sourceRapidBound_nonnegative) (by positivity))
        (frequencyDecay101_le_one _))
  have multiplied := mul_le_mul left right (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) sourceRapidBound_nonnegative) (by positivity))
      (frequencyDecay101_nonnegative _))
  simpa only [actualProductIntegrand,norm_mul,sourceProductKernelBound,pow_two,mul_assoc,
    mul_left_comm,mul_comm] using multiplied

theorem actualProductIntegrand_measurable (xi eta : PhysicalMomentum) :
    StronglyMeasurable (actualProductIntegrand xi eta) :=
  (kernel_stronglyMeasurable.comp_measurable (by fun_prop : Measurable
    (fun nu : PhysicalMomentum => (xi,nu)))).mul
    (kernel_stronglyMeasurable.comp_measurable (by fun_prop : Measurable
      (fun nu : PhysicalMomentum => (nu,eta))))

theorem actualProductIntegrand_integrable (xi eta : PhysicalMomentum) :
    Integrable (actualProductIntegrand xi eta) (volume : Measure PhysicalMomentum) :=
  ((frequencyDecay101_integrable.comp_sub_right xi).const_mul (sourceProductKernelBound xi eta)).mono
    (actualProductIntegrand_measurable xi eta).aestronglyMeasurable
    (Eventually.of_forall (fun nu => (actualProductIntegrand_norm_bound xi eta nu).trans (le_abs_self _)))

-- This is the complete original kernel product, before any Taylor expansion.
def actualProductKernel (xi eta : PhysicalMomentum) : ℂ :=
  ∫ nu : PhysicalMomentum,actualProductIntegrand xi eta nu

theorem actualProductKernel_hermitian (xi eta : PhysicalMomentum) :
    conj (actualProductKernel eta xi)=actualProductKernel xi eta := by
  rw [actualProductKernel,←integral_conj]
  apply integral_congr_ae
  filter_upwards with nu
  simp only [actualProductIntegrand,map_mul,weylKernel_hermitian,mul_comm]

theorem actualProductKernel_norm_bound (xi eta : PhysicalMomentum) :
    ‖actualProductKernel xi eta‖ ≤
      sourceProductKernelBound xi eta*(∫ k : PhysicalMomentum,frequencyDecay101 k) := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ nu : PhysicalMomentum,sourceProductKernelBound xi eta*frequencyDecay101 (nu-xi) :=
      integral_mono (actualProductIntegrand_integrable xi eta).norm
        ((frequencyDecay101_integrable.comp_sub_right xi).const_mul _)
        (actualProductIntegrand_norm_bound xi eta)
    _ = _ := by rw [integral_const_mul,integral_sub_right_eq_self]

def originalPrincipalSquareSlice (p : PhysicalMomentum) : 𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (sourceSchwartzSlice p) (sourceSchwartzSlice p)

theorem originalPrincipalSquareSlice_apply (p x : PhysicalMomentum) :
    originalPrincipalSquareSlice p x=(symbolSlice p x)^2 := by
  rw [originalPrincipalSquareSlice,SchwartzMap.smulLeftCLM_apply_apply (sourceSchwartzSlice p).hasTemperateGrowth]
  simp only [sourceSchwartzSlice_apply,smul_eq_mul,pow_two]

def originalPrincipalSquareKernel (xi eta : PhysicalMomentum) : ℂ :=
  𝓕 (originalPrincipalSquareSlice (physicalMidpoint xi eta)) (xi-eta)

theorem originalPrincipalSquareKernel_literal (xi eta : PhysicalMomentum) :
    originalPrincipalSquareKernel xi eta=
      ∫ x : PhysicalMomentum,𝐞 (-⟪x,xi-eta⟫) •
        (b1 (flatPosition x,physicalMidpoint xi eta) : ℂ)^2 := by
  rw [originalPrincipalSquareKernel,SchwartzMap.fourier_coe,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [originalPrincipalSquareSlice_apply,symbolSlice]

theorem originalPrincipalSquareKernel_integrable (xi eta : PhysicalMomentum) :
    Integrable (fun x : PhysicalMomentum => 𝐞 (-⟪x,xi-eta⟫) •
      (b1 (flatPosition x,physicalMidpoint xi eta) : ℂ)^2) := by
  have genuine : Integrable (fun x : PhysicalMomentum => 𝐞 (-⟪x,xi-eta⟫) •
      originalPrincipalSquareSlice (physicalMidpoint xi eta) x) :=
    (Real.fourierIntegral_convergent_iff (xi-eta)).mpr
    (originalPrincipalSquareSlice (physicalMidpoint xi eta)).integrable
  apply genuine.congr
  filter_upwards with x
  simp only [originalPrincipalSquareSlice_apply,symbolSlice]

theorem originalPrincipalSquareKernel_hermitian (xi eta : PhysicalMomentum) :
    conj (originalPrincipalSquareKernel eta xi)=originalPrincipalSquareKernel xi eta := by
  rw [originalPrincipalSquareKernel_literal,originalPrincipalSquareKernel_literal,←integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def,smul_eq_mul,map_mul,map_pow,Circle.starRingEnd_addChar,
    Complex.conj_ofReal,physicalMidpoint,add_comm eta xi,
    show eta-xi=-(xi-eta) by abel,inner_neg_right,neg_neg]

def actualFullCompositionKernelDefect (xi eta : PhysicalMomentum) : ℂ :=
  actualProductKernel xi eta-originalPrincipalSquareKernel xi eta

theorem actualFullCompositionKernelDefect_hermitian (xi eta : PhysicalMomentum) :
    conj (actualFullCompositionKernelDefect eta xi)=actualFullCompositionKernelDefect xi eta := by
  simp only [actualFullCompositionKernelDefect,map_sub,actualProductKernel_hermitian,
    originalPrincipalSquareKernel_hermitian]

end LowEnergy.PreparationVacuumRemainder
