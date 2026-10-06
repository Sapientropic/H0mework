import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionKernelReadback
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionReadback
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder
open PreparationActualFactor CanonicalPreparationSquareCutoff MeasureTheory Filter
open CanonicalPreparationCutoff
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap ENNReal
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

def phaseFrequencyProduct (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  𝐞 ⟪z,w.2⟫ • frequencyProductIntegrand t p w

theorem phaseFrequencyProduct_shear (t : ℝ) (z p : PhysicalMomentum) :
    phaseFrequencyProduct t z p=
      compositionIntegrand t z p ∘ (fun w : PhysicalMomentum × PhysicalMomentum => (w.1,w.2-w.1)) := by
  funext w
  simp only [phaseFrequencyProduct,frequencyProductIntegrand,compositionIntegrand,
    Function.comp_apply,show w.1+(w.2-w.1)=w.2 by abel]

theorem phaseFrequencyProduct_integrable (t : ℝ) (z p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) : Integrable (phaseFrequencyProduct t z p) (volume.prod volume) := by
  rw [phaseFrequencyProduct_shear]
  exact (measurePreserving_prod_sub (volume : Measure PhysicalMomentum) volume).integrable_comp_of_integrable
    (compositionIntegrand_integrable t z p unitInterval)

theorem compositionFamily_inverseFrequency (t : ℝ) (z p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) :
    compositionFamily t z p=𝓕⁻ (compositionFrequency t p) z := by
  have shear := (measurePreserving_prod_sub (volume : Measure PhysicalMomentum) volume).integral_comp
    (MeasurableEquiv.shearSubRight PhysicalMomentum).measurableEmbedding (compositionIntegrand t z p)
  calc
    _ = ∫ w : PhysicalMomentum × PhysicalMomentum,phaseFrequencyProduct t z p w ∂volume.prod volume := by
      rw [phaseFrequencyProduct_shear,compositionFamily]
      exact shear.symm
    _ = ∫ k : PhysicalMomentum,∫ q : PhysicalMomentum,phaseFrequencyProduct t z p (q,k) :=
      integral_prod_symm _ (phaseFrequencyProduct_integrable t z p unitInterval)
    _ = ∫ k : PhysicalMomentum,𝐞 ⟪z,k⟫ • compositionFrequency t p k := by
      apply integral_congr_ae
      filter_upwards with k
      simp only [phaseFrequencyProduct,compositionFrequency,Circle.smul_def,smul_eq_mul]
      exact integral_const_mul _ _
    _ = _ := by
      rw [Real.fourierInv_eq]
      simp only [real_inner_comm z]

def principalFrequency (p : PhysicalMomentum) : 𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕 (sourceSchwartzSlice p)) (𝓕 (sourceSchwartzSlice p))

theorem principalFrequency_readback (p k : PhysicalMomentum) :
    principalFrequency p k=compositionFrequency 0 p k := by
  rw [principalFrequency,SchwartzMap.convolution_apply,compositionFrequency]
  change (∫ q : PhysicalMomentum,(𝓕 (sourceSchwartzSlice p) : 𝓢(PhysicalMomentum,ℂ)) q *
      (𝓕 (sourceSchwartzSlice p) : 𝓢(PhysicalMomentum,ℂ)) (k-q))=
    ∫ q : PhysicalMomentum,frequencyProductIntegrand 0 p (q,k)
  apply integral_congr_ae
  filter_upwards with q
  simp only [frequencyProductIntegrand,zero_mul,zero_smul,add_zero,sub_zero,
    sourceSchwartzSlice_fourier]

theorem compositionFrequency_zero_fourier_integrable (p : PhysicalMomentum) :
    Integrable (𝓕 (compositionFrequency 0 p)) := by
  have same : (principalFrequency p : PhysicalMomentum → ℂ)=compositionFrequency 0 p :=
    funext (principalFrequency_readback p)
  rw [←same,←SchwartzMap.fourier_coe]
  exact (𝓕 (principalFrequency p) : 𝓢(PhysicalMomentum,ℂ)).integrable

theorem originalPrincipalSquareKernel_frequency_readback (xi eta : PhysicalMomentum) :
    originalPrincipalSquareKernel xi eta=
      compositionFrequency 0 (physicalMidpoint xi eta) (xi-eta) := by
  let p := physicalMidpoint xi eta
  have inverse : 𝓕⁻ (compositionFrequency 0 p)=
      (originalPrincipalSquareSlice p : PhysicalMomentum → ℂ) := by
    funext x
    rw [←compositionFamily_inverseFrequency 0 x p (by norm_num),compositionFamily_zero,
      originalPrincipalSquareSlice_apply]
  have continuous : Continuous (compositionFrequency 0 p) :=
    (principalFrequency p).continuous.congr (principalFrequency_readback p)
  have inversion := continuous.fourier_fourierInv_eq
    (compositionFrequency_integrable 0 p (by norm_num)) (compositionFrequency_zero_fourier_integrable p)
  rw [inverse] at inversion
  rw [originalPrincipalSquareKernel,SchwartzMap.fourier_coe]
  exact congrArg (fun f : PhysicalMomentum → ℂ => f (xi-eta)) inversion

theorem actualFullCompositionKernelDefect_frequency_readback (xi eta : PhysicalMomentum) :
    actualFullCompositionKernelDefect xi eta=
      compositionFrequency 1 (physicalMidpoint xi eta) (xi-eta)-
      compositionFrequency 0 (physicalMidpoint xi eta) (xi-eta) := by
  rw [actualFullCompositionKernelDefect,actualProductKernel_frequency_readback,
    originalPrincipalSquareKernel_frequency_readback]

def sourceFrequencyDefect (p k : PhysicalMomentum) : ℂ :=
  compositionFrequency 1 p k-compositionFrequency 0 p k

theorem sourceFrequencyDefect_integrable (p : PhysicalMomentum) : Integrable (sourceFrequencyDefect p) :=
  (compositionFrequency_integrable 1 p (by norm_num)).sub
    (compositionFrequency_integrable 0 p (by norm_num))

theorem compositionFrequency_inverse_integrable (t : ℝ) (p z : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) :
    Integrable (fun k : PhysicalMomentum => 𝐞 ⟪k,z⟫ • compositionFrequency t p k) := by
  have genuine := (Real.fourierIntegral_convergent_iff (-z)).mpr
    (compositionFrequency_integrable t p unitInterval)
  simpa only [inner_neg_right,neg_neg] using genuine

theorem sourceFullCompositionDefect_inverseFrequency (z : FlatConfiguration) (p : PhysicalMomentum) :
    sourceFullCompositionDefect z p=𝓕⁻ (sourceFrequencyDefect p) (flatPosition.symm z) := by
  rw [sourceFullCompositionDefect,
    compositionFamily_inverseFrequency 1 _ _ (by norm_num),
    compositionFamily_inverseFrequency 0 _ _ (by norm_num)]
  simp only [Real.fourierInv_eq,sourceFrequencyDefect,smul_sub]
  exact (integral_sub (compositionFrequency_inverse_integrable 1 p _ (by norm_num))
    (compositionFrequency_inverse_integrable 0 p _ (by norm_num))).symm

theorem actualFullCompositionKernelDefect_sourceFrequency (xi eta : PhysicalMomentum) :
    actualFullCompositionKernelDefect xi eta=sourceFrequencyDefect (physicalMidpoint xi eta) (xi-eta) :=
  actualFullCompositionKernelDefect_frequency_readback xi eta

theorem compositionFamily_continuous (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    Continuous (fun z : PhysicalMomentum => compositionFamily t z p) := by
  have continuous : Continuous (𝓕⁻ (compositionFrequency t p)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (show Continuous (fun w : PhysicalMomentum × PhysicalMomentum =>
        (-innerₗ PhysicalMomentum) w.1 w.2) from continuous_inner.neg)
      (compositionFrequency_integrable t p unitInterval)
  exact continuous.congr (fun z => (compositionFamily_inverseFrequency t z p unitInterval).symm)

theorem compositionFamily_memLp_top (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    MemLp (fun z : PhysicalMomentum => compositionFamily t z p) ∞ :=
  memLp_top_of_bound (compositionFamily_continuous t p unitInterval).aestronglyMeasurable
    (sourceCompositionBound p*(∫ k : PhysicalMomentum,frequencyDecay101 k)^2)
    (Eventually.of_forall (fun z => compositionFamily_norm_bound t z p unitInterval))

def compositionFrequencyLp (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    Lp (α := PhysicalMomentum) ℂ 1 :=
  ((memLp_one_iff_integrable).mpr (compositionFrequency_integrable t p unitInterval)).toLp
    (compositionFrequency t p)

def compositionSpaceLp (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    Lp (α := PhysicalMomentum) ℂ ∞ :=
  (compositionFamily_memLp_top t p unitInterval).toLp (fun z => compositionFamily t z p)

def compositionFrequencyDistribution (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    𝓢'(PhysicalMomentum,ℂ) := Lp.toTemperedDistribution (compositionFrequencyLp t p unitInterval)

def compositionSpaceDistribution (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1) :
    𝓢'(PhysicalMomentum,ℂ) := Lp.toTemperedDistribution (compositionSpaceLp t p unitInterval)

theorem compositionFrequencyDistribution_readback (t : ℝ) (p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) (test : 𝓢(PhysicalMomentum,ℂ)) :
    compositionFrequencyDistribution t p unitInterval test=
      ∫ k : PhysicalMomentum,test k • compositionFrequency t p k := by
  rw [compositionFrequencyDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [((memLp_one_iff_integrable).mpr
    (compositionFrequency_integrable t p unitInterval)).coeFn_toLp] with k hk
  rw [compositionFrequencyLp,hk]

theorem compositionSpaceDistribution_readback (t : ℝ) (p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) (test : 𝓢(PhysicalMomentum,ℂ)) :
    compositionSpaceDistribution t p unitInterval test=
      ∫ z : PhysicalMomentum,test z • compositionFamily t z p := by
  rw [compositionSpaceDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(compositionFamily_memLp_top t p unitInterval).coeFn_toLp] with z hz
  rw [compositionSpaceLp,hz]

theorem composition_inverse_pairing (t : ℝ) (p : PhysicalMomentum) (unitInterval : |t| ≤ 1)
    (test : 𝓢(PhysicalMomentum,ℂ)) :
    (∫ k : PhysicalMomentum,(𝓕⁻ (test : PhysicalMomentum → ℂ)) k • compositionFrequency t p k)=
      ∫ z : PhysicalMomentum,test z • compositionFamily t z p := by
  have pairing := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure PhysicalMomentum)) (ν := (volume : Measure PhysicalMomentum))
    (L := -(innerₗ PhysicalMomentum)) Real.continuous_fourierChar
    (show Continuous (fun w : PhysicalMomentum × PhysicalMomentum =>
      (-innerₗ PhysicalMomentum) w.1 w.2) from continuous_inner.neg)
    test.integrable (compositionFrequency_integrable t p unitInterval)
  have flip : (-(innerₗ PhysicalMomentum)).flip=-(innerₗ PhysicalMomentum) := by
    ext x y
    change -⟪y,x⟫ = -⟪x,y⟫
    rw [real_inner_comm y x]
  rw [flip] at pairing
  change (∫ k : PhysicalMomentum,(𝓕⁻ (test : PhysicalMomentum → ℂ)) k • compositionFrequency t p k)=
    ∫ z : PhysicalMomentum,test z • (𝓕⁻ (compositionFrequency t p)) z at pairing
  rw [pairing]
  apply integral_congr_ae
  filter_upwards with z
  rw [compositionFamily_inverseFrequency t z p unitInterval]

theorem compositionSpaceDistribution_inverseFrequency (t : ℝ) (p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) :
    compositionSpaceDistribution t p unitInterval=𝓕⁻ (compositionFrequencyDistribution t p unitInterval) := by
  ext test
  rw [compositionSpaceDistribution_readback,TemperedDistribution.fourierInv_apply,
    compositionFrequencyDistribution_readback]
  simp only [SchwartzMap.fourierInv_coe]
  exact (composition_inverse_pairing t p unitInterval test).symm

end LowEnergy.PreparationVacuumCompositionReadback
