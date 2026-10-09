import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonIntegrability
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource
open PreparationPhysicalChannelRadialJet CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform

private def newtonFlatEquiv : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] PhysicalMomentum :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- The source packet is an actual Schwartz inverse Fourier transform, with its original physical phase. -/
def emInverseSchwartz (test : 𝓢(PhysicalMomentum,ℂ)) : 𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ newtonFlatEquiv.symm
    (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ newtonFlatEquiv test))

theorem em_inverse_schwartz_apply (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emInverseSchwartz test x = emPacket test x := by
  change (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ newtonFlatEquiv test))
    (newtonFlatEquiv.symm x) = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with frequency
  change Complex.exp ((↑(2*Real.pi*inner ℝ (WithLp.toLp 2 frequency) (WithLp.toLp 2 x)))*Complex.I)*
    test frequency = sourceSpatialPhase frequency x*test frequency
  congr 2
  simp only [PiLp.inner_apply,Real.inner_apply,sourceSpatialMomentum,
    Pi.smul_apply,smul_eq_mul]
  push_cast
  rw [Finset.mul_sum]
  ring

private theorem newtonSpatial_nonnegative (k : PhysicalMomentum) : 0 ≤ spatialSquare k := by
  unfold spatialSquare
  positivity

private theorem newtonSpatial_positive (k : PhysicalMomentum) (nonzero : k≠0) :
    0 < spatialSquare k := by
  by_contra h
  have zero : spatialSquare k=0 := le_antisymm (not_lt.mp h) (newtonSpatial_nonnegative k)
  apply nonzero
  ext i
  fin_cases i
  · change k 0=0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 1),sq_nonneg (k 2)]
  · change k 1=0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 2)]
  · change k 2=0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 1)]

/-- The source's previously paid three-dimensional Newton singularity also dominates its spatial 1/r kernel. -/
theorem em_spatial_newton_schwartz_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun k=>‖test k‖/Real.sqrt (spatialSquare k)) := by
  have measurable : Measurable (fun k=>‖test k‖/Real.sqrt (spatialSquare k)) := by
    unfold spatialSquare
    fun_prop
  apply (test.integrable.norm.add (em_newton_schwartz_integrable test)).mono'
    measurable.aestronglyMeasurable
  filter_upwards with k
  have sqr := Real.sq_sqrt (newtonSpatial_nonnegative k)
  have rnn := Real.sqrt_nonneg (spatialSquare k)
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) rnn)]
  by_cases small : Real.sqrt (spatialSquare k) ≤ 1
  · have ar : spatialSquare k ≤ Real.sqrt (spatialSquare k) := by nlinarith
    have compared : ‖test k‖/Real.sqrt (spatialSquare k) ≤ ‖test k‖/spatialSquare k := by
      by_cases zero : spatialSquare k=0
      · simp [zero]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (lt_of_le_of_ne
        (newtonSpatial_nonnegative k) (Ne.symm zero)) ar
    exact le_trans compared (le_add_of_nonneg_left (norm_nonneg _))
  · have rp : 0 < Real.sqrt (spatialSquare k) := by linarith
    have compared : ‖test k‖/Real.sqrt (spatialSquare k) ≤ ‖test k‖ :=
      (div_le_iff₀ rp).mpr (by nlinarith [norm_nonneg (test k)])
    exact le_trans compared (le_add_of_nonneg_right
      (div_nonneg (norm_nonneg _) (newtonSpatial_nonnegative k)))

private def newtonTranslatedTest (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E:=PhysicalMomentum))
    ((emInverseSchwartz test).compSubConstCLM ℂ (-x))

private theorem newtonTranslatedTest_apply (test : 𝓢(PhysicalMomentum,ℂ)) (x y : PhysicalMomentum) :
    newtonTranslatedTest test x y = emPacket test (x-y) := by
  change emInverseSchwartz test (-y-(-x))=emPacket test (x-y)
  rw [show -y-(-x)=x-y by abel,em_inverse_schwartz_apply]

/-- Spatial convolution is paid for the actual source inverse packet, including its origin singularity. -/
theorem em_spatial_newton_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun y=>(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y)) := by
  have measured : Measurable (fun y=>(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y)) := by
    simp only [←newtonTranslatedTest_apply test x]
    unfold spatialSquare
    fun_prop
  have budget:=(em_spatial_newton_schwartz_integrable (newtonTranslatedTest test x)).const_mul (4*Real.pi)⁻¹
  apply budget.mono' measured.aestronglyMeasurable
  filter_upwards with y
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos Real.pi_pos,
    newtonTranslatedTest_apply,mul_inv_rev,div_eq_mul_inv]
  norm_num
  exact le_of_eq (by ring)

private theorem newtonFrequency_radial (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>emNewtonPacket 1 d test x) (𝓝[>] 0) (𝓝 (emNewtonPacket 1 0 test x)) := by
  change Tendsto (fun d : ℝ=>∫frequency,(1:ℂ)*sourceSpatialPhase frequency x*test frequency*
    emNewtonMultiplier 1 d frequency) _ (𝓝 (∫frequency,(1:ℂ)*sourceSpatialPhase frequency x*test frequency*
    emNewtonMultiplier 1 0 frequency))
  simp only [one_mul]
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume)
    (fun frequency=>‖test frequency‖/spatialSquare (sourceSpatialMomentum frequency))
  · exact Eventually.of_forall (fun d=>by
      have measured : Measurable (fun frequency=>sourceSpatialPhase frequency x*test frequency*
          emNewtonMultiplier 1 d frequency) := by
        unfold emNewtonMultiplier sourceSpatialPhase sourceSpatialMomentum spatialSquare
        fun_prop
      exact measured.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro d
    filter_upwards [volume.ae_ne (0:PhysicalMomentum)] with frequency nonzero
    have knz : sourceSpatialMomentum frequency≠0 := by
      intro zero
      rcases smul_eq_zero.mp zero with scalar | origin
      · exact (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos).ne' scalar
      · exact nonzero origin
    have ap:=newtonSpatial_positive _ knz
    have phase : ‖sourceSpatialPhase frequency x‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
    have denominator : ((spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*(1:ℂ)^2)=
        ((spatialSquare (sourceSpatialMomentum frequency)+d^2:ℝ):ℂ) := by push_cast;ring
    simp only [norm_mul,phase,one_mul,emNewtonMultiplier,denominator,norm_inv,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (add_pos_of_pos_of_nonneg ap (sq_nonneg d)),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ ap (le_add_of_nonneg_right (sq_nonneg d))) (norm_nonneg _)
  · exact em_physical_newton_schwartz_integrable test
  · filter_upwards [volume.ae_ne (0:PhysicalMomentum)] with frequency nonzero
    have knz : sourceSpatialMomentum frequency≠0 := by
      intro zero
      rcases smul_eq_zero.mp zero with scalar | origin
      · exact (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos).ne' scalar
      · exact nonzero origin
    have ap:=newtonSpatial_positive _ knz
    have continuous : ContinuousAt (fun d : ℝ=>emNewtonMultiplier 1 d frequency) 0 := by
      unfold emNewtonMultiplier
      apply ContinuousAt.inv₀
      · fun_prop
      · simpa using Complex.ofReal_ne_zero.mpr ap.ne'
    exact tendsto_const_nhds.mul (continuous.tendsto.mono_left nhdsWithin_le_nhds)

private def newtonKernelBudget : ℝ := ‖(paidRadialGreen% greenAmplitude) 1‖*Real.sqrt Real.pi/2

private theorem newtonKernel_bound (d : ℝ) (y : PhysicalMomentum) (positive : 0<spatialSquare y) :
    ‖emRegulatedNewton 1 d y‖ ≤ newtonKernelBudget/Real.sqrt (spatialSquare y) := by
  have realPositive : 0<(1:ℂ).re := by norm_num
  have densityIntegrable:=(paidRadialGreen% greenDensity_integrable) 1 realPositive d y positive
  have gaussianIntegrable:=((integrable_exp_neg_mul_sq positive).const_mul ‖(paidRadialGreen% greenAmplitude) 1‖).integrableOn (s:=Ioi (0:ℝ))
  calc
    _ ≤ ∫u : ℝ in Ioi 0,‖(paidRadialGreen% greenDensity) 1 d u y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫u : ℝ in Ioi 0,‖(paidRadialGreen% greenAmplitude) 1‖*Real.exp (-(spatialSquare y)*u^2) := by
      apply integral_mono_ae densityIntegrable.norm gaussianIntegrable
      exact Eventually.of_forall (fun u=>by simpa using (paidRadialGreen% greenDensity_bound) 1 realPositive d u y)
    _ = newtonKernelBudget/Real.sqrt (spatialSquare y) := by
      rw [integral_const_mul,integral_gaussian_Ioi,Real.sqrt_div Real.pi_pos.le]
      unfold newtonKernelBudget
      ring

private theorem newtonSpace_radial (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>∫y : PhysicalMomentum,emRegulatedNewton 1 d y*emPacket test (x-y))
      (𝓝[>] 0) (𝓝 (∫y : PhysicalMomentum,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*
        emPacket test (x-y))) := by
  have realPositive : 0<(1:ℂ).re := by norm_num
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume)
    (fun y=>newtonKernelBudget*(‖emPacket test (x-y)‖/Real.sqrt (spatialSquare y)))
  · filter_upwards [self_mem_nhdsWithin] with d dp
    have kernel:=(paidRadialGreen% greenKernel_integrable) 1 realPositive d dp
    have packet : Continuous (fun y=>emPacket test (x-y)) := by
      simp only [←newtonTranslatedTest_apply test x]
      exact (newtonTranslatedTest test x).continuous
    exact kernel.aestronglyMeasurable.mul packet.aestronglyMeasurable
  · apply Eventually.of_forall
    intro d
    filter_upwards [volume.ae_ne (0:PhysicalMomentum)] with y nonzero
    rw [norm_mul]
    calc
      _ ≤ (newtonKernelBudget/Real.sqrt (spatialSquare y))*‖emPacket test (x-y)‖ :=
        mul_le_mul_of_nonneg_right (newtonKernel_bound d y (newtonSpatial_positive y nonzero)) (norm_nonneg _)
      _ = _ := by ring
  · simpa only [newtonTranslatedTest_apply] using
      (em_spatial_newton_schwartz_integrable (newtonTranslatedTest test x)).const_mul newtonKernelBudget
  · filter_upwards [volume.ae_ne (0:PhysicalMomentum)] with y nonzero
    have generated:=(paidRadialGreen% greenKernel_limit) 1 realPositive y (newtonSpatial_positive y nonzero)
    rw [(paidRadialGreen% greenKernel_zero) 1 realPositive y (newtonSpatial_positive y nonzero)] at generated
    exact generated.mul_const (emPacket test (x-y))

/-- The massless original Fourier packet is exactly convolution with 1/(4pi*r). The Gaussian regulator is removed on both sides under proved integrable domination. -/
theorem em_newton_massless_convolution (kappa : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa 0 test x=
      ∫y : PhysicalMomentum,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y) := by
  have equivalent : (fun d : ℝ=>emNewtonPacket 1 d test x)=ᶠ[𝓝[>] 0]
      (fun d : ℝ=>∫y : PhysicalMomentum,emRegulatedNewton 1 d y*emPacket test (x-y)) := by
    filter_upwards [self_mem_nhdsWithin] with d dp
    exact em_newton_packet_convolution 1 (by norm_num) d dp test x
  have common:=tendsto_nhds_unique (newtonFrequency_radial test x)
    ((newtonSpace_radial test x).congr' equivalent.symm)
  have independent : emNewtonPacket kappa 0 test x=emNewtonPacket 1 0 test x := by
    unfold emNewtonPacket
    congr 1
    funext frequency
    simp [emNewtonMultiplier]
  exact independent.trans common

end LowEnergy.GaussComposite.ActualEMCarrierOwn
