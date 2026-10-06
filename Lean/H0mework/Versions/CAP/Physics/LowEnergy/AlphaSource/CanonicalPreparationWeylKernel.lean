import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylSlices
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationVacuumSymbol
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationActualFactor
open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

def partialFourier (p k : PhysicalMomentum) : ℂ := 𝓕 (symbolSlice p) k

-- Mathlib uses exp(-2πi ξ·x); physical midpoint momentum is π(ξ+η).
def physicalMidpoint (xi eta : PhysicalMomentum) : PhysicalMomentum := Real.pi • (xi+eta)

def weylKernel (xi eta : PhysicalMomentum) : ℂ :=
  partialFourier (physicalMidpoint xi eta) (xi-eta)

theorem physicalMidpoint_original (xi eta : PhysicalMomentum) :
    physicalMidpoint xi eta=(1/2 : ℝ) • ((2*Real.pi) • xi+(2*Real.pi) • eta) := by
  rw [physicalMidpoint,←smul_add,smul_smul]
  congr 1
  ring

theorem partialFourier_integrable (p k : PhysicalMomentum) :
    Integrable (fun x : PhysicalMomentum => 𝐞 (-⟪x,k⟫) • symbolSlice p x) :=
  (Real.fourierIntegral_convergent_iff k).mpr (symbolSlice_integrable p)

theorem weylKernel_integrable (xi eta : PhysicalMomentum) :
    Integrable (fun x : PhysicalMomentum =>
      𝐞 (-⟪x,xi-eta⟫) • symbolSlice (physicalMidpoint xi eta) x) :=
  partialFourier_integrable _ _

theorem partialFourier_literal (p k : PhysicalMomentum) :
    partialFourier p k=∫ x : PhysicalMomentum,
      𝐞 (-⟪x,k⟫) • (b1 (flatPosition x,p) : ℂ) := rfl

theorem actual_raw_pairing (x k : PhysicalMomentum) :
    ⟪x,k⟫=flatCovector k (flatPosition x) := by
  simp only [PiLp.inner_apply,Real.inner_apply]
  change (∑ i : Fin 100, x i*k i)=∑ i : Fin 100,k i*x i
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem partialFourier_raw100 (p k : PhysicalMomentum) :
    partialFourier p k=∫ z : FlatConfiguration,
      𝐞 (-flatCovector k z) • (b1 (z,p) : ℂ) ∂flatMeasure := by
  rw [partialFourier_literal]
  simp only [actual_raw_pairing]
  exact actual_flatPosition_measure.integral_comp flatPosition.toHomeomorph.measurableEmbedding
    (fun z : FlatConfiguration => 𝐞 (-flatCovector k z) • (b1 (z,p) : ℂ))

theorem partialFourier_conjugate (p k : PhysicalMomentum) :
    conj (partialFourier p k)=partialFourier p (-k) := by
  rw [partialFourier_literal,partialFourier_literal,←integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def,smul_eq_mul,map_mul,Circle.starRingEnd_addChar,
    Complex.conj_ofReal,inner_neg_right,neg_neg]

theorem partialFourier_continuous (p : PhysicalMomentum) : Continuous (partialFourier p) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (symbolSlice_integrable p)

theorem partialFourier_norm_bound (p k : PhysicalMomentum) :
    ‖partialFourier p k‖≤∫ x : PhysicalMomentum,‖symbolSlice p x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

def sourcePositionVolume : ℝ := (flatMeasure thetaPositionClosed).toReal

def sourceKernelBound : ℝ := sourceOrderOneBound*sourcePositionVolume

theorem sourcePositionVolume_nonnegative : 0≤ sourcePositionVolume := ENNReal.toReal_nonneg

theorem sourceKernelBound_nonnegative : 0≤ sourceKernelBound :=
  mul_nonneg sourceOrderOneBound_nonnegative sourcePositionVolume_nonnegative

theorem source_position_measure_finite : flatMeasure thetaPositionClosed≠⊤ := by
  rw [←raw100_volume]
  exact thetaPositionClosed_compact.measure_ne_top

theorem symbolSlice_integral_norm_bound (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖symbolSlice p x‖)≤ sourceKernelBound*‖p‖ := by
  have rawIntegrable : Integrable (fun z : FlatConfiguration => ‖(b1 (z,p) : ℂ)‖) flatMeasure := by
    rw [←raw100_volume]
    exact ((Complex.continuous_ofReal.comp
      (b1_continuous.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        ((b1_position_compact p).comp_left (by norm_num : (Complex.ofReal : ℝ→ℂ) 0=0))).norm
  have supportEq : (∫ z in thetaPositionClosed,‖(b1 (z,p) : ℂ)‖ ∂flatMeasure)=
      ∫ z : FlatConfiguration,‖(b1 (z,p) : ℂ)‖ ∂flatMeasure := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z outside
    simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside outside,
      zero_mul,Complex.ofReal_zero,norm_zero]
  calc
    _ = ∫ z : FlatConfiguration,‖(b1 (z,p) : ℂ)‖ ∂flatMeasure :=
      actual_flatPosition_measure.integral_comp flatPosition.toHomeomorph.measurableEmbedding _
    _ = ∫ z in thetaPositionClosed,‖(b1 (z,p) : ℂ)‖ ∂flatMeasure := supportEq.symm
    _ ≤ ∫ z in thetaPositionClosed,sourceOrderOneBound*‖p‖ ∂flatMeasure := by
      apply setIntegral_mono_on rawIntegrable.integrableOn
        (integrableOn_const source_position_measure_finite) thetaPositionClosed_closed.measurableSet
      intro z _
      simpa only [Complex.norm_real,Real.norm_eq_abs] using b1_order_one (z,p)
    _ = sourceKernelBound*‖p‖ := by
      rw [setIntegral_const]
      change sourcePositionVolume*(sourceOrderOneBound*‖p‖)=_
      rw [sourceKernelBound]
      ring

theorem weylKernel_order_one (xi eta : PhysicalMomentum) :
    ‖weylKernel xi eta‖≤ sourceKernelBound*‖physicalMidpoint xi eta‖ :=
  (partialFourier_norm_bound _ _).trans (symbolSlice_integral_norm_bound _)

theorem weylKernel_hermitian (xi eta : PhysicalMomentum) :
    conj (weylKernel eta xi)=weylKernel xi eta := by
  rw [weylKernel,partialFourier_conjugate]
  simp only [physicalMidpoint,add_comm eta xi,neg_sub]
  rfl

theorem weylKernel_zero_low (xi eta : PhysicalMomentum)
    (low : ‖physicalMidpoint xi eta‖≤1/2) : weylKernel xi eta=0 := by
  have zero : symbolSlice (physicalMidpoint xi eta)=0 := by
    funext x
    simp only [symbolSlice,b1_zero_low (flatPosition x,physicalMidpoint xi eta) low,
      Complex.ofReal_zero,Pi.zero_apply]
  simp only [weylKernel,partialFourier,zero,Real.fourier_eq,Pi.zero_apply,smul_zero,integral_zero]

theorem physicalMidpoint_source :
    physicalMidpoint ((2*Real.pi)⁻¹ • sourceMomentum) ((2*Real.pi)⁻¹ • sourceMomentum)=
      sourceMomentum := by
  rw [physicalMidpoint,←add_smul,←mul_smul]
  have scalar : Real.pi*((2*Real.pi)⁻¹+(2*Real.pi)⁻¹)=1 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [scalar,one_smul]

theorem original_vacuum_cutoff_factor (z : FlatConfiguration) (p : PhysicalMomentum) :
    (b1 (z,p) : ℂ) • CanonicalPreparationCreation.vacuumFiber=
      (factorWeight (z,p) : ℂ) •
        ((principalFactor (PreparationScalarCoordinates.fullCoordinates.symm z)
          (nativeCovector p) : ℂ) • CanonicalPreparationCreation.vacuumFiber) := by
  rw [b1,nativePhase,Complex.ofReal_mul,mul_smul]

end LowEnergy.PreparationVacuumWeyl
