import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Physical

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise ComplexConjugate Matrix
namespace SaturationMonoid.NavierStokes.NativeWindowPressureStrainPhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativePhysicalFourier NativeStressCurlAlgebra NativeHigherTimeJets
open NativeWindowHighPressureCurrent NativeWindowHighPressurePhysical NativeWindowPressureSectors
open NativePhysicalGradient (multiplier)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pressureScalar (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  realSynthesis F (fun k => stressPressureCoefficient k (mixedFlux value value k))

def gradient (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (direction input : Coordinate) : C(Torus,ℝ) :=
  realSynthesis F (fun k => multiplier k direction*value k input)

def strain (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) : C(Torus,ℝ) :=
  pressureScalar value F*(gradient value F output input+gradient value F input output)

theorem pressure_reality (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value) (k : IntegerWavevector) :
    stressPressureCoefficient (waveNeg k) (mixedFlux value value (waveNeg k))=conj (stressPressureCoefficient k (mixedFlux value value k)) := by
  have flux : mixedFlux value value (waveNeg k)=fun i j => conj (mixedFlux value value k i j) :=
    funext fun i => funext fun j => NativePressureFullOrder.quadraticFlux_reality value reality k i j
  rw [flux,NativePressureFullOrder.stressPressure_reality]

theorem gradient_reality (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value)
    (k : IntegerWavevector) (direction input : Coordinate) :
    multiplier (waveNeg k) direction*value (waveNeg k) input=conj (multiplier k direction*value k input) := by
  have scalar : multiplier (waveNeg k) direction=conj (multiplier k direction) := by
    change multiplier (-k) direction=conj (multiplier k direction)
    rw [NativePhysicalGradient.multiplier_neg]
    simp only [multiplier,complexWavevector,map_mul,Complex.conj_I,Complex.conj_ofReal]
    ring
  have entry : value (waveNeg k) input=conj (value k input) := congrFun (reality k) input
  rw [scalar,entry,map_mul]

theorem strain_fourier (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value)
    (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) (k : IntegerWavevector) :
    NativeWindowFiniteGramFourier.fourierRead k (strain value F output input)=strainRow value F k output input := by
  rw [strain,mul_add,map_add]
  unfold pressureScalar gradient
  rw [real_product_coefficient F closed (fun k => stressPressureCoefficient k (mixedFlux value value k))
    (fun k => multiplier k output*value k input) (pressure_reality value reality) (fun k => gradient_reality value reality k output input),
    real_product_coefficient F closed (fun k => stressPressureCoefficient k (mixedFlux value value k))
    (fun k => multiplier k input*value k output) (pressure_reality value reality) (fun k => gradient_reality value reality k input output)]
  simp only [strainRow,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [scalarRow]
  split_ifs <;> ring

theorem pressureScalar_continuous (F : Finset IntegerWavevector) : Continuous (fun value => pressureScalar value F) := by
  apply continuous_finsetSum
  intro k _
  have flux : Continuous (fun value : ComplexVorticityHilbertState => mixedFlux value value k) :=
    continuous_pi fun i => continuous_pi fun j => (mixedFluxCLM k i j).continuous.clm_apply continuous_id
  exact (NativeWindowStressHeatBalance.basis k).continuous.comp ((NativeCofinalStress.stressPressureCLM k).continuous.comp flux)

def pressureCap (F : Finset IntegerWavevector) : ℝ := 9*∑ k ∈ F,‖NativeWindowStressHeatBalance.basis k‖

theorem pressureCap_nonnegative (F : Finset IntegerWavevector) : 0 ≤ pressureCap F := by
  unfold pressureCap
  positivity

theorem pressureScalar_bound (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) :
    ‖pressureScalar value F‖ ≤ pressureCap F*‖value‖^2 := by
  unfold pressureScalar realSynthesis
  apply (norm_sum_le _ _).trans
  have each (k : IntegerWavevector) : ‖NativeWindowStressHeatBalance.basis k (stressPressureCoefficient k (mixedFlux value value k))‖ ≤
      ‖NativeWindowStressHeatBalance.basis k‖*(9*‖value‖^2) := by
    apply ((NativeWindowStressHeatBalance.basis k).le_opNorm _).trans
    have paid := (pressure_norm k _).trans (NativeWindowFiniteStressConvergence.tensor_majorant (mixedFlux value value k)
      (3*‖value‖*‖value‖) (by positivity) (mixedFlux_norm_le value value k))
    exact mul_le_mul_of_nonneg_left (paid.trans_eq (by ring)) (norm_nonneg _)
  exact (Finset.sum_le_sum fun k _ => each k).trans_eq (by rw [← Finset.sum_mul]; unfold pressureCap; ring)

theorem gradient_trace_zero (value : ComplexVorticityHilbertState) (transverse : ∀ k,complexWavevector k ⬝ᵥ value k=0)
    (F : Finset IntegerWavevector) : (∑ j : Coordinate,gradient value F j j)=0 := by
  ext point
  simp only [gradient,realSynthesis,ContinuousMap.sum_apply,ContinuousMap.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  have source : (∑ j : Coordinate,multiplier k j*value k j)=0 := by
    change (∑ j : Coordinate,(Complex.I*(2*Real.pi:ℝ)*complexWavevector k j)*value k j)=0
    rw [show (∑ j : Coordinate,(Complex.I*(2*Real.pi:ℝ)*complexWavevector k j)*value k j)=
      (Complex.I*(2*Real.pi:ℝ))*(complexWavevector k ⬝ᵥ value k) by simp only [dotProduct,Finset.mul_sum,mul_assoc]]
    rw [transverse,mul_zero]
  have read := congrArg (fun z => NativeWindowStressHeatBalance.basis k z point) source
  simpa only [map_sum,ContinuousMap.sum_apply,map_zero,ContinuousMap.zero_apply] using read

theorem strain_trace_zero (value : ComplexVorticityHilbertState) (transverse : ∀ k,complexWavevector k ⬝ᵥ value k=0)
    (F : Finset IntegerWavevector) : (∑ i : Coordinate,strain value F i i)=0 := by
  simp only [strain,← Finset.mul_sum,Finset.sum_add_distrib,gradient_trace_zero value transverse F,add_zero,mul_zero]

def gradientRead (F : Finset IntegerWavevector) (radius : ℕ) (direction input : Coordinate) :
    NativeCompleteStressAction.FullSpace →L[ℝ] C(Torus,ℝ) :=
  NativeWindowStressHeatSource.jetRead F direction 1 input-
    NativeWindowStressHeatSource.jetRead (F∩integerWaveFrequencyCube radius) direction 1 input

private theorem realSynthesis_mask (F G : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) :
    realSynthesis F (fun k => if k ∈ G then a k else 0)=realSynthesis (F∩G) a := by
  simp only [realSynthesis,apply_ite,map_zero]
  rw [← Finset.sum_filter]
  congr 1

variable {nu : Viscosity}

theorem source_gradient (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (F : Finset IntegerWavevector) (direction input : Coordinate) :
    gradient (value seed radius time) F direction input=gradientRead F radius direction input (NativeUnifiedCompleteSource.source seed time) := by
  have read (G : Finset IntegerWavevector) : NativeWindowStressHeatSource.jetRead G direction 1 input (NativeUnifiedCompleteSource.source seed time)=
      realSynthesis G (fun k => multiplier k direction*velocity seed time k input) := by
    ext point
    rw [NativeWindowStressHeatSource.jetRead_apply,realSynthesis_apply]
    simp only [NativeWindowStressHeatSource.polynomial,pow_one,pow_zero,one_mul]
    rfl
  rw [gradientRead,sub_apply,read,read]
  simp only [gradient,value,NativeWindowPressureLowInputs.high,lp.coeFn_sub,Pi.sub_apply,mul_sub,realSynthesis_sub,
    complexSharpSupportProjection_apply,ite_apply,Pi.zero_apply,mul_ite,mul_zero,realSynthesis_mask]

theorem source_transverse (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (k : IntegerWavevector) : complexWavevector k ⬝ᵥ value seed radius time k=0 := by
  rw [value,NativeWindowPressureLowInputs.high_row]
  split_ifs
  · simp
  · exact NativeCompleteVelocityCurl.source_transverse seed time nonnegative k

theorem source_strain_fourier (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) (k : IntegerWavevector) :
    NativeWindowFiniteGramFourier.fourierRead k (strain (value seed radius time) F output input)=strainRow (value seed radius time) F k output input :=
  strain_fourier _ (source_reality seed radius time) F closed output input k

theorem source_strain_trace_zero (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : (∑ i : Coordinate,strain (value seed radius time) F i i)=0 :=
  strain_trace_zero _ (source_transverse seed radius time nonnegative) F

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_strain_next (seed : GeneratedWholeRestartCurrent nu) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    strain (value seed radius (step.2.clockAdvance+time)) F output input=strain (value step.1 radius time) F output input := by
  rw [value_next seed step generated radius time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowPressureStrainPhysical
