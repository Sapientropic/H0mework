import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffCurrent
import H0mework.Versions.X.NavierStokes.WindowEnergyRetained.Action
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Spatial
import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Physical

set_option autoImplicit false
open scoped BigOperators Topology ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffPhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativePhysicalFourier NativeWindowCrossHistoryAction NativeWindowRetainedAction NativeWindowHighPressurePhysical
open NativeWindowStressHeatSource NativeWindowFiniteGramFourier NativeForwardWindowPairingReadout
open NativeWindowStressHeatBalance (basis)
open NativePhysicalGradient (multiplier)
noncomputable section
variable {nu : Viscosity}

def filtered (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (output input : Coordinate) : C(Torus,ℝ) :=
  realSynthesis F (fun k => stressRead k output input (NativeUnifiedCompleteSource.source seed time))

def filteredGradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : C(Torus,ℝ) :=
  realSynthesis F (fun k => multiplier k j*stressRead k output input (NativeUnifiedCompleteSource.source seed time))

def field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (output input : Coordinate) : C(Torus,ℝ) :=
  filtered seed F time output input+velocity seed F time output*velocity seed F time input

def fieldGradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : C(Torus,ℝ) :=
  filteredGradient seed F time j output input+
    gradient seed F time j output*velocity seed F time input+velocity seed F time output*gradient seed F time j input

theorem synthesis_line (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (j : Coordinate)
    (x : PhysicalSpace) (parameter : ℝ) : HasDerivAt
      (fun r => realSynthesis F a (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (realSynthesis F (fun k => multiplier k j*a k)
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have original := Complex.reCLM.hasFDerivAt.comp_hasDerivAt parameter (polynomial_line F a j 0 x parameter)
  convert! original using 1
  · funext r
    simp only [realSynthesis_apply,polynomial,pow_zero,one_mul,Function.comp_def,Complex.reCLM_apply]
  · simp only [realSynthesis_apply,polynomial,pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem field_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) (x : PhysicalSpace) (parameter : ℝ) : HasDerivAt
      (fun r => field seed F time output input (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (fieldGradient seed F time j output input
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have original := (synthesis_line F (fun k => stressRead k output input (NativeUnifiedCompleteSource.source seed time)) j x parameter).add
    ((velocity_derivative seed F time output j x parameter).mul (velocity_derivative seed F time input j x parameter))
  simpa only [field,fieldGradient,filtered,filteredGradient,ContinuousMap.add_apply,ContinuousMap.mul_apply,Pi.add_apply,Pi.mul_apply,add_assoc] using! original

theorem filtered_divergence (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (output : Coordinate) : (∑ j : Coordinate,filteredGradient seed F time j output j)=
      convectionRead F output (NativeUnifiedCompleteSource.source seed time) := by
  simp only [filteredGradient,realSynthesis,convectionRead,sum_apply,ContinuousLinearMap.comp_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← map_sum]
  apply congrArg (basis k)
  change (∑ j : Coordinate,multiplier k j*stressRead k output j (NativeUnifiedCompleteSource.source seed time))=
    Complex.I*(2*Real.pi : ℝ)*∑ j : Coordinate,complexWavevector k j*stressRead k output j (NativeUnifiedCompleteSource.source seed time)
  simp only [multiplier,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem divergence_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (nonnegative : 0 ≤ time) (output : Coordinate) : (∑ j : Coordinate,fieldGradient seed F time j output j)=
      convectionResidual seed F time output := by
  simp only [fieldGradient,Finset.sum_add_distrib,← Finset.mul_sum,gradient_trace_zero seed F time nonnegative,mul_zero,add_zero,
    filtered_divergence,convectionResidual,advection]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def current (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : C(Torus,ℝ) :=
  velocity seed F time output*field seed F time input j+velocity seed F time input*field seed F time output j

def strain (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∑ j : Coordinate,(gradient seed F time j output*field seed F time input j+
    gradient seed F time j input*field seed F time output j)

def currentGradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : C(Torus,ℝ) :=
  gradient seed F time j output*field seed F time input j+velocity seed F time output*fieldGradient seed F time j input j+
    gradient seed F time j input*field seed F time output j+velocity seed F time input*fieldGradient seed F time j output j

theorem current_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) (x : PhysicalSpace) (parameter : ℝ) : HasDerivAt
      (fun r => current seed F time j output input (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (currentGradient seed F time j output input
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have original := ((velocity_derivative seed F time output j x parameter).mul (field_derivative seed F time j input j x parameter)).add
    ((velocity_derivative seed F time input j x parameter).mul (field_derivative seed F time j output j x parameter))
  simpa only [current,currentGradient,ContinuousMap.add_apply,ContinuousMap.mul_apply,Pi.add_apply,Pi.mul_apply,add_assoc] using! original

theorem convection_pair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (nonnegative : 0 ≤ time) (output input : Coordinate) :
    convectionPair seed F output input time=(∑ j : Coordinate,currentGradient seed F time j output input)-strain seed F time output input := by
  simp only [currentGradient,strain,Finset.sum_add_distrib,← Finset.mul_sum,divergence_original seed F time nonnegative,
    convectionPair,NativeWindowRetainedAction.pair]
  ring

theorem velocity_synthesis (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (i : Coordinate) :
    velocity seed F time i=realSynthesis F (fun k => NativeEndpointVelocityCarrier.wholeVelocity
      (NativeUnifiedCompleteSource.source seed time).fst k i) := by
  have original := (NativeWindowStressHeatTime.field_original seed F i time).trans
    (NativeWindowHighPressurePhysical.source_read seed time F i).symm
  simpa only [NativeWindowHighPressureCurrent.velocity,NativeUnheatedSourceWeightedTail.velocity] using! original

theorem product_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    fourierRead k (velocity seed F time output*velocity seed F time input)=
      -NativeHigherTimeJets.mixedFlux (NativeUnheatedWindowStress.projection seed F time)
        (NativeUnheatedWindowStress.projection seed F time) k output input := by
  let v:=NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have reality : ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory.FiniteStateFourierReality v :=
    NativeEndpointVelocityCarrier.wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality
  have rowReal (i : Coordinate) (p : IntegerWavevector) : v (waveNeg p) i=conj (v p i) := congrFun (reality p) i
  rw [velocity_synthesis,velocity_synthesis,real_product_coefficient F closed _ _ (rowReal output) (rowReal input)]
  change _ = -(-(∑' p,NativeUnheatedWindowStress.projection seed F time p input*
    NativeUnheatedWindowStress.projection seed F time (k-p) output))
  rw [neg_neg,tsum_eq_sum (s := F) (fun p outside => by
    simp [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,outside])]
  apply Finset.sum_congr rfl
  intro p inside
  by_cases last : k-p∈F <;>
    simp [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,inside,last,NativeUnifiedCompleteSource.velocity_read,mul_comm]

theorem field_fourier_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) : ∀ᵐ time : ℝ,∀ k output input,
    fourierRead k (field seed F time output input)=NativeWindowConvectionCutoffStress.coefficients seed F time k output input := by
  filter_upwards [source_tensor_ae seed] with time original k output input
  let v:=NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have reality : ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory.FiniteStateFourierReality v :=
    NativeEndpointVelocityCarrier.wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality
  have rowReal (p : IntegerWavevector) : stressRead (waveNeg p) output input (NativeUnifiedCompleteSource.source seed time)=
      conj (stressRead p output input (NativeUnifiedCompleteSource.source seed time)) := by
    change tensorRead (waveNeg p) (NativeUnifiedCompleteSource.source seed time) output input=
      conj (tensorRead p (NativeUnifiedCompleteSource.source seed time) output input)
    rw [original (waveNeg p),original p]
    exact NativePressureFullOrder.quadraticFlux_reality v reality p output input
  rw [field,map_add,filtered,realSynthesis_fourier F closed _ rowReal,product_fourier seed F closed time output input k]
  simp only [NativeWindowConvectionCutoffStress.coefficients,Pi.sub_apply]
  split_ifs <;> rfl

theorem value_fourier_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) : ∀ᵐ time : ℝ,0 ≤ time →∀ k output input,
    NativeWindowConvectionCutoffStress.value seed F time k (output,input)=
      (NativeWindowSobolevStress.quarter k : ℂ)*fourierRead k (field seed F time output input) := by
  filter_upwards [NativeWindowConvectionCutoffStress.value_original_ae seed,field_fourier_ae seed F closed] with time original physical nonnegative k output input
  rw [original nonnegative F k,physical]
  rfl

theorem current_fourier_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) : ∀ᵐ time : ℝ,0 ≤ time →∀ j output input k,
    NativeWindowConvectionCutoffCurrent.current seed F time j output input k=
      (NativeUnheatedSexticLatticePower.density 2 k : ℂ)*fourierRead k (current seed F time j output input) := by
  filter_upwards [field_fourier_ae seed F closed,NativeWindowConvectionCutoffCurrent.component_row_ae seed]
    with time physical original nonnegative j output input k
  have single (o i : Coordinate) : fourierRead k (velocity seed F time o*field seed F time i j)=
      ∑ p∈F,NativeUnheatedWindowStress.projection seed F time p o*NativeWindowConvectionCutoffStress.coefficients seed F time (k-p) i j := by
    rw [NativeWindowHighTransportWork.fourier_product]
    simp_rw [NativeWindowHighTransportWork.velocity_fourier seed time F closed,physical]
    exact tsum_eq_sum fun p outside => by
      simp [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,outside]
  change NativeWindowConvectionCutoffCurrent.component seed F j output input time k=_
  rw [original nonnegative F j output input k,current,map_add,single output input,single input output,← Finset.sum_add_distrib]

open NativeWindowHighTransportSpatial NativeSpatialTranslation NativePhysicalTranslation

theorem synthesis_shift_derivative (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (j : Coordinate) :
    HasDerivAt (fun r => shift j r (realSynthesis F a)) (realSynthesis F (fun k => multiplier k j*a k)) 0 := by
  have translated (r : ℝ) : shift j r (realSynthesis F a)=
      (Complex.reCLM.compLeftContinuous ℝ Torus) (polynomial F (fun k => phase j r k*a k) j 0) := by
    ext point
    change realSynthesis F a (point+displacement j r)=_
    rw [realSynthesis_apply]
    change (polynomial F a 0 0 (point+displacement j r)).re=(polynomial F (fun k => phase j r k*a k) j 0 point).re
    simp only [polynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,pow_zero,one_mul,
      character_add,character_displacement]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have source := (Complex.reCLM.compLeftContinuous ℝ Torus).hasFDerivAt.comp_hasDerivAt 0 (polynomial_shift_derivative F a j)
  simp only [translated]
  convert! source using 1
  ext point
  change realSynthesis F (fun k => multiplier k j*a k) point=(polynomial F a j 1 point).re
  simp only [realSynthesis_apply,polynomial,pow_zero,one_mul,pow_one]

theorem field_shift_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : HasDerivAt (fun r => shift j r (field seed F time output input))
      (fieldGradient seed F time j output input) 0 := by
  have source := (synthesis_shift_derivative F (fun k => stressRead k output input (NativeUnifiedCompleteSource.source seed time)) j).add
    ((velocity_shift_derivative seed F time output j).mul (velocity_shift_derivative seed F time input j))
  simp only [shift_zero] at source
  convert! source using 1
  ext point
  simp only [fieldGradient,filteredGradient,ContinuousMap.add_apply,ContinuousMap.mul_apply]
  ring

theorem current_shift_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) : HasDerivAt (fun r => shift j r (current seed F time j output input))
      (currentGradient seed F time j output input) 0 := by
  have source := ((velocity_shift_derivative seed F time output j).mul (field_shift_derivative seed F time j input j)).add
    ((velocity_shift_derivative seed F time input j).mul (field_shift_derivative seed F time j output j))
  simp only [shift_zero] at source
  convert! source using 1
  ext point
  simp only [currentGradient,ContinuousMap.add_apply,ContinuousMap.mul_apply]
  ring

theorem currentGradient_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) (k : IntegerWavevector) : fourierRead k (currentGradient seed F time j output input)=
      multiplier k j*fourierRead k (current seed F time j output input) :=
  fourier_derivative j _ _ (current_shift_derivative seed F time j output input) k

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffPhysical
