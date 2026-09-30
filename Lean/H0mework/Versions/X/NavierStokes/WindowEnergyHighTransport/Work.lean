import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Green
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Source
import H0mework.Versions.X.NavierStokes.WindowEnergyLowAdvector.Energy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeCompleteStressAction NativeForwardWindowPairingReadout
open NativeWindowCrossHistoryAction NativeWindowHighTransportGreen
open NativeWindowLowAdvectorHistory (jointMeasure read_memLp)
noncomputable section
variable {nu : Viscosity}

abbrev Field := C(Torus,ℝ)

def cubic (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (j output input : Coordinate) (time : ℝ) : Field :=
  drift seed F A time j*velocity seed F time output*velocity seed F time input

def derivativePair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (j output input : Coordinate) (time : ℝ) : Field :=
  gradient seed F time j output*velocity seed F time input+velocity seed F time output*gradient seed F time j input

private theorem velocity_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (i : Coordinate) :
    MemLp (fun shift => velocity seed F (time-shift) i) ∞ averageMeasure := by
  simpa only [velocity,NativeWindowStressHeatTime.field_original] using read_memLp seed time (NativeWindowFiniteGramFourier.read F i)

private theorem gradient_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (j i : Coordinate) :
    MemLp (fun shift => gradient seed F (time-shift) j i) ∞ averageMeasure := read_memLp seed time (NativeWindowStressHeatSource.jetRead F j 1 i)

theorem cubic_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector) (j output input : Coordinate) :
    Integrable (fun shift => cubic seed F A j output input (time-shift)) averageMeasure := by
  have d := (velocity_memLp seed time F j).sub (velocity_memLp seed time A j)
  have paid := (velocity_memLp seed time F input).mul (r := ∞) ((velocity_memLp seed time F output).mul (r := ∞) d)
  simpa only [Pi.mul_def,Pi.sub_def,cubic,drift,Pi.sub_apply] using paid.integrable (by norm_num : (1 : ℝ≥0∞)≤∞)

theorem derivativePair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (j output input : Coordinate) :
    Integrable (fun shift => derivativePair seed F j output input (time-shift)) averageMeasure := by
  have first := ((read_memLp seed time (NativeWindowFiniteGramFourier.read F input)).mul (r := ∞)
    (read_memLp seed time (NativeWindowStressHeatSource.jetRead F j 1 output))).integrable (by norm_num : (1 : ℝ≥0∞)≤∞)
  have last := ((read_memLp seed time (NativeWindowStressHeatSource.jetRead F j 1 input)).mul (r := ∞)
    (read_memLp seed time (NativeWindowFiniteGramFourier.read F output))).integrable (by norm_num : (1 : ℝ≥0∞)≤∞)
  simpa only [Pi.mul_def,Pi.add_def,derivativePair,NativeWindowCrossHistoryAction.gradient,velocity,NativeWindowStressHeatTime.field_original] using (show Integrable (fun shift =>
    NativeWindowStressHeatSource.jetRead F j 1 output (NativeUnifiedCompleteSource.source seed (time-shift))*
      NativeWindowFiniteGramFourier.read F input (NativeUnifiedCompleteSource.source seed (time-shift))+
    NativeWindowFiniteGramFourier.read F output (NativeUnifiedCompleteSource.source seed (time-shift))*
      NativeWindowStressHeatSource.jetRead F j 1 input (NativeUnifiedCompleteSource.source seed (time-shift))) averageMeasure from Integrable.fun_add (ε' := Field) first last)

def physicalCurrent (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector) (j output input : Coordinate) : Field :=
  ∫ shift,cubic seed F A j output input (time-shift) ∂averageMeasure

def stressGradient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (j output input : Coordinate) : Field :=
  ∫ shift,derivativePair seed F j output input (time-shift) ∂averageMeasure

def fullPairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector) : Field :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    physicalCurrent seed time F A j output input*stressGradient seed time F j output input

theorem transport_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector) :
    Integrable (fun times : ℝ × ℝ => transportPair seed F A (time-times.1) (time-times.2)) jointMeasure := by
  have row (j output input : Coordinate) : Integrable (fun times : ℝ × ℝ =>
      cubic seed F A j output input (time-times.1)*derivativePair seed F j output input (time-times.2)) jointMeasure :=
    (cubic_integrable seed time F A j output input).op_fst_snd (by fun_prop)
      ⟨1,fun x y => by simpa only [one_mul] using norm_mul_le x y⟩ (derivativePair_integrable seed time F j output input)
  have all := integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ (fun j _ => integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ
    (fun output _ => integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ (fun input _ => row j output input)))
  change Integrable (fun times : ℝ × ℝ => ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    cubic seed F A j output input (time-times.1)*derivativePair seed F j output input (time-times.2)) jointMeasure
  exact all

theorem transport_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector) :
    (∫ times : ℝ × ℝ,transportPair seed F A (time-times.1) (time-times.2) ∂jointMeasure)=fullPairing seed time F A := by
  have row (j output input : Coordinate) : Integrable (fun times : ℝ × ℝ =>
      cubic seed F A j output input (time-times.1)*derivativePair seed F j output input (time-times.2)) jointMeasure :=
    (cubic_integrable seed time F A j output input).op_fst_snd (by fun_prop)
      ⟨1,fun x y => by simpa only [one_mul] using norm_mul_le x y⟩ (derivativePair_integrable seed time F j output input)
  change (∫ times : ℝ × ℝ,∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    cubic seed F A j output input (time-times.1)*derivativePair seed F j output input (time-times.2) ∂jointMeasure)=_
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ
    (fun output _ => integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ (fun input _ => row j output input)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun output _ => integrable_finsetSum (ε' := Field) (μ := jointMeasure) Finset.univ (fun input _ => row j output input))]
  apply Finset.sum_congr rfl
  intro output _
  rw [integral_finsetSum Finset.univ (fun input _ => row j output input)]
  apply Finset.sum_congr rfl
  intro input _
  exact integral_prod_bilin (ContinuousLinearMap.mul ℝ Field) (cubic_integrable seed time F A j output input)
    (derivativePair_integrable seed time F j output input)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mean : Field →L[ℝ] ℝ := (innerSL ℝ (NativeWindowStressHeatSource.physical 1)).comp NativeWindowStressHeatSource.physical

theorem mean_apply (f : Field) : mean f=∫ point : Torus,f point := by
  change inner ℝ (NativeWindowStressHeatSource.physical 1) (NativeWindowStressHeatSource.physical f)=_
  simp only [NativeWindowStressHeatSource.physical_inner,ContinuousMap.one_apply,one_mul]

theorem work_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowLowAdvectorEnergy.highWork seed time radius F=mean (fullPairing seed time F (F∩wholeRestartModes radius)) := by
  let A := F∩wholeRestartModes radius
  let paired : ℝ × ℝ → Field := fun times => transportPair seed F A (time-times.1) (time-times.2)
  have paid := transport_integrable seed time F A
  have flipped : Integrable (fun times : ℝ × ℝ => paired times.swap) jointMeasure :=
    (Measure.measurePreserving_swap.integrable_comp_emb (MeasurableEquiv.prodComm : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)).measurableEmbedding).mpr paid
  have swap : (∫ times : ℝ × ℝ,paired times.swap ∂jointMeasure)=∫ times,paired times ∂jointMeasure :=
    Measure.measurePreserving_swap.integral_comp (MeasurableEquiv.prodComm : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)).measurableEmbedding paired
  have original := (mean.integral_comp_comm (NativeWindowLowAdvectorEnergy.high_integrable seed time radius F)).symm
  change mean (∫ times,NativeWindowLowAdvectorEnergy.highIntegrand seed time radius F times ∂jointMeasure)=_ at original
  rw [NativeWindowLowAdvectorEnergy.highWork,← mean_apply]
  rw [original,← integral_neg]
  have row : (fun times : ℝ × ℝ => -mean (NativeWindowLowAdvectorEnergy.highIntegrand seed time radius F times)) =ᵐ[jointMeasure]
      fun times => (1/2 : ℝ)*(mean (paired times)+mean (paired times.swap)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := averageMeasure) (ν := averageMeasure)).ae NativeWindowHistoryGNS.average_support,
      (Measure.quasiMeasurePreserving_snd (μ := averageMeasure) (ν := averageMeasure)).ae NativeWindowHistoryGNS.average_support] with times first last
    have source := paired_green seed F A (time-times.1) (time-times.2) (by linarith) (by linarith)
    have read : mean (NativeWindowLowAdvectorEnergy.highIntegrand seed time radius F times) =
        (1/2 : ℝ)*(∫ point : Torus,(pair (velocity seed F (time-times.1)) (velocity seed F (time-times.2))*
          incrementField seed F A (time-times.1) (time-times.2)) point) := by
      change mean ((1/2 : ℝ) • _)=_
      rw [map_smul,smul_eq_mul,mean_apply]
      rfl
    rw [read]
    simpa only [neg_mul,← mean_apply,paired,Prod.fst_swap,Prod.snd_swap] using source
  rw [integral_congr_ae row,integral_const_mul,integral_add (mean.integrable_comp paid) (mean.integrable_comp flipped),
    mean.integral_comp_comm paid,mean.integral_comp_comm flipped,swap]
  change _=mean (fullPairing seed time F A)
  have same : (∫ times,paired times ∂jointMeasure)=fullPairing seed time F A := transport_integral seed time F A
  rw [same]
  ring


theorem stressGradient_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (j output input : Coordinate) (x : ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace) :
    stressGradient seed time F j output input (NativeFullOrderSynthesis.circlePoint x)=
      NativeWindowStressHeatGram.cross (NativeWindowFiniteGramSource.value seed time F x)
        (NativeWindowFiniteGramSource.gradient seed time F x j) output input := by
  have commute := (ContinuousMap.evalCLM ℝ (NativeFullOrderSynthesis.circlePoint x)).integral_comp_comm
    (derivativePair_integrable seed time F j output input)
  simp only [ContinuousMap.evalCLM_apply] at commute
  rw [stressGradient,← commute]
  unfold NativeWindowStressHeatGram.cross
  rw [← NativeWindowLowAdvectorHistory.scalar_product_integral,← NativeWindowLowAdvectorHistory.scalar_product_integral,
    ← integral_add (NativeWindowLowAdvectorHistory.scalar_product_integrable _ _)
      (NativeWindowLowAdvectorHistory.scalar_product_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [NativeWindowLowAdvectorHistory.value_read seed time F x,
    NativeWindowLowAdvectorHistory.gradient_read seed time F x j] with shift value gradientRead
  simp only [derivativePair,ContinuousMap.add_apply,ContinuousMap.mul_apply,value,gradientRead]
  ring

theorem stressGradient_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (j output input : Coordinate) (x : ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => NativeWindowFiniteGramFourier.stress seed time F output input
      (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (stressGradient seed time F j output input
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  simp only [NativeWindowFiniteGramFourier.stress_physical,stressGradient_physical]
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp (NativeWindowFiniteGramSource.stress_derivative seed time F x j parameter) output) input


open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open NativeEndpointVelocityCarrier NativeWindowFiniteGramFourier

theorem fourier_product (f g : Field) (wave : IntegerWavevector) :
    fourierRead wave (f*g)=∑' p,fourierRead p f*fourierRead (wave-p) g := by
  let first := (Complex.ofRealCLM.compLeftContinuous ℝ Torus) f
  let last := (Complex.ofRealCLM.compLeftContinuous ℝ Torus) g
  have actual := NativeFourierProduct.product_coeff (first.toLp 2 volume ℂ) (last.toLp 2 volume ℂ) wave
  simp only [UnitAddTorus.mFourierCoeff_toLp] at actual
  rw [fourierRead_apply]
  calc
    _ = UnitAddTorus.mFourierCoeff (fun point => (first.toLp 2 volume ℂ) point*(last.toLp 2 volume ℂ) point) wave := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume first,
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume last] with point left right
      change UnitAddTorus.mFourier (-wave) point • ((f*g) point : ℂ)=
        UnitAddTorus.mFourier (-wave) point • ((first.toLp 2 volume ℂ) point*(last.toLp 2 volume ℂ) point)
      rw [left,right]
      simp only [ContinuousMap.mul_apply,Complex.ofReal_mul]
      rfl
    _ = _ := by
      rw [actual]
      simp only [fourierRead_apply]
      rfl

theorem velocity_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (i : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave (velocity seed F time i)=NativeUnheatedWindowStress.projection seed F time wave i := by
  rw [velocity,NativeWindowStressHeatTime.field_original,fourierRead_apply]
  simp_rw [read_original]
  have paid := NativePhysicalContinuous.continuousField_fourier
    (complexSharpSupportProjection F (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst))
    (NativeCorrectionPhysical.finite_amplitude_paid F _) (complexSharpSupportProjection_reality _ _ closed
      (wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality)) i wave
  simpa only [NativeUnheatedWindowStress.projection,NativeUnifiedCompleteSource.velocity_read] using paid

theorem cubic_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (closed : ∀ k,k∈F → waveNeg k∈F) (j output input : Coordinate) (wave : IntegerWavevector) :
    (NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*
      fourierRead wave (cubic seed F (F∩wholeRestartModes radius) j output input time)=
        NativeWindowHighTransportSource.component seed F radius j output input time wave := by
  classical
  have lowClosed : ∀ k,k∈F∩wholeRestartModes radius →waveNeg k∈F∩wholeRestartModes radius := by
    intro k member
    exact Finset.mem_inter.mpr ⟨closed k (Finset.mem_inter.mp member).1,
      ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget.puncturedIntegerWaveFrequencyCube_waveNeg_mem radius (Finset.mem_inter.mp member).2⟩
  have pairReadSame : velocity seed F time output*velocity seed F time input=
      pairRead F output input (NativeUnifiedCompleteSource.source seed time) := by
    simp only [pairRead,velocity,NativeWindowStressHeatTime.field_original]
  rw [cubic,mul_assoc,fourier_product]
  simp_rw [drift,Pi.sub_apply,map_sub,velocity_fourier seed time F closed,
    velocity_fourier seed time (F∩wholeRestartModes radius) lowClosed,pairReadSame,
    pair_fourier F _ (complexSharpSupportProjection_reality _ _ closed
      (wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality)),NativeCompleteStressBilinear.mixed_read,
    NativeUnifiedCompleteSource.velocity_read]
  rw [NativeWindowHighTransportSource.component_row]
  have supported (p : IntegerWavevector) (outside : p∉F) : NativeWindowHighTransportSource.highVelocity seed F radius time p j=0 := by
    rw [NativeWindowHighTransportSource.high_original]
    simp [outside]
  change (NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*(∑' p,
    NativeWindowHighTransportSource.highVelocity seed F radius time p j*(-NativeHigherTimeJets.mixedFlux
      (NativeUnheatedWindowStress.projection seed F time) (NativeUnheatedWindowStress.projection seed F time) (wave-p) output input))=_
  rw [tsum_eq_sum (s := F) (fun p outside => by rw [supported p outside,zero_mul])]
  simp only [mul_neg,Finset.sum_neg_distrib,mul_neg]
  ring


theorem physicalCurrent_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (radius : ℕ) (closed : ∀ k,k∈F →waveNeg k∈F)
    (j output input : Coordinate) (wave : IntegerWavevector) :
    (NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*
      fourierRead wave (physicalCurrent seed time F (F∩wholeRestartModes radius) j output input)=
        NativeWindowHighTransportSource.window seed F radius 0 time j output input wave := by
  rw [physicalCurrent,← (fourierRead wave).integral_comp_comm (cubic_integrable seed time F (F∩wholeRestartModes radius) j output input),
    ← integral_const_mul]
  have same : (fun shift => (NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*
      fourierRead wave (cubic seed F (F∩wholeRestartModes radius) j output input (time-shift))) =
      fun shift => NativeWindowHighTransportSource.component seed F radius j output input (time-shift) wave := by
    funext shift
    exact cubic_fourier seed (time-shift) F radius closed j output input wave
  rw [same,density_integral]
  have read := NativeWindowHighTransportSource.window_row seed F radius 0 time time ⟨nonnegative,le_rfl⟩ j output input wave
  simp_rw [← NativeWindowHighTransportSource.component_row] at read
  rw [read]
  change (∫ shift,NativeForwardWindowJets.kernelJet 0 shift •
    NativeWindowHighTransportSource.component seed F radius j output input (time-shift) wave)=_
  exact (NativeWindowFiniteStressUniform.average_original 0 time time ⟨nonnegative,le_rfl⟩
    (fun sample => NativeWindowHighTransportSource.component seed F radius j output input sample wave)).symm

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportWork
