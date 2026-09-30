import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Current

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowHighPressurePhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativePhysicalFourier NativeStressCurlAlgebra NativeHigherTimeJets
open NativeWindowStressHeatSource NativeWindowStressOseenLow NativeWindowFiniteGramFourier
open NativeWindowHighPressureCurrent NativeWindowPressureSectors
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def realSynthesis (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) : C(Torus,ℝ) :=
  ∑ k ∈ F, NativeWindowStressHeatBalance.basis k (a k)

private theorem sum_waveNeg (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (f : IntegerWavevector → ℂ) :
    (∑ k ∈ F,f (waveNeg k))=∑ k ∈ F,f k := by
  refine Finset.sum_bij (fun k _ => waveNeg k) ?_ ?_ ?_ ?_
  · exact fun k inside => closed k inside
  · intro a _ b _ same
    simpa using congrArg waveNeg same
  · intro k inside
    exact ⟨waveNeg k,closed k inside,by simp⟩
  · intros
    rfl

theorem realSynthesis_apply (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (point : Torus) :
    realSynthesis F a point=(polynomial F a 0 0 point).re := by
  simp only [realSynthesis,ContinuousMap.sum_apply]
  change (∑ k ∈ F,(a k*UnitAddTorus.mFourier k point).re) = _
  simp only [polynomial,pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  exact (Complex.re_sum _ _).symm

theorem realSynthesis_complex (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F)
    (a : IntegerWavevector → ℂ) (reality : ∀ k,a (waveNeg k)=conj (a k)) :
    (Complex.ofRealCLM.compLeftContinuous ℝ Torus) (realSynthesis F a)=polynomial F a 0 0 := by
  ext point
  change ((realSynthesis F a point : ℝ):ℂ)=polynomial F a 0 0 point
  rw [realSynthesis_apply]
  apply Complex.conj_eq_iff_re.mp
  simp only [polynomial,pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,map_sum,map_mul]
  have reflected := sum_waveNeg F closed (fun k => a k*UnitAddTorus.mFourier k point)
  have phase (k : IntegerWavevector) : UnitAddTorus.mFourier (waveNeg k) point=conj (UnitAddTorus.mFourier k point) :=
    UnitAddTorus.mFourier_neg
  simpa only [reality,phase] using reflected

theorem realSynthesis_fourier (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F)
    (a : IntegerWavevector → ℂ) (reality : ∀ k,a (waveNeg k)=conj (a k)) (k : IntegerWavevector) :
    fourierRead k (realSynthesis F a)=if k ∈ F then a k else 0 := by
  change complexCoefficient k ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (realSynthesis F a)) = _
  rw [realSynthesis_complex F closed a reality,polynomial_coefficient]
  simp only [pow_zero,one_mul]

theorem complex_product_coefficient (F : Finset IntegerWavevector) (a b : IntegerWavevector → ℂ) (k : IntegerWavevector) :
    complexCoefficient k (polynomial F a 0 0*polynomial F b 0 0) =
      ∑ q ∈ F,if k-q ∈ F then a (k-q)*b q else 0 := by
  have single (p : IntegerWavevector) : complexCoefficient k (UnitAddTorus.mFourier p)=if k=p then 1 else 0 := by
    have paid := polynomial_coefficient {p} (fun _ => (1:ℂ)) 0 0 k
    simpa only [polynomial,Finset.sum_singleton,pow_zero,one_mul,one_smul,Finset.mem_singleton] using paid
  rw [NativeWindowPressureLowSource.polynomial_product]
  simp only [map_sum,map_smul,single,smul_eq_mul,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  have same (p : IntegerWavevector) : k=p+q ↔ p=k-q := by
    constructor
    · intro equal
      exact eq_sub_of_add_eq equal.symm
    · intro equal
      exact sub_eq_iff_eq_add.mp equal.symm
  simp only [same,Finset.sum_ite_eq']

theorem real_product_coefficient (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F)
    (a b : IntegerWavevector → ℂ) (aReal : ∀ k,a (waveNeg k)=conj (a k)) (bReal : ∀ k,b (waveNeg k)=conj (b k))
    (k : IntegerWavevector) :
    fourierRead k (realSynthesis F a*realSynthesis F b)=∑ q ∈ F,if k-q ∈ F then a (k-q)*b q else 0 := by
  have same : (Complex.ofRealCLM.compLeftContinuous ℝ Torus) (realSynthesis F a*realSynthesis F b)=
      polynomial F a 0 0*polynomial F b 0 0 := by
    ext point
    change ((realSynthesis F a point*realSynthesis F b point:ℝ):ℂ)=_
    rw [Complex.ofReal_mul]
    exact congrArg₂ HMul.hMul
      (congrArg (fun f : C(Torus,ℂ) => f point) (realSynthesis_complex F closed a aReal))
      (congrArg (fun f : C(Torus,ℂ) => f point) (realSynthesis_complex F closed b bReal))
  change complexCoefficient k ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (realSynthesis F a*realSynthesis F b)) = _
  rw [same,complex_product_coefficient]

theorem force_reality (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value)
    (k : IntegerWavevector) (output : Coordinate) : force value value (waveNeg k) output=conj (force value value k output) := by
  have flux : mixedFlux value value (waveNeg k)=fun i j => conj (mixedFlux value value k i j) :=
    funext fun i => funext fun j => NativePressureFullOrder.quadraticFlux_reality value reality k i j
  simp only [force,flux,NativePressureFullOrder.stressPressure_reality,complexWavevector_waveNeg,Pi.neg_apply,map_mul,map_neg,
    Complex.conj_I,Complex.conj_ofReal]
  simp only [complexWavevector,Complex.conj_ofReal]
  ring

def pressurePair (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) : C(Torus,ℝ) :=
  realSynthesis F (fun k => force value value k output)*realSynthesis F (fun k => value k input)+
    realSynthesis F (fun k => force value value k input)*realSynthesis F (fun k => value k output)

theorem pressurePair_fourier (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value)
    (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) (k : IntegerWavevector) :
    fourierRead k (pressurePair value F output input)=tensorRow value F k output input := by
  have real (coordinate : Coordinate) (wave : IntegerWavevector) : value (waveNeg wave) coordinate=conj (value wave coordinate) :=
    congrFun (reality wave) coordinate
  rw [pressurePair,map_add,real_product_coefficient F closed _ _ (fun k => force_reality value reality k output) (real input),
    real_product_coefficient F closed _ _ (fun k => force_reality value reality k input) (real output)]
  simp only [tensorRow,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

theorem realSynthesis_projection (value : ComplexVorticityHilbertState) (F G : Finset IntegerWavevector)
    (inside : G ⊆ F) (input : Coordinate) :
    realSynthesis F (fun k => complexSharpSupportProjection G value k input)=realSynthesis G (fun k => value k input) := by
  unfold realSynthesis
  rw [← Finset.sum_subset inside (fun k _ outside => by
    simp only [complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply,map_zero])]
  apply Finset.sum_congr rfl
  intro k member
  exact congrArg (NativeWindowStressHeatBalance.basis k)
    (congrFun ((complexSharpSupportProjection_apply G value k).trans (if_pos member)) input)

theorem realSynthesis_sub (F : Finset IntegerWavevector) (a b : IntegerWavevector → ℂ) :
    realSynthesis F (fun k => a k-b k)=realSynthesis F a-realSynthesis F b := by
  simp only [realSynthesis,map_sub,Finset.sum_sub_distrib]

variable {nu : Viscosity}

theorem source_reality (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    FiniteStateFourierReality (value seed radius time) := by
  have raw : FiniteStateFourierReality (velocity seed time) :=
    wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality
  intro wave
  change NativeWindowPressureLowInputs.high (velocity seed time) (integerWaveFrequencyCube radius) (waveNeg wave) =
    vectorConj (NativeWindowPressureLowInputs.high (velocity seed time) (integerWaveFrequencyCube radius) wave)
  rw [NativeWindowPressureLowInputs.high_row,NativeWindowPressureLowInputs.high_row]
  by_cases member : wave ∈ integerWaveFrequencyCube radius
  · rw [if_pos member,if_pos (cube_closed radius wave member)]
    simp
  · have absent : waveNeg wave ∉ integerWaveFrequencyCube radius := fun inside => member (by simpa using cube_closed radius (waveNeg wave) inside)
    rw [if_neg member,if_neg absent]
    exact raw wave

theorem source_pressurePair_fourier (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (F : Finset IntegerWavevector) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) (k : IntegerWavevector) :
    fourierRead k (pressurePair (value seed radius time) F output input)=tensorRow (value seed radius time) F k output input :=
  pressurePair_fourier _ (source_reality seed radius time) F closed output input k

theorem source_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (input : Coordinate) :
    realSynthesis F (fun k => velocity seed time k input)=NativeWindowFiniteGramFourier.read F input (NativeUnifiedCompleteSource.source seed time) := by
  simp only [NativeWindowFiniteGramFourier.read,NativeWindowFiniteGramFourier.complexRead,ContinuousLinearMap.comp_apply,
    sum_apply,map_sum,realSynthesis]
  apply Finset.sum_congr rfl
  intro k _
  rfl

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay

theorem source_velocity (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (F : Finset IntegerWavevector) (input : Coordinate) :
    realSynthesis F (fun k => value seed radius time k input)=
      NativeWindowFiniteGramFourier.read F input (NativeUnifiedCompleteSource.source seed time)-
        NativeWindowFiniteGramFourier.read (F∩wholeRestartModes radius) input (NativeUnifiedCompleteSource.source seed time) := by
  have projected : realSynthesis F (fun k => value seed radius time k input)=
      realSynthesis F (fun k => NativeWindowHighTransportSource.highVelocity seed F radius time k input) := by
    rw [← projected_value_original,realSynthesis_projection _ F F (fun _ h => h)]
  rw [projected,NativeWindowHighTransportSource.highVelocity]
  change realSynthesis F (fun k => NativeUnheatedWindowStress.projection seed F time k input-
    NativeUnheatedWindowStress.projection seed (F∩wholeRestartModes radius) time k input)=_
  rw [realSynthesis_sub]
  have original : NativeAbsoluteEventualControl.velocity seed time=NativeUnheatedSourceWeightedTail.velocity seed time :=
    (NativeUnifiedCompleteSource.velocity_read seed time).symm
  simp only [NativeUnheatedWindowStress.projection,original]
  rw [realSynthesis_projection _ F F (fun _ h => h),realSynthesis_projection _ F _ Finset.inter_subset_left]
  exact congrArg₂ HSub.hSub (source_read seed time F input) (source_read seed time (F∩wholeRestartModes radius) input)

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_pressurePair_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    pressurePair (value seed radius (step.2.clockAdvance+time)) F output input=pressurePair (value step.1 radius time) F output input := by
  rw [value_next seed step generated radius time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHighPressurePhysical
