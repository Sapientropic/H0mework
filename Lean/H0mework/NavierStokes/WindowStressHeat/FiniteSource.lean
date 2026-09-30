import H0mework.NavierStokes.WindowHistory.Current
import H0mework.NavierStokes.InitialData.PhysicalCompiler
import H0mework.NavierStokes.WindowStressHeat.Gram

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteGramSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowPairingReadout
noncomputable section
variable {nu : Viscosity}

abbrev H := Lp ℝ 2 averageMeasure

def originalHistory (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp FullSpace 2 averageMeasure :=
  ((memLp_two_iff_integrable_sq_norm (original_integrable seed time).aestronglyMeasurable).mpr
    (NativeForwardWindowPairingMoments.original_square_integrable seed time)).toLp
      (fun shift => NativeUnifiedCompleteSource.source seed (time-shift))

theorem originalHistory_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    originalHistory seed time =ᵐ[averageMeasure]
      fun shift => NativeUnifiedCompleteSource.source seed (time-shift) := MemLp.coeFn_toLp _

def lift (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : (FullSpace →L[ℝ] ℝ) →L[ℝ] H :=
  ((ContinuousLinearMap.id ℝ (FullSpace →L[ℝ] ℝ)).compLpL₂ 2 averageMeasure).flip
    (originalHistory seed time)

theorem lift_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (read : FullSpace →L[ℝ] ℝ) :
    lift seed time read =ᵐ[averageMeasure]
      fun shift => read (NativeUnifiedCompleteSource.source seed (time-shift)) := by
  filter_upwards [read.coeFn_compLp (originalHistory seed time), originalHistory_ae seed time]
    with shift applied original
  change (read.compLp (originalHistory seed time)) shift = _
  rw [applied,original]

def realRead (wave : IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp (velocityRead wave coordinate)

def imagRead (wave : IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] ℝ :=
  Complex.imCLM.comp (velocityRead wave coordinate)

def modeRead (wave : IntegerWavevector) (coordinate : Coordinate) (x : PhysicalSpace) : FullSpace →L[ℝ] ℝ :=
  integerCosine wave x • realRead wave coordinate-integerSine wave x • imagRead wave coordinate

def modeJet (wave : IntegerWavevector) (coordinate direction : Coordinate) (x : PhysicalSpace) : FullSpace →L[ℝ] ℝ :=
  (-integerAngularCoefficient wave direction*integerSine wave x) • realRead wave coordinate-
    (integerAngularCoefficient wave direction*integerCosine wave x) • imagRead wave coordinate

def fieldRead (F : Finset IntegerWavevector) (x : PhysicalSpace) (coordinate : Coordinate) : FullSpace →L[ℝ] ℝ :=
  ∑ wave ∈ F, modeRead wave coordinate x

def gradientRead (F : Finset IntegerWavevector) (x : PhysicalSpace) (direction coordinate : Coordinate) : FullSpace →L[ℝ] ℝ :=
  ∑ wave ∈ F, modeJet wave coordinate direction x

def secondRead (F : Finset IntegerWavevector) (x : PhysicalSpace) (direction coordinate : Coordinate) : FullSpace →L[ℝ] ℝ :=
  ∑ wave ∈ F, (-(integerAngularCoefficient wave direction)^2) • modeRead wave coordinate x

def value (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (coordinate : Coordinate) : H := lift seed time (fieldRead F x coordinate)

def gradient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (direction coordinate : Coordinate) : H := lift seed time (gradientRead F x direction coordinate)

def second (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (direction coordinate : Coordinate) : H := lift seed time (secondRead F x direction coordinate)

theorem fieldRead_original (F : Finset IntegerWavevector) (x : PhysicalSpace) (coordinate : Coordinate) (state : FullSpace) :
    fieldRead F x coordinate state = finiteRealComplexFourierField F (wholeVelocity state.fst) x coordinate := by
  change (∑ wave ∈ F, modeRead wave coordinate x) state =
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) coordinate)
      (∑ wave ∈ F, realComplexFourierMode wave (wholeVelocity state.fst wave) x)
  simp only [sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro wave _
  rfl

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (coordinate : Coordinate) : value seed time F x coordinate =ᵐ[averageMeasure]
      fun shift => finiteRealComplexFourierField F
        (wholeVelocity (NativeUnifiedCompleteSource.source seed (time-shift)).fst) x coordinate := by
  filter_upwards [lift_ae seed time (fieldRead F x coordinate)] with shift original
  exact original.trans (fieldRead_original F x coordinate _)

def line (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) : PhysicalSpace :=
  x+parameter • EuclideanSpace.single direction (1 : ℝ)

theorem modeRead_derivative (wave : IntegerWavevector) (coordinate direction : Coordinate)
    (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => modeRead wave coordinate (line x direction r))
      (modeJet wave coordinate direction (line x direction parameter)) parameter := by
  have path := (hasDerivAt_id parameter).smul_const (EuclideanSpace.single direction (1 : ℝ)) |>.const_add x
  have phase := (integerWavePhaseLinear wave).hasFDerivAt.comp_hasDerivAt parameter path
  simp only [one_smul,integerWavePhaseLinear_single,Function.comp_def,id_eq] at phase
  have cosine := phase.cos
  have sine := phase.sin
  simpa only [modeRead,modeJet,integerCosine,integerSine,← integerWavePhaseLinear_apply,
    line,mul_comm,mul_neg,neg_mul,Pi.sub_def] using
    (cosine.smul_const (realRead wave coordinate)).sub (sine.smul_const (imagRead wave coordinate))

theorem modeJet_derivative (wave : IntegerWavevector) (coordinate direction : Coordinate)
    (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => modeJet wave coordinate direction (line x direction r))
      ((-(integerAngularCoefficient wave direction)^2) • modeRead wave coordinate (line x direction parameter)) parameter := by
  have path := (hasDerivAt_id parameter).smul_const (EuclideanSpace.single direction (1 : ℝ)) |>.const_add x
  have phase := (integerWavePhaseLinear wave).hasFDerivAt.comp_hasDerivAt parameter path
  simp only [one_smul,integerWavePhaseLinear_single,Function.comp_def,id_eq] at phase
  have cosine := phase.cos
  have sine := phase.sin
  have paid := ((sine.const_mul (-integerAngularCoefficient wave direction)).smul_const (realRead wave coordinate)).sub
    ((cosine.const_mul (integerAngularCoefficient wave direction)).smul_const (imagRead wave coordinate))
  convert! paid using 1
  simp only [modeRead,integerCosine,integerSine,integerWavePhaseLinear_apply,line,smul_sub,smul_smul]
  congr 2 <;> ring

theorem value_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) :
    HasDerivAt (fun r => value seed time F (line x direction r))
      (gradient seed time F (line x direction parameter) direction) parameter := by
  apply hasDerivAt_pi.mpr
  intro coordinate
  apply (lift seed time).hasFDerivAt.comp_hasDerivAt parameter
  simpa only [fieldRead,gradientRead,Finset.sum_fn] using
    (HasDerivAt.sum (u := F) fun wave _ => modeRead_derivative wave coordinate direction x parameter)

theorem gradient_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) :
    HasDerivAt (fun r => gradient seed time F (line x direction r) direction)
      (second seed time F (line x direction parameter) direction) parameter := by
  apply hasDerivAt_pi.mpr
  intro coordinate
  apply (lift seed time).hasFDerivAt.comp_hasDerivAt parameter
  simpa only [gradientRead,secondRead,Finset.sum_fn] using
    (HasDerivAt.sum (u := F) fun wave _ => modeJet_derivative wave coordinate direction x parameter)

def stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) : Matrix Coordinate Coordinate ℝ := NativeWindowStressHeatGram.gram (value seed time F x)

def gradientStress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) : Matrix Coordinate Coordinate ℝ := NativeWindowStressHeatGram.gradientGram (gradient seed time F x)

theorem stress_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (output input : Coordinate) : stress seed time F x output input =
      ∫ shift, fieldRead F x output (NativeUnifiedCompleteSource.source seed (time-shift))*
        fieldRead F x input (NativeUnifiedCompleteSource.source seed (time-shift)) ∂averageMeasure := by
  rw [stress,NativeWindowStressHeatGram.gram,Matrix.gram_apply,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lift_ae seed time (fieldRead F x output),lift_ae seed time (fieldRead F x input)]
    with shift first last
  change inner ℝ (value seed time F x output shift) (value seed time F x input shift) = _
  simp only [value,first,last]
  exact mul_comm _ _


theorem gradientStress_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (output input : Coordinate) : gradientStress seed time F x output input =
      ∑ j : Coordinate, ∫ shift, gradientRead F x j output (NativeUnifiedCompleteSource.source seed (time-shift))*
        gradientRead F x j input (NativeUnifiedCompleteSource.source seed (time-shift)) ∂averageMeasure := by
  simp only [gradientStress,NativeWindowStressHeatGram.gradientGram,Matrix.sum_apply,
    NativeWindowStressHeatGram.gram,Matrix.gram_apply,L2.inner_def]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [lift_ae seed time (gradientRead F x j output),lift_ae seed time (gradientRead F x j input)]
    with shift first last
  simp only [gradient,first,last]
  exact mul_comm _ _

theorem stress_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (j : Coordinate) (parameter : ℝ) :
    HasDerivAt (fun r => stress seed time F (line x j r))
      (NativeWindowStressHeatGram.cross (value seed time F (line x j parameter))
        (gradient seed time F (line x j parameter) j)) parameter :=
  NativeWindowStressHeatGram.gram_hasDerivAt (value_derivative seed time F x j parameter)

theorem stress_second_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (j : Coordinate) (parameter : ℝ) :
    HasDerivAt (fun r => NativeWindowStressHeatGram.cross (value seed time F (line x j r))
      (gradient seed time F (line x j r) j))
      (NativeWindowStressHeatGram.cross (value seed time F (line x j parameter))
        (second seed time F (line x j parameter) j)+
        (2 : ℝ) • NativeWindowStressHeatGram.gram (gradient seed time F (line x j parameter) j)) parameter := by
  convert! NativeWindowStressHeatGram.cross_hasDerivAt
    (value_derivative seed time F x j parameter) (gradient_derivative seed time F x j parameter) using 1
  ext output input
  simp only [NativeWindowStressHeatGram.cross,NativeWindowStressHeatGram.gram,Matrix.add_apply,
    Matrix.smul_apply,Matrix.gram_apply,smul_eq_mul]
  ring

theorem stress_heat (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (x : PhysicalSpace) :
    NativeWindowStressHeatGram.pairing (-stress seed time F x)
      (-nu.coeff • NativeWindowStressHeatGram.cross (value seed time F x)
        (∑ j : Coordinate, second seed time F x j)) =
      nu.coeff*NativeWindowStressHeatGram.pairing (stress seed time F x)
        (NativeWindowStressHeatGram.secondGram (value seed time F x) (gradient seed time F x) (second seed time F x))-
      2*nu.coeff*Matrix.trace (stress seed time F x*gradientStress seed time F x) :=
  NativeWindowStressHeatGram.heat_pairing _ _ _ _

theorem originalHistory_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    originalHistory seed (step.2.clockAdvance+time) = originalHistory step.1 time := by
  apply Lp.ext
  filter_upwards [originalHistory_ae seed (step.2.clockAdvance+time),originalHistory_ae step.1 time,
    NativeWindowHistoryGNS.average_support] with shift first last inside
  rw [first,last,add_sub_assoc,NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith)]

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) :
    (value seed (step.2.clockAdvance+time) F,gradient seed (step.2.clockAdvance+time) F,
      second seed (step.2.clockAdvance+time) F,stress seed (step.2.clockAdvance+time) F,gradientStress seed (step.2.clockAdvance+time) F) =
    (value step.1 time F,gradient step.1 time F,second step.1 time F,stress step.1 time F,gradientStress step.1 time F) := by
  unfold stress gradientStress value gradient second lift
  rw [originalHistory_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteGramSource
