import H0mework.Versions.X.NavierStokes.WindowStressHeat.Fourier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowStressHeatSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalGradient NativeCompleteStressAction NativeForwardWindowPairingReadout
open NativeWindowFiniteGramSource
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem ofReal_apply (field : C(Torus,ℝ)) (point : Torus) :
    (Complex.ofRealCLM.compLeftContinuous ℝ Torus) field point = (field point : ℂ) := rfl

private theorem re_apply (field : C(Torus,ℂ)) (point : Torus) :
    (Complex.reCLM.compLeftContinuous ℝ Torus) field point = (field point).re := rfl

def polynomial (F : Finset IntegerWavevector) (coefficient : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) : C(Torus,ℂ) :=
  ∑ wave ∈ F, (multiplier wave direction^order*coefficient wave) • UnitAddTorus.mFourier wave

theorem polynomial_field (F : Finset IntegerWavevector) (coefficient : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) :
    (polynomial F coefficient direction order).toLp 2 volume ℂ = NativeWindowStressHeatEnergy.field
      (NativeWindowStressHeatEnergy.finiteJet F coefficient direction order) := by
  simp only [polynomial,NativeWindowStressHeatEnergy.field,NativeWindowStressHeatEnergy.finiteJet,
    NativeWindowStressHeatEnergy.finiteSequence,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro wave _
  have split (z : ℂ) : lp.single 2 wave z = z • lp.single (E := fun _ : IntegerWavevector => ℂ) 2 wave 1 := by
    simpa only [smul_eq_mul,mul_one] using lp.single_smul (E := fun _ : IntegerWavevector => ℂ) 2 wave z (1 : ℂ)
  rw [split,map_smul,HilbertBasis.repr_symm_single]
  apply congrArg (fun value : ScalarField => (multiplier wave direction^order*coefficient wave) • value)
  rw [show UnitAddTorus.mFourierBasis wave = UnitAddTorus.mFourierLp 2 wave from congrFun UnitAddTorus.coe_mFourierBasis wave]

theorem circle_line (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) :
    NativeFullOrderSynthesis.circlePoint (line x direction parameter) =
      NativeFullOrderSynthesis.circlePoint x+NativePhysicalTranslation.displacement direction parameter := by
  funext coordinate
  simp only [NativeFullOrderSynthesis.circlePoint,line,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
    Pi.add_apply,NativePhysicalTranslation.displacement]
  by_cases same : coordinate = direction
  · subst coordinate
    simp
  · simp [same]

theorem character_line (wave : IntegerWavevector) (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) :
    HasDerivAt (fun r => UnitAddTorus.mFourier wave (NativeFullOrderSynthesis.circlePoint (line x direction r)))
      (multiplier wave direction*UnitAddTorus.mFourier wave
        (NativeFullOrderSynthesis.circlePoint (line x direction parameter))) parameter := by
  simp only [circle_line,NativePhysicalTranslation.character_add,NativePhysicalTranslation.character_displacement]
  convert! (NativeSpatialTranslation.phase_hasDerivAt direction wave parameter).const_mul
    (UnitAddTorus.mFourier wave (NativeFullOrderSynthesis.circlePoint x)) using 1
  ring

theorem polynomial_line (F : Finset IntegerWavevector) (coefficient : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => polynomial F coefficient direction order
      (NativeFullOrderSynthesis.circlePoint (line x direction r)))
      (polynomial F coefficient direction (order+1)
        (NativeFullOrderSynthesis.circlePoint (line x direction parameter))) parameter := by
  have generated := HasDerivAt.sum (u := F) fun wave _ =>
    (character_line wave x direction parameter).const_mul (multiplier wave direction^order*coefficient wave)
  convert! generated using 1
  · simp only [polynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_fn]
  · simp only [polynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,pow_succ]
    apply Finset.sum_congr rfl
    intro wave _
    ring

def jetRead (F : Finset IntegerWavevector) (direction : Coordinate) (order : ℕ)
    (coordinate : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ Torus).comp
    (∑ wave ∈ F, ((ContinuousLinearMap.toSpanSingleton ℂ
      (multiplier wave direction^order • UnitAddTorus.mFourier wave)).restrictScalars ℝ).comp
        (velocityRead wave coordinate))

theorem jetRead_apply (F : Finset IntegerWavevector) (direction : Coordinate) (order : ℕ)
    (coordinate : Coordinate) (state : FullSpace) (point : Torus) :
    jetRead F direction order coordinate state point =
      (polynomial F (fun wave => velocityRead wave coordinate state) direction order point).re := by
  change (((∑ wave ∈ F, ((ContinuousLinearMap.toSpanSingleton ℂ
      (multiplier wave direction^order • UnitAddTorus.mFourier wave)).restrictScalars ℝ).comp
        (velocityRead wave coordinate)) state) point).re = _
  simp only [sum_apply,ContinuousMap.sum_apply,polynomial,ContinuousMap.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro wave _
  change velocityRead wave coordinate state*(multiplier wave direction^order*UnitAddTorus.mFourier wave point) = _
  ring

theorem jetRead_zero (F : Finset IntegerWavevector) (direction coordinate : Coordinate) :
    jetRead F direction 0 coordinate = NativeWindowFiniteGramFourier.read F coordinate := by
  simp only [jetRead,pow_zero,one_smul,NativeWindowFiniteGramFourier.read,
    NativeWindowFiniteGramFourier.complexRead]

theorem jetRead_line (F : Finset IntegerWavevector) (direction : Coordinate) (order : ℕ)
    (coordinate : Coordinate) (state : FullSpace) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => jetRead F direction order coordinate state
      (NativeFullOrderSynthesis.circlePoint (line x direction r)))
      (jetRead F direction (order+1) coordinate state
        (NativeFullOrderSynthesis.circlePoint (line x direction parameter))) parameter := by
  simp only [jetRead_apply]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt parameter
    (polynomial_line F (fun wave => velocityRead wave coordinate state) direction order x parameter)

theorem jetRead_first (F : Finset IntegerWavevector) (direction coordinate : Coordinate)
    (state : FullSpace) (x : PhysicalSpace) :
    jetRead F direction 1 coordinate state (NativeFullOrderSynthesis.circlePoint x) =
      gradientRead F x direction coordinate state := by
  have actual := jetRead_line F direction 0 coordinate state x 0
  simp only [jetRead_zero,NativeWindowFiniteGramFourier.read_physical,line,zero_smul,add_zero] at actual
  have original := (HasDerivAt.sum (u := F) fun wave _ =>
    modeRead_derivative wave coordinate direction x 0).clm_apply (hasDerivAt_const 0 state)
  simp only [zero_smul,add_zero,line,Finset.sum_fn,sum_apply,
    map_zero] at original
  simp only [fieldRead,gradientRead,sum_apply] at actual ⊢
  exact actual.unique original

def productAverage (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (left right : FullSpace →L[ℝ] C(Torus,ℝ)) : C(Torus,ℝ) :=
  ∫ shift, left (NativeUnifiedCompleteSource.source seed (time-shift))*
    right (NativeUnifiedCompleteSource.source seed (time-shift)) ∂averageMeasure

theorem product_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (left right : FullSpace →L[ℝ] C(Torus,ℝ)) :
    Integrable (fun shift => left (NativeUnifiedCompleteSource.source seed (time-shift))*
      right (NativeUnifiedCompleteSource.source seed (time-shift))) averageMeasure := by
  apply Integrable.of_bound (((left.integrable_comp (original_integrable seed time)).aestronglyMeasurable).mul
    ((right.integrable_comp (original_integrable seed time)).aestronglyMeasurable))
      (‖left‖*‖right‖*NativeUnifiedCompleteSource.budget seed^2)
  filter_upwards with shift
  apply (norm_mul_le _ _).trans
  have bound (read : FullSpace →L[ℝ] C(Torus,ℝ)) :
      ‖read (NativeUnifiedCompleteSource.source seed (time-shift))‖ ≤ ‖read‖*NativeUnifiedCompleteSource.budget seed :=
    (read.le_opNorm _).trans (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed _) (norm_nonneg _))
  exact (mul_le_mul (bound left) (bound right) (norm_nonneg _) ((norm_nonneg _).trans (bound left))).trans_eq (by ring)

theorem productAverage_apply (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (left right : FullSpace →L[ℝ] C(Torus,ℝ)) (point : Torus) :
    productAverage seed time left right point = ∫ shift,
      left (NativeUnifiedCompleteSource.source seed (time-shift)) point*
      right (NativeUnifiedCompleteSource.source seed (time-shift)) point ∂averageMeasure :=
  ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (product_integrable seed time left right)).symm

def diffusion (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∑ direction : Coordinate, productAverage seed time (jetRead F direction 1 output) (jetRead F direction 1 input)

theorem diffusion_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) (x : PhysicalSpace) :
    diffusion seed time F output input (NativeFullOrderSynthesis.circlePoint x) =
      gradientStress seed time F x output input := by
  simp only [diffusion,ContinuousMap.sum_apply,productAverage_apply,jetRead_first,gradientStress_original]

theorem circle_surjective : Function.Surjective NativeFullOrderSynthesis.circlePoint := by
  intro point
  choose representative original using fun coordinate => QuotientAddGroup.mk_surjective (point coordinate)
  refine ⟨WithLp.toLp 2 representative, ?_⟩
  funext coordinate
  exact original coordinate

def stressJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (direction : Coordinate) (order : ℕ) (output input : Coordinate) : C(Torus,ℂ) :=
  polynomial (F+F) (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input) direction order

theorem stressJet_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (direction output input : Coordinate) :
    stressJet seed time F direction 0 output input =
      (Complex.ofRealCLM.compLeftContinuous ℝ Torus) (NativeWindowFiniteGramFourier.stress seed time F output input) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (volume : Measure Torus)
  rw [stressJet,polynomial_field]
  simp only [NativeWindowStressHeatEnergy.finiteJet,pow_zero,one_mul]
  exact NativeWindowFiniteGramFourier.stress_field seed time F closed output input

theorem stressJet_first (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (direction output input : Coordinate) (x : PhysicalSpace) :
    stressJet seed time F direction 1 output input (NativeFullOrderSynthesis.circlePoint x) =
      ((NativeWindowStressHeatGram.cross (value seed time F x) (gradient seed time F x direction)) output input : ℂ) := by
  have actual := polynomial_line (F+F) (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input)
    direction 0 x 0
  change HasDerivAt (fun r => stressJet seed time F direction 0 output input (NativeFullOrderSynthesis.circlePoint (line x direction r)))
    (stressJet seed time F direction 1 output input (NativeFullOrderSynthesis.circlePoint (line x direction 0))) 0 at actual
  simp only [stressJet_zero seed time F closed,ofReal_apply,
    NativeWindowFiniteGramFourier.stress_physical,line,zero_smul,add_zero] at actual
  have generated := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp (stress_derivative seed time F x direction 0) output) input)
  simp only [line,zero_smul,add_zero,Function.comp_def,Complex.ofRealCLM_apply] at generated
  exact actual.unique generated

theorem stressJet_second (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (direction output input : Coordinate) (x : PhysicalSpace) :
    stressJet seed time F direction 2 output input (NativeFullOrderSynthesis.circlePoint x) =
      ((NativeWindowStressHeatGram.cross (value seed time F x) (second seed time F x direction)+
        (2 : ℝ) • NativeWindowStressHeatGram.gram (gradient seed time F x direction)) output input : ℂ) := by
  have actual := polynomial_line (F+F) (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input)
    direction 1 x 0
  change HasDerivAt (fun r => stressJet seed time F direction 1 output input (NativeFullOrderSynthesis.circlePoint (line x direction r)))
    (stressJet seed time F direction 2 output input (NativeFullOrderSynthesis.circlePoint (line x direction 0))) 0 at actual
  simp only [stressJet_first seed time F closed,line,zero_smul,add_zero] at actual
  have generated := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp (stress_second_derivative seed time F x direction 0) output) input)
  simp only [line,zero_smul,add_zero,Function.comp_def,Complex.ofRealCLM_apply] at generated
  exact actual.unique generated

def laplacian (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∑ direction : Coordinate, (Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input)

theorem laplacian_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) (x : PhysicalSpace) :
    laplacian seed time F output input (NativeFullOrderSynthesis.circlePoint x) =
      NativeWindowStressHeatGram.secondGram (value seed time F x) (gradient seed time F x) (second seed time F x) output input := by
  simp only [laplacian,ContinuousMap.sum_apply,re_apply,
    stressJet_second seed time F closed,Complex.ofReal_re,NativeWindowStressHeatGram.secondGram,Matrix.sum_apply]

def heat (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  -nu.coeff • laplacian seed time F output input+(2*nu.coeff) • diffusion seed time F output input

theorem heat_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) (x : PhysicalSpace) :
    heat seed time F output input (NativeFullOrderSynthesis.circlePoint x) =
      (-nu.coeff • NativeWindowStressHeatGram.cross (value seed time F x)
        (∑ direction : Coordinate, second seed time F x direction)) output input := by
  simp only [heat,ContinuousMap.add_apply,ContinuousMap.smul_apply,laplacian_physical seed time F closed,
    diffusion_physical,NativeWindowStressHeatGram.secondGram_split,gradientStress,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

def physical : C(Torus,ℝ) →L[ℝ] ScalarField :=
  ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).restrictScalars ℝ).comp
    (Complex.ofRealCLM.compLeftContinuous ℝ Torus)

theorem physical_inner (left right : C(Torus,ℝ)) : inner ℝ (physical left) (physical right) =
    ∫ point : Torus, left point*right point := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) left),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) right)] with point first last
  change inner ℝ (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) left).toLp 2 volume ℂ point)
    (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) right).toLp 2 volume ℂ point) = _
  rw [first,last,ofReal_apply,ofReal_apply]
  simp [Complex.inner,mul_comm]

def interaction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    NativeWindowFiniteGramFourier.stress seed time F output input*diffusion seed time F output input

theorem interaction_nonnegative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) : 0 ≤ interaction seed time F point := by
  obtain ⟨x,rfl⟩ := circle_surjective point
  simp only [interaction,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
    NativeWindowFiniteGramFourier.stress_physical,diffusion_physical]
  change 0 ≤ NativeWindowStressHeatGram.pairing (NativeWindowStressHeatGram.gram (value seed time F x))
    (NativeWindowStressHeatGram.gradientGram (gradient seed time F x))
  rw [NativeWindowStressHeatGram.pairing_gradient_trace]
  exact NativeWindowStressHeatGram.trace_gradient_nonnegative _ _

theorem interaction_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) : interaction seed time F (NativeFullOrderSynthesis.circlePoint x) =
      Matrix.trace (stress seed time F x*gradientStress seed time F x) := by
  simp only [interaction,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
    NativeWindowFiniteGramFourier.stress_physical,diffusion_physical]
  exact NativeWindowStressHeatGram.pairing_gradient_trace _ _

theorem interaction_inner (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) :
    (∑ output : Coordinate, ∑ input : Coordinate,
      inner ℝ (physical (NativeWindowFiniteGramFourier.stress seed time F output input))
        (physical (diffusion seed time F output input))) = ∫ point, interaction seed time F point := by
  simp only [physical_inner]
  have paid (output input : Coordinate) : Integrable (fun point : Torus =>
      NativeWindowFiniteGramFourier.stress seed time F output input point*diffusion seed time F output input point) :=
    (NativeWindowFiniteGramFourier.stress seed time F output input*diffusion seed time F output input).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [interaction,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
  rw [integral_finsetSum Finset.univ (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid output input))]
  apply Finset.sum_congr rfl
  intro output _
  exact (integral_finsetSum Finset.univ (fun input _ => paid output input)).symm

theorem laplacian_field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    physical (laplacian seed time F output input) = ∑ direction : Coordinate,
      NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteJet (F+F)
        (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input) direction 2) := by
  rw [laplacian,map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  rw [← polynomial_field]
  have real : (Complex.ofRealCLM.compLeftContinuous ℝ Torus)
      ((Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input)) =
        stressJet seed time F direction 2 output input := by
    ext point
    obtain ⟨x,rfl⟩ := circle_surjective point
    simp only [ofReal_apply,re_apply,stressJet_second seed time F closed,Complex.ofReal_re]
  change ((Complex.ofRealCLM.compLeftContinuous ℝ Torus)
    ((Complex.reCLM.compLeftContinuous ℝ Torus) (stressJet seed time F direction 2 output input))).toLp 2 volume ℂ = _
  rw [real]
  rfl

def dirichlet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ direction : Coordinate, ∑ output : Coordinate, ∑ input : Coordinate,
    ‖NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteJet (F+F)
      (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input) direction 1)‖^2

def heatWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    inner ℝ (-physical (NativeWindowFiniteGramFourier.stress seed time F output input))
      (physical (heat seed time F output input))

theorem stress_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (direction output input : Coordinate) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate
      (NativePhysicalTranslation.displacement direction displacement)
        (physical (NativeWindowFiniteGramFourier.stress seed time F output input)))
      (NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteJet (F+F)
        (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input) direction 1)) 0 := by
  have generated := NativeWindowStressHeatEnergy.finiteJet_hasDerivAt (F+F)
    (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input) direction 0
  simpa only [NativeWindowStressHeatEnergy.finiteJet,pow_zero,one_mul,
    NativeWindowFiniteGramFourier.stress_field seed time F closed] using! generated

theorem heatWork_identity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    heatWork seed time F = -nu.coeff*dirichlet seed time F-
      2*nu.coeff*(∫ point, interaction seed time F point) := by
  have source (output input : Coordinate) : NativeWindowStressHeatEnergy.field
      (NativeWindowStressHeatEnergy.finiteSequence (F+F)
        (fun wave => NativeWindowFiniteGramFourier.coefficients seed time F wave output input)) =
      physical (NativeWindowFiniteGramFourier.stress seed time F output input) :=
    NativeWindowFiniteGramFourier.stress_field seed time F closed output input
  have paid := NativeWindowStressHeatEnergy.tensor_heat_pairing nu.coeff (F+F)
    (NativeWindowFiniteGramFourier.coefficients seed time F) (fun output input => physical (diffusion seed time F output input))
  simp only [source,interaction_inner] at paid
  simpa only [heatWork,heat,map_add,map_smul,laplacian_field seed time F closed,dirichlet] using! paid

theorem heatWork_coercive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    heatWork seed time F ≤ -nu.coeff*dirichlet seed time F := by
  rw [heatWork_identity seed time F closed]
  exact sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num) nu.coeff_pos.le)
    (integral_nonneg (interaction_nonnegative seed time F)))

theorem cube_heatWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (radius : ℕ) :
    let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius
    heatWork seed time F = -nu.coeff*dirichlet seed time F-2*nu.coeff*(∫ point, interaction seed time F point) ∧
      heatWork seed time F ≤ -nu.coeff*dirichlet seed time F :=
  ⟨heatWork_identity seed time _ (NativeWindowFiniteGramFourier.cube_closed radius),
    heatWork_coercive seed time _ (NativeWindowFiniteGramFourier.cube_closed radius)⟩

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem productAverage_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (left right : FullSpace →L[ℝ] C(Torus,ℝ)) :
    productAverage seed (step.2.clockAdvance+time) left right = productAverage step.1 time left right := by
  unfold productAverage
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift inside
  rw [add_sub_assoc,NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith)]

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) :
    (heat seed (step.2.clockAdvance+time) F,diffusion seed (step.2.clockAdvance+time) F,
      dirichlet seed (step.2.clockAdvance+time) F,heatWork seed (step.2.clockAdvance+time) F,
      interaction seed (step.2.clockAdvance+time) F) =
    (heat step.1 time F,diffusion step.1 time F,dirichlet step.1 time F,heatWork step.1 time F,interaction step.1 time F) := by
  unfold heatWork interaction heat diffusion dirichlet laplacian stressJet NativeWindowFiniteGramFourier.coefficients
  simp only [NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative,
    productAverage_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowStressHeatSource
