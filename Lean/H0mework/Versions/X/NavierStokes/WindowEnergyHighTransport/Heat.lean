import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportHeat
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativePhysicalGradient (multiplier)
open NativeWindowHighTransportResolvent NativeWindowHighTransportRelative
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def frequencies (F : Finset IntegerWavevector) : Finset IntegerWavevector := (F+F)∪(F+(F+F))

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (k : IntegerWavevector) (output input : Coordinate) : ℂ :=
  NativeWindowFiniteGramFourier.coefficients seed time F k output input+primitive seed F radius 0 time output input k

theorem combined_sequence (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)=
      finiteSequence (F+F) (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k output input)+
        primitive seed F radius 0 time output input := by
  classical
  apply lp.ext
  funext k
  simp only [finiteSequence_apply,lp.coeFn_add,Pi.add_apply,frequencies,Finset.mem_union,coefficients]
  by_cases first : k∈F+F <;> by_cases last : k∈F+(F+F)
  · simp [first,last]
  · simp [first,last,primitive_supported seed F radius 0 time output input k last]
  · simp [first,last,NativeWindowFiniteGramFourier.coefficients_supported seed time F closed k first output input]
  · simp [first,last,primitive_supported seed F radius 0 time output input k last]

theorem combined_field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input))=
      NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input)+
        primitiveField seed F radius 0 time output input := by
  rw [combined_sequence seed F radius time closed output input]
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (_+_)=_
  rw [map_add]
  have source := NativeWindowFiniteGramFourier.stress_field seed time F closed output input
  change field _=NativeWindowStressHeatSource.physical _ at source
  rw [show (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm
    (finiteSequence (F+F) (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k output input))=
    NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input) from source]
  rfl

theorem relative_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    relative seed F radius time output input=
      -field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)) := by
  rw [combined_field seed F radius time closed output input]
  unfold relative NativeWindowStressHeatBalance.sigma
  abel

theorem multiplier_square_sum (k : IntegerWavevector) : (∑ j : Coordinate,multiplier k j^2)=-(integerWaveViscousMultiplier k : ℝ) := by
  simp only [multiplier,complexWavevector,mul_pow,Complex.I_sq,neg_one_mul,integerWaveViscousMultiplier,integerWaveNormSq,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sum,← Finset.mul_sum]
  ring

theorem laplacian_fourier (G : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (k : IntegerWavevector) :
    (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (∑ j : Coordinate,field (finiteJet G a j 2)) k=
      -(integerWaveViscousMultiplier k : ℝ)*finiteSequence G a k := by
  simp only [map_sum,lp.coeFn_sum,Finset.sum_apply,field,LinearIsometryEquiv.apply_symm_apply,
    finiteJet,finiteSequence_apply]
  by_cases inside : k∈G
  · simp only [if_pos inside,← Finset.sum_mul,multiplier_square_sum]
  · simp only [if_neg inside,Finset.sum_const_zero,mul_zero]

theorem heat_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+
      primitiveViscous seed F radius time output input=
      -nu.coeff • (∑ j : Coordinate,field (finiteJet (frequencies F)
        (fun k => coefficients seed F radius time k output input) j 2))+
      (2*nu.coeff) • NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input) := by
  rw [NativeWindowStressHeatSource.heat,map_add,map_smul,map_smul,NativeWindowStressHeatSource.laplacian_field seed time F closed output input]
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  have scaling (scalar : ℝ) (value : ScalarField) : (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (scalar • value)=
      scalar • (UnitAddTorus.mFourierBasis (d := Coordinate)).repr value :=
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.restrictScalars ℝ).map_smul scalar value
  simp only [map_add,scaling,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,laplacian_fourier]
  have actual := primitiveViscous_fourier seed F radius time output input k
  rw [← UnitAddTorus.mFourierBasis_repr] at actual
  rw [actual,combined_sequence seed F radius time closed output input]
  simp only [lp.coeFn_add,Pi.add_apply,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul]
  ring

def dirichlet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    ‖field (finiteJet (frequencies F) (fun k => coefficients seed F radius time k output input) j 1)‖^2

def crossWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (primitiveField seed F radius 0 time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input))

theorem heatWork_identity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    NativeWindowHighTransportNormalForm.heatWork seed F radius time=
      -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)-
        2*nu.coeff*crossWork seed F radius time := by
  have paid := tensor_heat_pairing nu.coeff (frequencies F) (coefficients seed F radius time)
    (fun output input => NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input))
  simp only [← heat_original seed F radius time closed,
    combined_field seed F radius time closed,inner_add_left,Finset.sum_add_distrib,
    NativeWindowStressHeatSource.interaction_inner] at paid
  have same (output input : Coordinate) : -(NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress seed time F output input)+primitiveField seed F radius 0 time output input)=
      relative seed F radius time output input := by unfold relative NativeWindowStressHeatBalance.sigma; abel
  simp only [same] at paid
  change NativeWindowHighTransportNormalForm.heatWork seed F radius time=
    -nu.coeff*dirichlet seed F radius time-2*nu.coeff*((∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)+crossWork seed F radius time) at paid
  exact paid.trans (by ring)

theorem gradient_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j output input : Coordinate) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j displacement)
      (relative seed F radius time output input))
      (-field (finiteJet (frequencies F) (fun k => coefficients seed F radius time k output input) j 1)) 0 := by
  have source := (finiteJet_hasDerivAt (frequencies F) (fun k => coefficients seed F radius time k output input) j 0).neg
  simp only [finiteJet,pow_zero,one_mul] at source
  rw [relative_original seed F radius time closed output input]
  simpa only [NativePhysicalTranslation.translate,map_neg,Pi.neg_apply] using! source


theorem source_energy_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      (∀ k,k∈F →waveNeg k∈F) →
      deriv (energy seed F radius) time+nu.coeff*dirichlet seed F radius time+
        2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point) ≤
      NativeWindowHighTransportNormalForm.retainedWork seed F radius time+
        NativeWindowHighTransportNormalForm.preparationWork seed F radius time+energy seed F radius time+epsilon-
        2*nu.coeff*crossWork seed F radius time := by
  obtain ⟨low,paid⟩ := NativeWindowHighTransportNormalForm.energy_uniform_feed seed horizon nonnegative epsilon positive
  refine ⟨low,fun radius above F time inside closed => ?_⟩
  have generated := paid radius above F time inside closed
  rw [heatWork_identity seed F radius time closed] at generated
  linarith only [generated]


def gradientHistory (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (j i : Coordinate) : NativeWindowFiniteGramSource.H :=
  NativeWindowFiniteGramSource.lift seed time ((ContinuousMap.evalCLM ℝ point).comp (NativeWindowStressHeatSource.jetRead F j 1 i))

theorem gradientHistory_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (j i : Coordinate) : gradientHistory seed time F point j i =ᵐ[NativeForwardWindowPairingReadout.averageMeasure]
      fun shift => NativeWindowCrossHistoryAction.gradient seed F (time-shift) j i point :=
  NativeWindowFiniteGramSource.lift_ae seed time ((ContinuousMap.evalCLM ℝ point).comp (NativeWindowStressHeatSource.jetRead F j 1 i))

theorem diffusion_history (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (output input : Coordinate) : NativeWindowStressHeatSource.diffusion seed time F output input point=
      ∑ j : Coordinate,inner ℝ (gradientHistory seed time F point j output) (gradientHistory seed time F point j input) := by
  simp only [NativeWindowStressHeatSource.diffusion,ContinuousMap.sum_apply,NativeWindowStressHeatSource.productAverage_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientHistory_original seed time F point j output,
    gradientHistory_original seed time F point j input] with shift first last
  rw [first,last]
  change _=inner ℝ (NativeWindowStressHeatSource.jetRead F j 1 output (NativeUnifiedCompleteSource.source seed (time-shift)) point)
    (NativeWindowStressHeatSource.jetRead F j 1 input (NativeUnifiedCompleteSource.source seed (time-shift)) point)
  simp only [RCLike.inner_apply,conj_trivial]
  ring

theorem crossWork_history (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    crossWork seed F radius time=∑ output : Coordinate,∑ input : Coordinate,
      ∫ point : Torus,(primitiveField seed F radius 0 time output input point).re*
        ∑ j : Coordinate,inner ℝ (gradientHistory seed time F point j output) (gradientHistory seed time F point j input) := by
  unfold crossWork
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
    ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (NativeWindowStressHeatSource.diffusion seed time F output input))] with point actual
  change inner ℝ (primitiveField seed F radius 0 time output input point)
    (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (NativeWindowStressHeatSource.diffusion seed time F output input)).toLp 2 volume ℂ point)=_
  rw [actual,← diffusion_history seed time F point output input]
  change inner ℝ (primitiveField seed F radius 0 time output input point)
    (NativeWindowStressHeatSource.diffusion seed time F output input point : ℂ)=_
  simp [Complex.inner,mul_comm]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportHeat
