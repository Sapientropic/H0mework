import H0mework.Versions.X.NavierStokes.WindowEnergyJoint.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowJointHeat
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowPressureStrainHistory (correction relative)
open NativePhysicalGradient (multiplier)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem pressure_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) (outside : k ∉ F+F) :
    NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k=0 := by
  by_cases zero : k=0
  · subst k
    change (∑ j : Coordinate,NativeWindowHighTransportResolvent.factor nu j 0*
      NativeWindowHighPressureResolvent.window seed F radius 0 time j output input 0)=0
    simp [NativeWindowHighTransportResolvent.factor,multiplier,complexWavevector]
  · have rate : nu.coeff*integerWaveViscousMultiplier k ≠ 0 := by
      unfold integerWaveViscousMultiplier
      positivity [nu.coeff_pos,integerWaveNormSq_pos zero]
    exact (smul_eq_zero.mp (NativeWindowRetainedPressure.viscous_supported seed F radius time output input k outside)).resolve_left rate

abbrev frequencies := NativeWindowHighTransportHeat.frequencies

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (k : IntegerWavevector) (output input : Coordinate) : ℂ :=
  NativeWindowHighTransportHeat.coefficients seed F radius time k output input-
    NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k

theorem combined_sequence (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) :
    finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)=
      finiteSequence (F+F) (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k output input)+
        NativeWindowHighTransportResolvent.primitive seed F radius 0 time output input-
          NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input := by
  have split : finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)=
      finiteSequence (frequencies F) (fun k => NativeWindowHighTransportHeat.coefficients seed F radius time k output input)-
        NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input := by
    apply lp.ext
    funext k
    simp only [finiteSequence_apply,lp.coeFn_sub,Pi.sub_apply,coefficients]
    by_cases inside : k ∈ frequencies F
    · simp only [if_pos inside]
    · have absent : k ∉ F+F := fun member => inside (Finset.mem_union_left _ member)
      simp only [if_neg inside,pressure_supported seed F radius time output input k absent,sub_self]
  rw [split,NativeWindowHighTransportHeat.combined_sequence seed F radius time closed output input]

theorem combined_field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) :
    field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input))=
      NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input)+
        correction seed F radius time output input := by
  rw [combined_sequence seed F radius time closed output input]
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm ((_+_)-_)=_
  rw [map_sub,map_add]
  have source := NativeWindowFiniteGramFourier.stress_field seed time F closed output input
  change field _=NativeWindowStressHeatSource.physical _ at source
  rw [show (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm
    (finiteSequence (F+F) (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k output input))=
      NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input) from source]
  change _+NativeWindowHighTransportRelative.primitiveField seed F radius 0 time output input-
    field (NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input)=_
  rw [correction]
  abel

theorem relative_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) :
    relative seed F radius time output input=
      -field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)) := by
  rw [combined_field seed F radius time closed output input]
  unfold relative NativeWindowStressHeatBalance.sigma
  abel

theorem heat_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) :
    NativeWindowJointNormalForm.heatRate seed F radius time output input=
      -nu.coeff • (∑ j : Coordinate,field (finiteJet (frequencies F)
        (fun k => coefficients seed F radius time k output input) j 2))+
          (2*nu.coeff) • NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input) := by
  rw [NativeWindowJointNormalForm.heatRate,NativeWindowHighTransportHeat.heat_original seed F radius time closed output input]
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  have scaling (scalar : ℝ) (value : ScalarField) : (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (scalar • value)=
      scalar • (UnitAddTorus.mFourierBasis (d := Coordinate)).repr value :=
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.restrictScalars ℝ).map_smul scalar value
  simp only [map_sub,map_add,scaling,lp.coeFn_sub,lp.coeFn_add,lp.coeFn_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    NativeWindowHighTransportHeat.laplacian_fourier]
  have pressure := NativeWindowRetainedPressure.viscousPrimitive_fourier seed F radius time output input k
  rw [← UnitAddTorus.mFourierBasis_repr] at pressure
  rw [pressure,combined_sequence seed F radius time closed output input,
    NativeWindowHighTransportHeat.combined_sequence seed F radius time closed output input]
  simp only [lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul]
  ring

def dirichlet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    ‖field (finiteJet (frequencies F) (fun k => coefficients seed F radius time k output input) j 1)‖^2

def crossWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (correction seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input))

theorem heatWork_identity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) :
    NativeWindowJointNormalForm.heatWork seed F radius time=
      -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)-
        2*nu.coeff*crossWork seed F radius time := by
  have paid := tensor_heat_pairing nu.coeff (frequencies F) (coefficients seed F radius time)
    (fun output input => NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input))
  simp only [← heat_original seed F radius time closed,
    combined_field seed F radius time closed,inner_add_left,Finset.sum_add_distrib,
    NativeWindowStressHeatSource.interaction_inner] at paid
  have same (output input : Coordinate) : -(NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress seed time F output input)+correction seed F radius time output input)=
      relative seed F radius time output input := by unfold relative NativeWindowStressHeatBalance.sigma; abel
  simp only [same] at paid
  change NativeWindowJointNormalForm.heatWork seed F radius time=
    -nu.coeff*dirichlet seed F radius time-2*nu.coeff*((∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)+crossWork seed F radius time) at paid
  exact paid.trans (by ring)

theorem gradient_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (j output input : Coordinate) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j displacement)
      (relative seed F radius time output input))
      (-field (finiteJet (frequencies F) (fun k => coefficients seed F radius time k output input) j 1)) 0 := by
  have source := (finiteJet_hasDerivAt (frequencies F) (fun k => coefficients seed F radius time k output input) j 0).neg
  simp only [finiteJet,pow_zero,one_mul] at source
  rw [relative_original seed F radius time closed output input]
  simpa only [NativePhysicalTranslation.translate,map_neg,Pi.neg_apply] using! source

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem dirichlet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    dirichlet seed F radius (step.2.clockAdvance+time)=dirichlet step.1 F radius time := by
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  have before := gradient_original seed F radius (step.2.clockAdvance+time) closed j output input
  rw [NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F] at before
  exact congrArg (fun value : ScalarField => ‖value‖^2)
    (neg_injective (before.unique (gradient_original step.1 F radius time closed j output input)))

end
end SaturationMonoid.NavierStokes.NativeWindowJointHeat
