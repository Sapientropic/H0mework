import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassMeanJet

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMassSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus realValue realField)
open NativeWindowGreenSourceForm (velocity gradientValue fullJet)
open NativeWindowMeanSpatialJet (gradient)
open NativeWindowMassField (State Scalar)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance physicalHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs AddCircle.haarAddCircle.IsAddHaarMeasure
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

def pointJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) (x : Torus) : ℝ :=
  -NativeCanonicalGreenNormalization.densityJet (realValue (velocity seed time) x)
    (fullJet seed time valid x) j.succ/(NativeCanonicalFluidCoframe.density (realValue (velocity seed time) x))^2

def rawJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) (x : Torus) : ℝ :=
  NativeWindowMassReciprocal.derivative (realField (velocity seed time) x) (gradient seed time valid j x)

theorem rawJet_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    rawJet seed time valid j=ᵐ[volume] pointJet seed time valid j := by
  filter_upwards [NativePhysicalFourier.realField_apply (velocity seed time),
    NativeWindowMeanSpatialJet.gradient_ae seed time valid j] with x first last
  simp only [rawJet,first,last,pointJet,NativeWindowMassReciprocal.derivative_apply,
    NativeWindowMassReciprocal.value,NativeCanonicalGreenNormalization.densityJet,fullJet,Fin.cases_succ]
  ring

theorem rawJet_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    MemLp (rawJet seed time valid j) 2 (volume : Measure Torus) := by
  have measured : AEStronglyMeasurable (rawJet seed time valid j) volume := by
    have first:=(Lp.memLp (realField (velocity seed time))).1
    have last:=(Lp.memLp (gradient seed time valid j)).1
    change AEStronglyMeasurable
      (fun x => -(NativeWindowMassReciprocal.value (realField (velocity seed time) x))^2/4*
        inner ℝ (realField (velocity seed time) x) (gradient seed time valid j x)) volume
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.neg_apply,Pi.pow_apply] using!
      ((((NativeWindowMassReciprocal.value_continuous.comp_aestronglyMeasurable first).pow 2).neg.mul_const (4:ℝ)⁻¹).mul
        (first.inner last))
  apply (Lp.memLp (gradient seed time valid j)).of_le_mul measured (c := 1/8)
  filter_upwards with x
  simpa only [rawJet,Real.norm_eq_abs,div_eq_mul_inv,one_mul,mul_comm] using
    NativeWindowMassReciprocal.derivative_bound (realField (velocity seed time) x) (gradient seed time valid j x)

def jet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) : Scalar 2 :=
  (rawJet_memLp seed time valid j).toLp (rawJet seed time valid j)

theorem jet_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    jet seed time valid j=ᵐ[volume] pointJet seed time valid j :=
  (rawJet_memLp seed time valid j).coeFn_toLp.trans (rawJet_ae seed time valid j)

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j : Coordinate) :
    ‖jet seed time valid j‖ ≤ NativeWindowMeanSpatialJet.budget seed horizon/8 := by
  have bound:‖jet seed time valid j‖ ≤ (1/8:ℝ)*‖gradient seed time valid j‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(rawJet_memLp seed time valid j).coeFn_toLp] with x actual
    change jet seed time valid j x=_ at actual
    rw [actual,Real.norm_eq_abs]
    simpa only [rawJet,div_eq_mul_inv,one_mul,mul_comm] using
      NativeWindowMassReciprocal.derivative_bound (realField (velocity seed time) x) (gradient seed time valid j x)
  exact bound.trans ((mul_le_mul_of_nonneg_left (NativeWindowMeanSpatialJet.gradient_bound seed time horizon valid before j)
    (by norm_num : (0:ℝ) ≤ 1/8)).trans_eq (by ring))

def field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Scalar 1 :=
  NativeWindowMassField.field 1 (realField (velocity seed time))

theorem field_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    field seed time=ᵐ[volume] fun x => (NativeCanonicalFluidCoframe.density (realValue (velocity seed time) x))⁻¹ := by
  filter_upwards [NativeWindowMassField.field_ae 1 (realField (velocity seed time)),
    NativePhysicalFourier.realField_apply (velocity seed time)] with x actual source
  change field seed time x=_ at actual
  rw [actual,source]
  rfl

def weakJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) : Scalar 1 :=
  NativeWindowMassField.derivative (realField (velocity seed time)) (gradient seed time valid j)

theorem weakJet_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    weakJet seed time valid j=ᵐ[volume] jet seed time valid j :=
  (NativeWindowMassField.derivative_ae _ _).trans (rawJet_memLp seed time valid j).coeFn_toLp.symm

def translate (j : Coordinate) (z : ℝ) (v : Scalar 1) : Scalar 1 :=
  Lp.compMeasurePreserving (fun x : Torus => x+NativePhysicalTranslation.displacement j z)
    (measurePreserving_add_right volume (NativePhysicalTranslation.displacement j z)) v

theorem shifted_field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j : Coordinate) (z : ℝ) :
    NativeWindowMassField.field 1 (NativeWindowMeanSpatialJet.shifted seed time j z)=translate j z (field seed time) := by
  apply Lp.ext
  have source:=(measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j z)).quasiMeasurePreserving.ae
    (field_ae seed time)
  filter_upwards [NativeWindowMassField.field_ae 1 (NativeWindowMeanSpatialJet.shifted seed time j z),
    NativeWindowMeanSpatialJet.shifted_ae seed time j z,Lp.coeFn_compMeasurePreserving (field seed time)
      (measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j z)),source]
      with x first shifted translated actual
  change translate j z (field seed time) x=_ at translated
  rw [first,shifted,translated]
  exact actual.symm

theorem hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    HasDerivAt (fun z => translate j z (field seed time)) (weakJet seed time valid j) 0 := by
  have actual:=(NativeWindowMassField.hasFDerivAt (NativeWindowMeanSpatialJet.shifted seed time j 0)).comp_hasDerivAt 0
    (NativeWindowMeanSpatialJet.shifted_hasDerivAt seed time valid j)
  simp only [NativeWindowMeanSpatialJet.shifted_zero,Function.comp_def,shifted_field] at actual
  exact actual

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) (j : Coordinate) :
    jet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) j=jet step.1 time (by linarith) j := by
  have same:velocity seed (step.2.clockAdvance+time)=velocity step.1 time := by
    simp only [velocity,NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_next seed 0 step generated time nonnegative]
  have gradientSame:gradient seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) j=
      gradient step.1 time (by linarith) j := by
    simp only [NativeWindowMeanSpatialJet.gradient,NativeWindowMeanSpatialJet.assemble,
      NativeWindowHistoryFirstJet.physicalJet_next seed step generated time nonnegative]
  apply Lp.ext
  filter_upwards [(rawJet_memLp seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) j).coeFn_toLp,
    (rawJet_memLp step.1 time (by linarith) j).coeFn_toLp] with x first last
  change jet seed (step.2.clockAdvance+time) _ j x=_ at first
  change jet step.1 time _ j x=_ at last
  rw [first,last,rawJet,rawJet,same,gradientSame]

end
end SaturationMonoid.NavierStokes.NativeWindowMassSource
