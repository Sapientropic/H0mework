import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Spatial
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Fourier
import H0mework.Versions.X.NavierStokes.PhysicalReadout.Continuous
import H0mework.Versions.X.NavierStokes.NativeWorkSource.ReadoutPhysicalTranslationMaterial

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderPhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryAllOrderWord (value retained)
open NativeWindowHistoryAllOrderPrincipal (weight)
open NativeWindowHistorySchurAction (effective)
open NativePhysicalFourier NativeEndpointVelocityCarrier
open PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy (FixedMatterSpatialWordIndex)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

abbrev Field := Lp PhysicalSpace 2 (volume : Measure Torus)

def read : wholePhysical →L[ℝ] Field := NativePhysicalSource.physicalCLM.comp wholePhysical.subtypeL

theorem read_norm (v : wholePhysical) : ‖read v‖ = ‖v‖ :=
  NativePhysicalSource.physicalCLM_norm v.val v.property.2

theorem read_pairing (u v : wholePhysical) : inner ℝ (read u) (read v) = inner ℝ u v := by
  have plus := norm_add_sq_real (read u) (read v)
  rw [← map_add, read_norm, read_norm, read_norm] at plus
  linarith only [plus, norm_add_sq_real u v]

def field (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) : Field :=
  read (value seed M word time)

theorem actual_time_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) :
    HasDerivAt (field seed M word)
      (read (effective seed M time (value seed M word time) + retained seed M word time)) time :=
  read.hasFDerivAt.comp_hasDerivAt time (NativeWindowHistoryAllOrderWord.value_hasDerivAt seed M word time)

theorem word_row (M : ℕ) (word : List Coordinate) (v : wholePhysical)
    (k : IntegerWavevector) (i : Coordinate) :
    wholeVelocity (NativeWindowHistorySpatialWords.fiber M word v).val k i =
      NativeWindowStageNineWords.multiplier word k *
        complexSharpSupportProjection (modes M) (wholeVelocity v.val) k i := by
  change NativeWindowAbsoluteTimeFourier.rowMap k i
    (NativePhysicalPairing.includeCLM (modes M) (modes_closed M)
      (NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) word
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))) = _
  rw [NativeWindowAbsoluteTimeFourier.row_include,NativeWindowStageNineWords.word_row]
  rfl

theorem word_cons (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (j : Coordinate) (k : IntegerWavevector) (i : Coordinate) :
    wholeVelocity (value seed M (j::word) time).val k i =
      NativePhysicalGradient.multiplier k j * wholeVelocity (value seed M word time).val k i := by
  simp only [value,word_row,NativeWindowStageNineWords.multiplier]
  ring

theorem scalar_ordinary_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (j i : Coordinate) :
    HasDerivAt (fun z => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j z)
      (scalarField (wholeVelocity (value seed M word time).val) i))
      (scalarField (wholeVelocity (value seed M (j::word) time).val) i) 0 := by
  let inverse : ScalarSequence →L[ℝ] ScalarField :=
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have derivative := NativeSpatialTranslation.translate_hasDerivAt_zero j
    (scalarSequence (wholeVelocity (value seed M word time).val) i)
    (scalarSequence (wholeVelocity (value seed M (j::word) time).val) i)
    (fun k => word_cons seed M word time j k i)
  have actual := inverse.hasFDerivAt.comp_hasDerivAt 0 derivative
  have source (z : ℝ) : NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j z)
      (scalarField (wholeVelocity (value seed M word time).val) i) =
      inverse (NativeSpatialTranslation.translate j z
        (scalarSequence (wholeVelocity (value seed M word time).val) i)) := by
    rw [NativePhysicalTranslation.translate_eq_fourier, scalarField, LinearIsometryEquiv.apply_symm_apply]
    rfl
  simp only [source]
  exact actual

theorem ordinary_spatial_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (j : Coordinate) :
    HasDerivAt (fun z => NativeMaterialSpatialAction.action (NativePhysicalTranslation.displacement j z)
      (field seed M word time)) (field seed M (j::word) time) 0 := by
  have each (i : Coordinate) :=
    ((NativeMaterialSpatialAction.coordinateEmbedding i).compLpL 2 (volume : Measure Torus)).hasFDerivAt.comp_hasDerivAt 0
      (scalar_ordinary_derivative seed M word time j i)
  have actual := ((each 0).add (each 1)).add (each 2)
  have realized (directions : List Coordinate) : field seed M directions time =
      NativeMaterialSpatialAction.assemble (scalarField (wholeVelocity (value seed M directions time).val)) :=
    (NativeMaterialSpatialAction.assemble_source _).symm
  simp only [realized,NativeMaterialSpatialAction.action_assemble]
  exact actual

theorem empty_word_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    field seed M [] time = NativePhysicalSource.physicalCLM
      (NativeWindowHistoryMeanTime.read M (NativeForwardWindowSource.source seed time).fst) := by
  have empty : value seed M [] time =
      NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M) := by
    exact NativeWindowHistoryMeanPhysicalJet.include_mean seed M time
  rw [field,empty]
  change NativePhysicalSource.physicalCLM
    (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)).val = _
  rw [NativeWindowHistoryMeanTime.source_mean]
  simp only [NativeWindowHistoryMeanTime.jet,NativeForwardWindowEvolution.velocityJet,
    NativeForwardWindowJets.jet_zero]

theorem physical_principal_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M order,∀ time ∈ Icc 0 horizon,
      (∑ word : FixedMatterSpatialWordIndex order,
        2*inner ℝ (read (weight nu M (value seed M word.toList time)))
          (read (effective seed M time (value seed M word.toList time)))) ≤
        -nu.coeff^2*(∑ word : FixedMatterSpatialWordIndex order,
          ‖read (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M (value seed M word.toList time))‖^2)+
        C*(∑ word : FixedMatterSpatialWordIndex order,
          ‖field seed M word.toList time‖^2) := by
  simpa only [read_pairing,read_norm,field,NativeWindowHistoryAllOrderSpatial.principalWork,
    NativeWindowHistoryAllOrderSpatial.dissipation,NativeWindowHistoryAllOrderWord.energy] using
    NativeWindowHistoryAllOrderSpatial.source_principal_bound seed horizon

theorem actual_work_integral (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    NativeWindowHistoryAllOrderSpatial.work seed M order time =
      ∑ word : FixedMatterSpatialWordIndex order,
        ∫ x : Torus,2*inner ℝ (read (weight nu M (value seed M word.toList time)) x)
          (read (retained seed M word.toList time) x) := by
  simp only [NativeWindowHistoryAllOrderSpatial.work,integral_const_mul,← L2.inner_def,read_pairing]

theorem physical_source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M order,∀ time ∈ Icc 0 horizon,
      deriv (fun t => ∑ word : FixedMatterSpatialWordIndex order,
        inner ℝ (field seed M word.toList t) (read (weight nu M (value seed M word.toList t)))) time +
          nu.coeff^2*(∑ word : FixedMatterSpatialWordIndex order,
            ‖read (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M (value seed M word.toList time))‖^2) ≤
        C*(∑ word : FixedMatterSpatialWordIndex order,‖field seed M word.toList time‖^2)+
          ∑ word : FixedMatterSpatialWordIndex order,
            ∫ x : Torus,2*inner ℝ (read (weight nu M (value seed M word.toList time)) x)
              (read (retained seed M word.toList time) x) := by
  simp only [← actual_work_integral,field,read_pairing,read_norm]
  exact NativeWindowHistoryAllOrderSpatial.source_generator seed horizon

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem field_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    field seed M word (step.2.clockAdvance+time) = field step.1 M word time :=
  congrArg read (NativeWindowHistoryAllOrderWord.value_next seed M word step generated time nonnegative)


def coordinate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (time : ℝ) (i : Coordinate) : C(Torus,ℂ) :=
  NativeWindowAbsoluteTimeFourier.polynomial (modes M)
    (fun k => wholeVelocity (value seed M word time).val k i)

theorem coefficient_outside (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (k : IntegerWavevector) (outside : k ∉ modes M) :
    wholeVelocity (value seed M word time).val k = 0 := by
  funext i
  simp only [value,word_row,complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply,mul_zero]

theorem coefficient_summable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) :
    Summable (fun k => Real.sqrt (ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq
      (wholeVelocity (value seed M word time).val k))) :=
  summable_of_ne_finset_zero (s := modes M) fun k outside => by
    rw [coefficient_outside seed M word time k outside]
    simp [ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq]

theorem coordinate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (i : Coordinate) :
    coordinate seed M word time i = NativePhysicalContinuous.scalarContinuous
      (wholeVelocity (value seed M word time).val) i := by
  rw [NativePhysicalContinuous.scalarContinuous,tsum_eq_sum (s := modes M) (fun k outside => by
    rw [coefficient_outside seed M word time k outside]
    exact zero_smul ℂ (UnitAddTorus.mFourier k))]
  apply ContinuousMap.ext
  intro x
  simp only [coordinate,NativeWindowAbsoluteTimeFourier.polynomial,ContinuousMap.coe_mk,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem physical_representative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) :
    field seed M word time =ᵐ[volume] fun x : Torus =>
      WithLp.toLp 2 (fun i : Coordinate => (coordinate seed M word time i x).re) := by
  have actual:=NativePhysicalContinuous.continuousField_ae
    (wholeVelocity (value seed M word time).val) (coefficient_summable seed M word time)
  change realField (wholeVelocity (value seed M word time).val) =ᵐ[volume]
    fun x : Torus => WithLp.toLp 2 (fun i : Coordinate => (coordinate seed M word time i x).re)
  simpa only [NativePhysicalContinuous.continuousField,ContinuousMap.coe_mk,coordinate_original] using actual

theorem ordinary_pointwise_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List Coordinate) (time : ℝ) (j i : Coordinate) (x : Torus) :
    HasDerivAt (fun z => coordinate seed M word time i (x+NativePhysicalTranslation.displacement j z))
      (coordinate seed M (j::word) time i x) 0 := by
  have actual:=NativeWindowAbsoluteTimeFourier.polynomial_hasDerivAt (modes M)
    (fun k => wholeVelocity (value seed M word time).val k i) j x
  have next : coordinate seed M (j::word) time i =
      NativeWindowAbsoluteTimeFourier.polynomial (modes M)
        (fun k => NativePhysicalGradient.multiplier k j • wholeVelocity (value seed M word time).val k i) := by
    simp only [coordinate,word_cons,smul_eq_mul]
  rw [next]
  exact actual

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderPhysical
