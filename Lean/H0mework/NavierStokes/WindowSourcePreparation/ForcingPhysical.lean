import H0mework.NavierStokes.WindowSourcePreparation.ForcingSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowPreparationForce
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeFullOrderSynthesis
open NativePhysicalHistoryInitialAction NativeWindowPreparationWrite
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
noncomputable section

def rows (time : ℝ) : ComplexVorticityHilbertState := fraction time • momentum

theorem weighted_correction (time : ℝ) (wave : NonzeroIntegerWavevector) :
    NativeNegativeFourMomentum.weightedRowCLM wave.1 (rows time wave.1) =
      (fraction time • momentumCLM butterflyGainViscosity
        (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) wave := by
  change NativeNegativeFourMomentum.weightedRowCLM wave.1 (fraction time • momentum wave.1) = _
  rw [map_smul, ← full_initial_action]
  rfl

theorem actual_writer (time : ℝ) (wave : NonzeroIntegerWavevector) :
    NativeNegativeFourMomentum.embed (NativeForwardWindowEvolution.velocityJet stackedShortCurrent 1 time) wave =
      momentumCLM butterflyGainViscosity (NativeForwardWindowSource.source stackedShortCurrent time) wave-
        NativeNegativeFourMomentum.weightedRowCLM wave.1 (rows time wave.1) := by
  have actual := congrArg (fun value : WholeRestartVelocityEndpointState => value wave)
    (full_action_momentum stackedShortCurrent time)
  change NativeNegativeFourMomentum.embed (NativeForwardWindowEvolution.velocityJet stackedShortCurrent 1 time) wave =
    momentumCLM butterflyGainViscosity (NativeForwardWindowSource.source stackedShortCurrent time) wave-
      (fraction time • momentumCLM butterflyGainViscosity
        (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) wave at actual
  rw [weighted_correction]
  exact actual

def spacetime (point : BasePoint) : PhysicalSpace :=
  fraction (canonicalTimeProjection point) • field (canonicalSpatialProjection point)

theorem spacetime_smooth : ContDiff ℝ ∞ spacetime :=
  (fraction_smooth.comp canonicalTimeProjection.contDiff).smul
    (field_smooth.comp canonicalSpatialProjection.contDiff)

theorem spacetime_slice (time : ℝ) (point : PhysicalSpace) :
    spacetime (canonicalCauchySlicePoint time point) = fraction time • field point := by
  simp only [spacetime, canonicalTimeProjection_slice, canonicalSpatialProjection_slice]

theorem spatial_read (time : ℝ) (point : PhysicalSpace) :
    spatialField (rows time) point = spacetime (canonicalCauchySlicePoint time point) := by
  have scalar (coordinate : Coordinate) : NativePhysicalContinuous.scalarContinuous (rows time) coordinate =
      fraction time • NativePhysicalContinuous.scalarContinuous momentum coordinate := by
    simp only [NativePhysicalContinuous.scalarContinuous, rows, lp.coeFn_smul, Pi.smul_apply,
      smul_assoc, tsum_const_smul'']
  rw [spacetime_slice]
  apply PiLp.ext
  intro coordinate
  change (NativePhysicalContinuous.scalarContinuous (rows time) coordinate (circlePoint point)).re =
    fraction time * (NativePhysicalContinuous.scalarContinuous momentum coordinate (circlePoint point)).re
  rw [scalar]
  simp

theorem spacetime_after (point : BasePoint) (after : -1 ≤ canonicalTimeProjection point) : spacetime point = 0 := by
  rw [spacetime, fraction_after _ after, zero_smul]

theorem all_order_Lp (order : ℕ) (exponent : ℝ≥0∞) {domain : Set BasePoint}
    (compact : IsCompact domain) :
    ∃ bound : ℝ,
      MemLp (iteratedFDeriv ℝ order spacetime) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order spacetime) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuous := spacetime_smooth.continuous_iteratedFDeriv (m := order)
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuous.continuousOn
  have paid : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order spacetime point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound continuous.aestronglyMeasurable.restrict _ paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationForce
