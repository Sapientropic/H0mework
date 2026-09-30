import H0mework.Versions.X.NavierStokes.MaterialReadback.Differential

set_option autoImplicit false
open scoped ENNReal

namespace SaturationMonoid.NavierStokes.NativeMaterialReceipt

open MeasureTheory Set PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativeStressSource
open NativeMaterialReadback

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev MatterField := Lp MatterCoordinateCarrier 2 (volume : Measure Torus)

def background : MatterField :=
  (memLp_const (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0))).toLp
    (fun _ => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0))

def material (field : PhysicalField) : MatterField := background + materialIncrement.compLp field

theorem material_apply (field : PhysicalField) :
    material field =ᵐ[volume] fun point => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter (field point)) := by
  filter_upwards [Lp.coeFn_add background (materialIncrement.compLp field),
    (memLp_const (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0))
      (μ := (volume : Measure Torus)) (p := (2 : ℝ≥0∞))).coeFn_toLp,
    materialIncrement.coeFn_compLp field] with point sum constant increment
  rw [material, sum, Pi.add_apply, increment, materialIncrement_eq]
  change background point = _ at constant
  rw [constant, ← add_sub_assoc, add_sub_cancel_left]

theorem velocity_read (field : PhysicalField) : velocityRead.compLp (material field) = field := by
  apply Lp.ext
  filter_upwards [velocityRead.coeFn_compLp (material field), material_apply field] with point actual source
  rw [source, velocityRead_matter] at actual
  exact actual

theorem increment_read (field : PhysicalField) :
    velocityRead.compLp (materialIncrement.compLp field) = field := by
  apply Lp.ext
  filter_upwards [velocityRead.coeFn_compLp (materialIncrement.compLp field),
    materialIncrement.coeFn_compLp field] with point actual source
  rw [source, velocityRead_increment] at actual
  exact actual

theorem material_ae_hasDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time : ℝ, time ∈ uIcc (0 : ℝ) T →
      HasDerivAt (fun actual => material (physicalPrimitive receipt actual))
        (materialIncrement.compLp (physicalTangent receipt time)) time := by
  filter_upwards [physicalPrimitive_ae_hasDerivAt receipt] with time derivative inside
  exact ((materialIncrement.compLpL 2 (volume : Measure Torus)).hasFDerivAt.comp_hasDerivAt time
    (derivative inside)).const_add background

theorem material_integral_write {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∫ actual in 0..time.1, materialIncrement.compLp (physicalTangent receipt actual)) =
      material (receiptField receipt time) - material (realField (wholeBiotSavartVelocityState initial)) := by
  have integrableAt := (physicalTangent_intervalIntegrable receipt).mono_set (by
    rw [uIcc_of_le time.2.1, uIcc_of_le receipt.requestedTimePos.le]
    exact Icc_subset_Icc le_rfl time.2.2)
  change (∫ actual in 0..time.1, (materialIncrement.compLpL 2 (volume : Measure Torus))
    (physicalTangent receipt actual)) = _
  refine ((materialIncrement.compLpL 2 (volume : Measure Torus)).intervalIntegral_comp_comm integrableAt).trans ?_
  refine (congrArg (materialIncrement.compLpL 2 (volume : Measure Torus)) (physical_integral_write receipt time)).trans ?_
  rw [map_sub]
  change materialIncrement.compLp (receiptField receipt time) -
    materialIncrement.compLp (realField (wholeBiotSavartVelocityState initial)) = _
  simp only [material]
  abel

/-- The full material impulse is generated on the original physical clock and writes the same actual next. -/
theorem occurrence_material_write {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    let occurrence := generatedWholeRestartNativeActualOccurrence initial index
    (∫ actual in 0..occurrence.response.1.contact.time.1,
      materialIncrement.compLp (physicalTangent (occurrenceReceipt occurrence) actual)) =
        material (realField (wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState)) -
          material (realField (wholeBiotSavartVelocityState (run initial index).contact.physicalState)) := by
  let occurrence := generatedWholeRestartNativeActualOccurrence initial index
  exact material_integral_write (occurrenceReceipt occurrence)
    ⟨_, (occurrenceReceipt occurrence).requestedTimePos.le, le_rfl⟩

end
end SaturationMonoid.NavierStokes.NativeMaterialReceipt
