import H0mework.Versions.X.NavierStokes.NativeWorkSource.ReadoutPhysicalMaterialActionReadbackReceipt
import H0mework.Versions.X.NavierStokes.PhysicalTranslation.Field

set_option autoImplicit false
open scoped ENNReal Matrix

namespace SaturationMonoid.NavierStokes.NativeMaterialSpatialAction

open MeasureTheory PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePhysicalFourier NativePhysicalTimeAction NativeMaterialReadback NativePhysicalTranslation
open NativePhysicalSource NativeSourceMaterialJet

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def action {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (offset : Torus) :
    Lp E 2 (volume : Measure Torus) →L[ℝ] Lp E 2 (volume : Measure Torus) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun point : Torus => point + offset)
    (measurePreserving_add_right volume offset)).toContinuousLinearMap

theorem action_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (offset : Torus) (value : Lp E 2 (volume : Measure Torus)) :
    action offset value =ᵐ[volume] fun point => value (point + offset) :=
  Lp.coeFn_compMeasurePreserving value (measurePreserving_add_right volume offset)

theorem action_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (offset : Torus) (linear : E →L[ℝ] F) (value : Lp E 2 (volume : Measure Torus)) :
    action offset (linear.compLp value) = linear.compLp (action offset value) := by
  apply Lp.ext
  filter_upwards [action_apply offset (linear.compLp value),
    (measurePreserving_add_right volume offset).quasiMeasurePreserving.ae (linear.coeFn_compLp value),
    linear.coeFn_compLp (action offset value), action_apply offset value] with point translated shifted read actual
  rw [translated, shifted, read, actual]

def coordinateEmbedding (coordinate : Fin 3) : ℂ →L[ℝ] PhysicalSpace :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single coordinate 1)).comp Complex.reCLM

def assemble (values : Fin 3 → ScalarField) : PhysicalField :=
  (coordinateEmbedding 0).compLp (values 0) + (coordinateEmbedding 1).compLp (values 1) +
    (coordinateEmbedding 2).compLp (values 2)

theorem assemble_apply (values : Fin 3 → ScalarField) :
    assemble values =ᵐ[volume] fun point => WithLp.toLp 2 (fun coordinate => (values coordinate point).re) := by
  filter_upwards [Lp.coeFn_add ((coordinateEmbedding 0).compLp (values 0) + (coordinateEmbedding 1).compLp (values 1))
      ((coordinateEmbedding 2).compLp (values 2)),
    Lp.coeFn_add ((coordinateEmbedding 0).compLp (values 0)) ((coordinateEmbedding 1).compLp (values 1)),
    (coordinateEmbedding 0).coeFn_compLp (values 0), (coordinateEmbedding 1).coeFn_compLp (values 1),
    (coordinateEmbedding 2).coeFn_compLp (values 2)] with point total pair first second third
  rw [assemble, total, Pi.add_apply, pair, Pi.add_apply, first, second, third]
  ext coordinate
  fin_cases coordinate <;> simp [coordinateEmbedding]

theorem assemble_source (state : ComplexVorticityHilbertState) : assemble (scalarField state) = realField state := by
  apply Lp.ext
  filter_upwards [assemble_apply (scalarField state), realField_apply state] with point assembled actual
  exact assembled.trans actual.symm

theorem assemble_gradient (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    assemble (NativePhysicalGradient.field state direction) = NativeBalancedReceipt.spatialField state direction := by
  apply Lp.ext
  filter_upwards [assemble_apply (NativePhysicalGradient.field state direction),
    NativeBalancedReceipt.spatialField_apply state direction] with point assembled actual
  exact assembled.trans actual.symm

theorem action_assemble (offset : Torus) (values : Fin 3 → ScalarField) :
    action offset (assemble values) = assemble (fun coordinate => NativePhysicalTranslation.translate offset (values coordinate)) := by
  simp only [assemble, map_add, action_linear]
  rfl

theorem source_hasDerivAt (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    HasDerivAt (fun time => action (displacement direction time) (realField (wholeBiotSavartVelocityState state)))
      (NativeBalancedReceipt.spatialField state direction) 0 := by
  have each (coordinate : Fin 3) :=
    ((coordinateEmbedding coordinate).compLpL 2 (volume : Measure Torus)).hasFDerivAt.comp_hasDerivAt 0
      (source_translation_hasDerivAt state direction coordinate)
  have generated := ((each 0).add (each 1)).add (each 2)
  rw [← assemble_gradient]
  have fields (time : ℝ) : action (displacement direction time) (realField (wholeBiotSavartVelocityState state)) =
      assemble (fun coordinate => NativePhysicalTranslation.translate (displacement direction time)
        (scalarField (wholeBiotSavartVelocityState state) coordinate)) := by
    rw [← assemble_source, action_assemble]
  simp only [fields]
  convert! generated using 1

theorem action_background (offset : Torus) : action offset NativeMaterialReceipt.background = NativeMaterialReceipt.background := by
  apply Lp.ext
  have background := (memLp_const (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0))
    (μ := (volume : Measure Torus)) (p := (2 : ℝ≥0∞))).coeFn_toLp
  filter_upwards [action_apply offset NativeMaterialReceipt.background,
    (measurePreserving_add_right volume offset).quasiMeasurePreserving.ae background, background] with point actual shifted constant
  exact actual.trans (shifted.trans constant.symm)

theorem action_material (offset : Torus) (value : PhysicalField) :
    action offset (NativeMaterialReceipt.material value) = NativeMaterialReceipt.material (action offset value) := by
  simp only [NativeMaterialReceipt.material, map_add, action_background, action_linear]

/-- Spatial source jets are the derivatives of the same complete matter field under actual translations. -/
theorem material_hasDerivAt (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    HasDerivAt (fun time => action (displacement direction time)
      (NativeMaterialReceipt.material (realField (wholeBiotSavartVelocityState state))))
      (materialIncrement.compLp (NativeBalancedReceipt.spatialField state direction)) 0 := by
  have generated := (((materialIncrement.compLpL 2 (volume : Measure Torus)).hasFDerivAt.comp_hasDerivAt 0
    (source_hasDerivAt state direction)).const_add NativeMaterialReceipt.background)
  simp only [NativeMaterialReceipt.material]
  convert! generated using 1

theorem receipt_rawDerivative {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Set.Icc (0 : ℝ) T) (direction : Fin 3) :
    materialIncrement.compLp (NativeBalancedReceipt.spatialField (receipt.wholePath time) direction) =ᵐ[volume]
      fun point => matterCoordinateEquiv (NativeSourceMaterialAdjoint.rawDerivative
        (receiptJet receipt time point) direction.succ) := by
  filter_upwards [materialIncrement.coeFn_compLp (NativeBalancedReceipt.spatialField (receipt.wholePath time) direction),
    NativeBalancedReceipt.spatialField_apply (receipt.wholePath time) direction] with point actual spatial
  rw [spatial] at actual
  exact actual.trans (materialIncrement_rawDerivative (receiptJet receipt time point) direction.succ)

def connectionResponse {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Set.Icc (0 : ℝ) T) (direction : Fin 3) :=
  NativeCovariantReceipt.material receipt time direction -
    materialIncrement.compLp (NativeBalancedReceipt.spatialField (receipt.wholePath time) direction)

/-- The previously controlled covariant jet is the actual spatial derivative plus the same source connection action. -/
theorem connectionResponse_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Set.Icc (0 : ℝ) T) (direction : Fin 3) :
    connectionResponse receipt time direction =ᵐ[volume] fun point =>
      matterCoordinateEquiv (NativeBalancedMaterialJet.connectionOperator
        (receiptField receipt time point) (receiptJet receipt time point) direction.succ
          (NativeCanonicalFluidCoframe.matter (receiptField receipt time point))) := by
  filter_upwards [Lp.coeFn_sub (NativeCovariantReceipt.material receipt time direction)
      (materialIncrement.compLp (NativeBalancedReceipt.spatialField (receipt.wholePath time) direction)),
    NativeCovariantReceipt.material_apply receipt time direction, receipt_rawDerivative receipt time direction]
      with point difference covariant raw
  rw [connectionResponse, difference, Pi.sub_apply, covariant, raw,
    NativeBalancedMaterialJet.derivative, map_add, add_sub_cancel_left]

end
end SaturationMonoid.NavierStokes.NativeMaterialSpatialAction
