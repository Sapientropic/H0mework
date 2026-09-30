import H0mework.NavierStokes.MaterialJets.CovariantField

set_option autoImplicit false
open scoped Matrix BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeCovariantReceipt

open MeasureTheory Set PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativePhysicalGradient
open NativeSourceMaterialJet NativeBalancedGaugeEnergy NativeCovariantMaterialField

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

private theorem l2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (field : Lp E 2 (volume : Measure Torus)) : ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem spatialField_norm_le (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    ‖NativeBalancedReceipt.spatialField state direction‖ ^ 2 ≤
      ∑ coordinate : Fin 3, ‖field state direction coordinate‖ ^ 2 := by
  have pointBound (point : Torus) : ‖spatialJet state point direction‖ ^ 2 ≤
      ∑ coordinate : Fin 3, ‖field state direction coordinate point‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro coordinate _
    change ‖(field state direction coordinate point).re‖ ^ 2 ≤ _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (field state direction coordinate point)
  have each (coordinate : Fin 3) := (Lp.memLp (field state direction coordinate)).norm.integrable_sq
  rw [l2_norm_sq]
  calc
    _ ≤ ∫ point : Torus, ∑ coordinate : Fin 3, ‖field state direction coordinate point‖ ^ 2 := by
      apply integral_mono_ae (Lp.memLp (NativeBalancedReceipt.spatialField state direction)).norm.integrable_sq
        (integrable_finsetSum _ (fun coordinate _ => each coordinate))
      filter_upwards [NativeBalancedReceipt.spatialField_apply state direction] with point actual
      rw [actual]
      exact pointBound point
    _ = _ := by
      rw [integral_finsetSum _ (fun coordinate _ => each coordinate)]
      simp only [← l2_norm_sq]

theorem gradient_energy {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction : Fin 3, ‖NativeBalancedReceipt.jetFields receipt time direction.succ‖ ^ 2) ≤
      ‖realField (receipt.wholePath time)‖ ^ 2 := by
  change (∑ direction : Fin 3, ‖NativeBalancedReceipt.spatialField (receipt.wholePath time) direction‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ direction : Fin 3, ∑ coordinate : Fin 3, ‖field (receipt.wholePath time) direction coordinate‖ ^ 2 :=
      Finset.sum_le_sum fun direction _ => spatialField_norm_le _ direction
    _ = _ := by
      rw [gradient_norm_sq _ (receipt.wholePath_zero_row time) (wholePath_transverse receipt time),
        realField_norm_sq _ (receipt_reality receipt time)]

def material {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) :=
  materialField (receiptField receipt time) (NativeBalancedReceipt.jetFields receipt time) direction

theorem material_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) :
    material receipt time direction =ᵐ[volume] fun point =>
      matterCoordinateEquiv (NativeBalancedMaterialJet.derivative (receiptField receipt time point)
        (receiptJet receipt time point) direction.succ) := by
  filter_upwards [materialField_apply (receiptField receipt time) (NativeBalancedReceipt.jetFields receipt time) direction,
    NativeBalancedReceipt.jetFields_apply receipt time] with point actual jet
  have equal : (fun index => NativeBalancedReceipt.jetFields receipt time index point) = receiptJet receipt time point := funext jet
  simpa only [material, equal] using actual

/-- The source velocity, full time tangent and original enstrophy pay the complete spatial covariant matter jet. -/
theorem energy_bound {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction : Fin 3, ‖material receipt time direction‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 * (32 * ‖receiptField receipt time‖ ^ 2 +
        7 / 16 * ‖physicalTangent receipt time.1‖ ^ 2 + 2 * ‖realField (receipt.wholePath time)‖ ^ 2) := by
  have generated := field_energy_bound (receiptField receipt time) (NativeBalancedReceipt.jetFields receipt time)
  have budget := gradient_energy receipt time
  have timeValue : NativeBalancedReceipt.jetFields receipt time 0 = physicalTangent receipt time.1 := rfl
  rw [timeValue] at generated
  exact generated.trans (mul_le_mul_of_nonneg_left (by linarith [budget]) (sq_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeCovariantReceipt
