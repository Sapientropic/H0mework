import H0mework.Versions.X.NavierStokes.MaterialJets.Densitized

set_option autoImplicit false
open scoped Matrix BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeDensitizedReceipt

open MeasureTheory Set PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativeSourceMaterialJet
open NativeSourceMaterialAdjoint NativeMaterialMomentumJet NativeDensitizedMaterial

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev MatterField := Lp MatterCoordinateCarrier 2 (volume : Measure Torus)

def spatial {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) : MatterField :=
  (gammaCoordinate direction.succ).compLp (NativeCovariantReceipt.material receipt time direction)

def kinetic {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) : Fin 4 → MatterField :=
  ![-(spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2),
    spatial receipt time 0, spatial receipt time 1, spatial receipt time 2]

theorem spatial_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) :
    spatial receipt time direction =ᵐ[volume] fun point =>
      actualTerm (receiptField receipt time point) (receiptJet receipt time point) direction.succ := by
  filter_upwards [(gammaCoordinate direction.succ).coeFn_compLp (NativeCovariantReceipt.material receipt time direction),
    NativeCovariantReceipt.material_apply receipt time direction] with point actual source
  rw [source, ← actualTerm_spatial] at actual
  exact actual

theorem actual_sum_zero {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, (∑ direction, actualTerm (receiptField receipt time point) (receiptJet receipt time point) direction) = 0 := by
  filter_upwards [NativeBalancedMaterialJet.receipt_equations receipt time] with point equations
  have primal := (equations 0).1
  rw [source_yukawa_zero, add_zero] at primal
  rw [actualTerm_sum, primal, smul_zero, map_zero]

/-- The original field equation generates the time term from the same three controlled spatial terms. -/
theorem kinetic_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ direction : Fin 4, kinetic receipt time direction point =
      actualTerm (receiptField receipt time point) (receiptJet receipt time point) direction := by
  filter_upwards [spatial_apply receipt time 0, spatial_apply receipt time 1, spatial_apply receipt time 2,
    actual_sum_zero receipt time,
    Lp.coeFn_neg (spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2),
    Lp.coeFn_add (spatial receipt time 0 + spatial receipt time 1) (spatial receipt time 2),
    Lp.coeFn_add (spatial receipt time 0) (spatial receipt time 1)] with point first second third equation negative total pair
  intro direction
  fin_cases direction
  · change (-(spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2) : MatterField) point = _
    rw [negative, Pi.neg_apply, total, Pi.add_apply, pair, Pi.add_apply, first, second, third]
    simp only [Fin.sum_univ_four] at equation
    exact (eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using equation)).symm
  · exact first
  · exact second
  · exact third

theorem kinetic_sum_zero {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction, kinetic receipt time direction) = 0 := by
  rw [Fin.sum_univ_four]
  change -(spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2) +
    spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2 = 0
  simpa only [add_assoc] using neg_add_cancel
    (spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2)

private theorem triple_energy (first second third : MatterField) :
    ‖first + second + third‖ ^ 2 ≤ 3 * (‖first‖ ^ 2 + ‖second‖ ^ 2 + ‖third‖ ^ 2) := by
  have bound : ‖first + second + third‖ ≤ ‖first‖ + ‖second‖ + ‖third‖ :=
    (norm_add_le _ _).trans (by linarith [norm_add_le first second])
  have square := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr bound
  nlinarith [sq_nonneg (‖first‖ - ‖second‖), sq_nonneg (‖first‖ - ‖third‖),
    sq_nonneg (‖second‖ - ‖third‖)]

def gammaBudget : ℝ := 4 * ∑ direction : Fin 3, ‖gammaCoordinate direction.succ‖ ^ 2

theorem kinetic_energy {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction : Fin 4, ‖kinetic receipt time direction‖ ^ 2) ≤
      gammaBudget * ∑ direction : Fin 3, ‖NativeCovariantReceipt.material receipt time direction‖ ^ 2 := by
  have spatialBound : (∑ direction : Fin 3, ‖spatial receipt time direction‖ ^ 2) ≤
      (∑ direction : Fin 3, ‖gammaCoordinate direction.succ‖ ^ 2) *
        ∑ direction : Fin 3, ‖NativeCovariantReceipt.material receipt time direction‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro direction _
    have mapBound := (gammaCoordinate direction.succ).norm_compLp_le
      (NativeCovariantReceipt.material receipt time direction)
    have square := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr mapBound
    change ‖spatial receipt time direction‖ ^ 2 ≤ _ at square
    rw [mul_pow] at square
    exact square.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun index _ => sq_nonneg ‖gammaCoordinate index.succ‖)
        (Finset.mem_univ direction)) (sq_nonneg _))
  have timeBound := triple_energy (spatial receipt time 0) (spatial receipt time 1) (spatial receipt time 2)
  have full : (∑ direction : Fin 4, ‖kinetic receipt time direction‖ ^ 2) ≤
      4 * ∑ direction : Fin 3, ‖spatial receipt time direction‖ ^ 2 := by
    rw [Fin.sum_univ_four, Fin.sum_univ_three]
    change ‖-(spatial receipt time 0 + spatial receipt time 1 + spatial receipt time 2)‖ ^ 2 +
      ‖spatial receipt time 0‖ ^ 2 + ‖spatial receipt time 1‖ ^ 2 + ‖spatial receipt time 2‖ ^ 2 ≤ _
    rw [norm_neg]
    linarith
  exact full.trans (by dsimp only [gammaBudget]; nlinarith [spatialBound])

/-- All four original densitized kinetic terms are paid by the original velocity and full first jet. -/
theorem energy_bound {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction : Fin 4, ‖kinetic receipt time direction‖ ^ 2) ≤
      gammaBudget * ‖NativeBalancedGaugeEnergy.materialEmbedding‖ ^ 2 *
        (32 * ‖receiptField receipt time‖ ^ 2 + 7 / 16 * ‖physicalTangent receipt time.1‖ ^ 2 +
          2 * ‖realField (receipt.wholePath time)‖ ^ 2) := by
  have nonnegative : 0 ≤ gammaBudget := by unfold gammaBudget; positivity
  exact (kinetic_energy receipt time).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (NativeCovariantReceipt.energy_bound receipt time) nonnegative)

end
end SaturationMonoid.NavierStokes.NativeDensitizedReceipt
