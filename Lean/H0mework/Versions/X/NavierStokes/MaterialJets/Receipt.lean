import H0mework.Versions.X.NavierStokes.MaterialJets.Field

set_option autoImplicit false
open scoped Matrix BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeBalancedReceipt

open MeasureTheory Set PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativePhysicalGradient
open NativeSourceMaterialJet NativePauliCoframeAction NativeMaterialJetAction
open NativeCartanConstitutive NativeBalancedJetCoefficients NativeBalancedGaugeEnergy NativeBalancedMaterialField

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem spatialJet_memLp (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    MemLp (fun point : Torus => spatialJet state point direction) 2 volume := by
  apply memLp_piLp_iff.mpr
  intro coordinate
  exact Complex.reCLM.comp_memLp (field state direction coordinate)

def spatialField (state : ComplexVorticityHilbertState) (direction : Fin 3) : PhysicalField :=
  (spatialJet_memLp state direction).toLp (fun point => spatialJet state point direction)

theorem spatialField_apply (state : ComplexVorticityHilbertState) (direction : Fin 3) :
    spatialField state direction =ᵐ[volume] (fun point => spatialJet state point direction) :=
  (spatialJet_memLp state direction).coeFn_toLp

def jetFields {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) : Fin 4 → PhysicalField :=
  Fin.cases (physicalTangent receipt time.1) (spatialField (receipt.wholePath time))

theorem jetFields_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ direction : Fin 4, jetFields receipt time direction point = receiptJet receipt time point direction := by
  apply ae_all_iff.mpr
  intro direction
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact spatialField_apply _ coordinate

/-- The same three full spectral curls recover the original vorticity in the jet used by the mother action. -/
theorem curl_original {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, curl (normalizedJet (receiptJet receipt time point)) =
      normalizedVelocity (realField (receipt.wholePath time) point) := by
  let state := receipt.wholePath time
  have first := Lp.coeFn_sub (field state 1 2) (field state 2 1)
  have second := Lp.coeFn_sub (field state 2 0) (field state 0 2)
  have third := Lp.coeFn_sub (field state 0 1) (field state 1 0)
  change (curlField state 0 : Torus → ℂ) =ᵐ[volume] _ at first
  change (curlField state 1 : Torus → ℂ) =ᵐ[volume] _ at second
  change (curlField state 2 : Torus → ℂ) =ᵐ[volume] _ at third
  rw [curlField_eq state (receipt.wholePath_zero_row time) (wholePath_transverse receipt time)] at first second third
  filter_upwards [first, second, third, realField_apply state] with point first second third actual
  change curl (normalizedJet (receiptJet receipt time point)) = normalizedVelocity (realField state point)
  rw [actual]
  funext coordinate
  fin_cases coordinate
  · change (field state 1 2 point).re / 4 - (field state 2 1 point).re / 4 = (scalarField state 0 point).re / 4
    rw [first]
    simp only [Pi.sub_apply, Complex.sub_re]
    ring
  · change (field state 2 0 point).re / 4 - (field state 0 2 point).re / 4 = (scalarField state 1 point).re / 4
    rw [second]
    simp only [Pi.sub_apply, Complex.sub_re]
    ring
  · change (field state 0 1 point).re / 4 - (field state 1 0 point).re / 4 = (scalarField state 2 point).re / 4
    rw [third]
    simp only [Pi.sub_apply, Complex.sub_re]
    ring

private theorem normalized_energy (velocity : PhysicalSpace) :
    squared (normalizedVelocity velocity) = ‖velocity‖ ^ 2 / 16 := by
  simp [squared, normalizedVelocity, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  ring

def material {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) :=
  materialField (receiptField receipt time) (jetFields receipt time) direction

theorem material_apply {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) (direction : Fin 3) :
    material receipt time direction =ᵐ[volume] fun point =>
      matterCoordinateEquiv (NativeSourceColorAction.increment (receiptField receipt time point)
        (coefficients (normalizedVelocity (receiptField receipt time point)) (normalizedJet (receiptJet receipt time point)))
          direction.succ) := by
  filter_upwards [materialField_apply (receiptField receipt time) (jetFields receipt time) direction,
    jetFields_apply receipt time] with point actual jet
  have equal : (fun index => jetFields receipt time index point) = receiptJet receipt time point := funext jet
  simpa only [material, equal] using actual

theorem point_energy {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, (∑ direction : Fin 3, ‖material receipt time direction point‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 * (3 / 64 * ‖physicalTangent receipt time.1 point‖ ^ 2 +
        5 / 32 * ‖realField (receipt.wholePath time) point‖ ^ 2) := by
  have all := ae_all_iff.mpr (fun direction => material_apply receipt time direction)
  filter_upwards [all, curl_original receipt time] with point actual curl
  simp only [actual]
  have bound := source_material_energy (receiptField receipt time point) (receiptJet receipt time point)
  rw [curl, normalized_energy, show normalizedJet (receiptJet receipt time point) 0 =
    normalizedVelocity (physicalTangent receipt time.1 point) from rfl, normalized_energy] at bound
  convert bound using 1
  ring

private theorem l2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (field : Lp E 2 (volume : Measure Torus)) : ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The full original time tangent and vorticity pay the actual mother gauge response in L². -/
theorem energy_bound {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    (∑ direction : Fin 3, ‖material receipt time direction‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 * (3 / 64 * ‖physicalTangent receipt time.1‖ ^ 2 +
        5 / 32 * ‖realField (receipt.wholePath time)‖ ^ 2) := by
  have each (direction : Fin 3) := (Lp.memLp (material receipt time direction)).norm.integrable_sq
  have tangent := (Lp.memLp (physicalTangent receipt time.1)).norm.integrable_sq
  have vorticity := (Lp.memLp (realField (receipt.wholePath time))).norm.integrable_sq
  calc
    _ = ∫ point : Torus, ∑ direction : Fin 3, ‖material receipt time direction point‖ ^ 2 := by
      simp only [l2_norm_sq]
      exact (integral_finsetSum _ (fun direction _ => each direction)).symm
    _ ≤ ∫ point : Torus, ‖materialEmbedding‖ ^ 2 *
        (3 / 64 * ‖physicalTangent receipt time.1 point‖ ^ 2 +
          5 / 32 * ‖realField (receipt.wholePath time) point‖ ^ 2) :=
      integral_mono_ae (integrable_finsetSum _ (fun direction _ => each direction))
        (((tangent.const_mul (3 / 64)).add (vorticity.const_mul (5 / 32))).const_mul _)
        (point_energy receipt time)
    _ = _ := by
      rw [integral_const_mul, integral_add (tangent.const_mul _) (vorticity.const_mul _),
        integral_const_mul, integral_const_mul, ← l2_norm_sq, ← l2_norm_sq]

end
end SaturationMonoid.NavierStokes.NativeBalancedReceipt
