import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NativeLocalizedProfilePrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualNativePreparedLegPriceOwn
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard GaussComposite.SourceGraph GaussCoreHilbert CanonicalPhysicalSpatial
open CanonicalGradedSpatialSource ActualQuantitativePreparedFrameOwn ActualSourceTensorPriceEnvelopeOwn
open scoped InnerProductSpace BigOperators

theorem actual_sourceProfile_native_price (epsilon : ℝ) (precision : 0 < epsilon) :
    ‖sourceProfile epsilon precision‖ ≤ 13 := by
  have h := original_native_zeroLocalized_profile_bound (sourceCausalState epsilon precision).point.val
  have unit : ‖(sourceCausalState epsilon precision).point.val‖ = 1 := by
    rw [← zeroLocalized_physical_norm actualNativeLocalizer]
    exact actualPrepared_norm epsilon precision
  simpa only [sourceProfile, unit, mul_one] using h

theorem actualLeg_native_price (epsilon : ℝ) (precision : 0 < epsilon)
    (addition : Bool) (a s : Fin 2) : ‖actualLeg epsilon precision addition a s‖ ≤ 39 := by
  have h := (completedLeg_bound addition a s (sourceProfile epsilon precision)).trans
    (mul_le_mul_of_nonneg_left (actual_sourceProfile_native_price epsilon precision) legBound_nonnegative)
  simpa only [actualLeg, legBound, seed_unit, mul_one, show (3 : ℝ) * 13 = 39 by norm_num] using h

theorem actual_pair_native_price (epsilon : ℝ) (precision : 0 < epsilon)
    (A : H →L[ℂ] H) (P : ℝ) (price : ‖A‖ ≤ P)
    (left right : Bool) (a s b t : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
      (A (actualLeg epsilon precision right b t))‖ ≤ 1521 * P := by
  have hP : 0 ≤ P := (norm_nonneg A).trans price
  calc
    _ ≤ ‖actualLeg epsilon precision left a s‖ * P * ‖actualLeg epsilon precision right b t‖ :=
      vertex_pair_price A P price _ _
    _ ≤ 39 * P * 39 := mul_le_mul
      (mul_le_mul_of_nonneg_right (actualLeg_native_price epsilon precision left a s) hP)
      (actualLeg_native_price epsilon precision right b t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_original_form_native_price (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (left right : Bool) (a s b t : Fin 2) :
    ‖GaussFockPair.sourcePair
      (sourceTestApprox F (actualLeg epsilon precision left a s))
      ((physicalAction p + GaussYukawaOperator.originalAction)
        (sourceTestApprox F (actualLeg epsilon precision right b t)))‖ ≤
      1521 * originalFormPrice f p F := by
  rw [← formRestriction_original_pair f p F]
  exact actual_pair_native_price epsilon precision _ _ (finiteRiesz_price F _) left right a s b t

theorem actualFullY_original_form_native_binary_error (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (bits : ℕ) (left : Bool) (a s : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (actualFullY epsilon precision)) -
      inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (FullYSourceCutoffVolterra.cutoff (916 * bits)
          (actualPrepared epsilon precision)))‖ ≤
      60016320 * originalFormPrice f p F * (1 / 2 : ℝ) ^ bits := by
  rw [← inner_sub_right, ← map_sub]
  have hP := originalFormPrice_nonnegative f p F
  calc
    _ ≤ ‖actualLeg epsilon precision left a s‖ * originalFormPrice f p F *
        ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff (916 * bits)
          (actualPrepared epsilon precision)‖ :=
      vertex_pair_price _ _ (finiteRiesz_price F _) _ _
    _ ≤ 39 * originalFormPrice f p F * (1538880 * (1 / 2 : ℝ) ^ bits) := mul_le_mul
      (mul_le_mul_of_nonneg_right (actualLeg_native_price epsilon precision left a s) hP)
      (actual_fullY_numerical_binary_error epsilon precision bits) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end LowEnergy.ActualNativePreparedLegPriceOwn
