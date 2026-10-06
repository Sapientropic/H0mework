import H0mework.Arithmetic.SonineGap.StageZeroRieszStateNaturality

/-!
# Exact identification of centered and detector residuals

Normalized quotient stationarity forces the centered Gram residual to be the
detector covariance residual multiplied by the nonzero measurement-coordinate
share of the same joint state.  Therefore their zero fibres coincide.  This
closes the former same-occurrence prism seam without assuming neutrality,
criticality, or residual vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open SourceGeneratedCenteredGram
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCharacterGroupRing
open Character.GlobalCoPoissonCurrent

noncomputable section

theorem selectedStageZero_centeredResidual_eq_detectorResidual_mul_measurementShare
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedStageZeroCenteredGramResidual observation nontrivial =
      -((selectedOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta (1 : Units NNReal))).snd) *
        (((‖(selectedStageZeroJointState observation nontrivial).snd‖ ^ 2 : ℝ) : ℂ) /
          ((‖selectedStageZeroJointState observation nontrivial‖ ^ 2 : ℝ) : ℂ)) := by
  let state := selectedStageZeroJointState observation nontrivial
  let target := selectedStageZeroRawRieszTarget observation nontrivial
  have stateNe : state ≠ 0 :=
    selectedStageZeroJointState_ne_zero observation nontrivial
  have targetEqCharacter :
      target = quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        stageZeroSqrtScale := by
    unfold target selectedStageZeroRawRieszTarget
    exact occurrence_selectedDilationTrace_eq_character
      observation nontrivial stageZeroSqrtScale stageZeroSqrtScale_pos
  have targetNe : target ≠ 0 := by
    rw [targetEqCharacter]
    exact quarterDilationCharacter_ne_zero
      (selectedCoPoissonMuntzParameter observation)
      stageZeroSqrtScale stageZeroSqrtScale_pos
  have stationary :
      inner ℂ state
          (graphTargetMap
            (normalizedQuarterDilationGraphMorphism
              (selectedCoPoissonMuntzParameter observation)
              stageZeroSqrtScale stageZeroSqrtScale_pos) state) =
        inner ℂ state state := by
    simpa [state, selectedStageZeroJointState] using
      selectedRieszGraphTargetState_stageZero_normalized_stationary
        observation nontrivial
  have normalizedEnergy :
      target⁻¹ * inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) =
        inner ℂ state.fst state.fst := by
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply] at stationary
    change inner ℂ state.fst
          ((quarterDilationCharacter
              (selectedCoPoissonMuntzParameter observation)
              stageZeroSqrtScale)⁻¹ •
            positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) +
          inner ℂ state.snd state.snd =
        inner ℂ state.fst state.fst + inner ℂ state.snd state.snd at stationary
    rw [← targetEqCharacter] at stationary
    rw [inner_smul_right] at stationary
    exact add_right_cancel stationary
  have energy :
      inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) =
        target * inner ℂ state.fst state.fst := by
    calc
      _ = target * (target⁻¹ * inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst)) := by
            field_simp [targetNe]
      _ = _ := by rw [normalizedEnergy]
  have stateNormSqNe : (((‖state‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr stateNe))
  rw [selected_stageZero_detectorResidual_at_identity]
  change target - normalizedAutocorrelation state
      stageZeroOwnerFreeGraphTargetAction =
    -(1 - target) *
      (((‖state.snd‖ ^ 2 : ℝ) : ℂ) /
        ((‖state‖ ^ 2 : ℝ) : ℂ))
  unfold normalizedAutocorrelation
  rw [stageZeroOwnerFreeGraphTargetAction_eq_rawScale,
    WithLp.prod_inner_apply]
  change target -
      (inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) +
        inner ℂ state.snd state.snd) /
          (((‖state‖ ^ 2 : ℝ) : ℂ)) = _
  rw [energy, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  field_simp [stateNormSqNe]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  push_cast
  let energyNorm : ℂ := (‖state.fst‖ : ℂ) ^ 2
  let measurementNorm : ℂ := (‖state.snd‖ : ℂ) ^ 2
  change target * (energyNorm + measurementNorm) -
      (target * energyNorm + measurementNorm) =
    -((1 - target) * measurementNorm)
  ring

theorem reversalStageZero_centeredResidual_eq_detectorResidual_mul_measurementShare
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalStageZeroCenteredGramResidual observation nontrivial =
      -((reversalOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta (1 : Units NNReal))).snd) *
        (((‖(reversalStageZeroJointState observation nontrivial).snd‖ ^ 2 : ℝ) : ℂ) /
          ((‖reversalStageZeroJointState observation nontrivial‖ ^ 2 : ℝ) : ℂ)) := by
  let state := reversalStageZeroJointState observation nontrivial
  let target := reversalStageZeroRawRieszTarget observation nontrivial
  have stateNe : state ≠ 0 :=
    reversalStageZeroJointState_ne_zero observation nontrivial
  have targetEqCharacter :
      target = quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        stageZeroSqrtScale := by
    unfold target reversalStageZeroRawRieszTarget
    exact occurrence_reversalDilationTrace_eq_character
      observation nontrivial stageZeroSqrtScale stageZeroSqrtScale_pos
  have targetNe : target ≠ 0 := by
    rw [targetEqCharacter]
    exact quarterDilationCharacter_ne_zero
      (reversalCoPoissonMuntzParameter observation)
      stageZeroSqrtScale stageZeroSqrtScale_pos
  have stationary :
      inner ℂ state
          (graphTargetMap
            (normalizedQuarterDilationGraphMorphism
              (reversalCoPoissonMuntzParameter observation)
              stageZeroSqrtScale stageZeroSqrtScale_pos) state) =
        inner ℂ state state := by
    simpa [state, reversalStageZeroJointState] using
      reversalRieszGraphTargetState_stageZero_normalized_stationary
        observation nontrivial
  have normalizedEnergy :
      target⁻¹ * inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) =
        inner ℂ state.fst state.fst := by
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply] at stationary
    change inner ℂ state.fst
          ((quarterDilationCharacter
              (reversalCoPoissonMuntzParameter observation)
              stageZeroSqrtScale)⁻¹ •
            positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) +
          inner ℂ state.snd state.snd =
        inner ℂ state.fst state.fst + inner ℂ state.snd state.snd at stationary
    rw [← targetEqCharacter] at stationary
    rw [inner_smul_right] at stationary
    exact add_right_cancel stationary
  have energy :
      inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) =
        target * inner ℂ state.fst state.fst := by
    calc
      _ = target * (target⁻¹ * inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst)) := by
            field_simp [targetNe]
      _ = _ := by rw [normalizedEnergy]
  have stateNormSqNe : (((‖state‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr stateNe))
  rw [reversal_stageZero_detectorResidual_at_identity]
  change target - normalizedAutocorrelation state
      stageZeroOwnerFreeGraphTargetAction =
    -(1 - target) *
      (((‖state.snd‖ ^ 2 : ℝ) : ℂ) /
        ((‖state‖ ^ 2 : ℝ) : ℂ))
  unfold normalizedAutocorrelation
  rw [stageZeroOwnerFreeGraphTargetAction_eq_rawScale,
    WithLp.prod_inner_apply]
  change target -
      (inner ℂ state.fst
          (positiveMellinQuarterEnergyTranslation
            (Real.log stageZeroSqrtScale) state.fst) +
        inner ℂ state.snd state.snd) /
          (((‖state‖ ^ 2 : ℝ) : ℂ)) = _
  rw [energy, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  field_simp [stateNormSqNe]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  push_cast
  let energyNorm : ℂ := (‖state.fst‖ : ℂ) ^ 2
  let measurementNorm : ℂ := (‖state.snd‖ : ℂ) ^ 2
  change target * (energyNorm + measurementNorm) -
      (target * energyNorm + measurementNorm) =
    -((1 - target) * measurementNorm)
  ring

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
