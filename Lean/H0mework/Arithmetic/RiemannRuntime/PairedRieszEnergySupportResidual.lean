import H0mework.Arithmetic.SonineGap.StageZeroWeightedResidualIdentification
import H0mework.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinRadialDefect

/-!
# Paired Riesz energy-support residual

Normalized relation-graph stationarity already forces the energy coordinate
of each realized Riesz state to have the corresponding dilation character as
an inner-product eigenvalue.  Since the energy evolution is an isometry,
Cauchy--Schwarz kills that energy coordinate whenever the character norm is
strictly greater than one.

Selected and reversal character norms are reciprocal around the half-density
line.  Hence every off-line zero generates a concrete measurement-only Riesz
state: its energy coordinate is zero while its measurement coordinate is
nonzero.  This is the exact no-third-sink residual left by the current graph
carrier; it is not a new zero/RH premise.
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
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedFunctionalGraphPerfectification
open Character.GlobalCoPoissonCurrent

noncomputable section

universe h

/-- An isometric energy evolution cannot have a nonzero state whose
stationary inner-product character has norm greater than one. -/
theorem energy_eq_zero_of_isometric_stationary_character_norm_gt_one
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (energyAction : H ≃ₗᵢ[ℂ] H) (state : H) (character : ℂ)
    (stationary : inner ℂ state (energyAction state) =
      character * inner ℂ state state)
    (characterNorm : 1 < ‖character‖) :
    state = 0 := by
  by_contra stateNe
  have stateNormPos : 0 < ‖state‖ := norm_pos_iff.mpr stateNe
  have bound : ‖character‖ * ‖state‖ ^ 2 ≤ ‖state‖ ^ 2 := by
    calc
      ‖character‖ * ‖state‖ ^ 2 =
          ‖character * inner ℂ state state‖ := by
            rw [norm_mul, inner_self_eq_norm_sq_to_K]
            simp
      _ = ‖inner ℂ state (energyAction state)‖ :=
        congrArg norm stationary.symm
      _ ≤ ‖state‖ * ‖energyAction state‖ :=
        norm_inner_le_norm state (energyAction state)
      _ = ‖state‖ ^ 2 := by
        rw [energyAction.norm_map]
        ring
  have stateNormSqPos : 0 < ‖state‖ ^ 2 := sq_pos_of_pos stateNormPos
  nlinarith

theorem selectedRieszEnergy_expectation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    inner ℂ (selectedStageZeroJointState observation nontrivial).fst
        (positiveMellinQuarterEnergyTranslationIsometry
          (Real.log stageZeroSqrtScale)
          (selectedStageZeroJointState observation nontrivial).fst) =
      selectedStageZeroRawRieszTarget observation nontrivial *
        inner ℂ (selectedStageZeroJointState observation nontrivial).fst
          (selectedStageZeroJointState observation nontrivial).fst := by
  let state := selectedStageZeroJointState observation nontrivial
  let target := selectedStageZeroRawRieszTarget observation nontrivial
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
        inner ℂ state.fst state.fst + inner ℂ state.snd state.snd
      at stationary
    rw [← targetEqCharacter, inner_smul_right] at stationary
    exact add_right_cancel stationary
  change inner ℂ state.fst
      (positiveMellinQuarterEnergyTranslation
        (Real.log stageZeroSqrtScale) state.fst) =
    target * inner ℂ state.fst state.fst
  calc
    _ = target * (target⁻¹ * inner ℂ state.fst
        (positiveMellinQuarterEnergyTranslation
          (Real.log stageZeroSqrtScale) state.fst)) := by
          field_simp [targetNe]
    _ = _ := by rw [normalizedEnergy]

theorem reversalRieszEnergy_expectation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    inner ℂ (reversalStageZeroJointState observation nontrivial).fst
        (positiveMellinQuarterEnergyTranslationIsometry
          (Real.log stageZeroSqrtScale)
          (reversalStageZeroJointState observation nontrivial).fst) =
      reversalStageZeroRawRieszTarget observation nontrivial *
        inner ℂ (reversalStageZeroJointState observation nontrivial).fst
          (reversalStageZeroJointState observation nontrivial).fst := by
  let state := reversalStageZeroJointState observation nontrivial
  let target := reversalStageZeroRawRieszTarget observation nontrivial
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
        inner ℂ state.fst state.fst + inner ℂ state.snd state.snd
      at stationary
    rw [← targetEqCharacter, inner_smul_right] at stationary
    exact add_right_cancel stationary
  change inner ℂ state.fst
      (positiveMellinQuarterEnergyTranslation
        (Real.log stageZeroSqrtScale) state.fst) =
    target * inner ℂ state.fst state.fst
  calc
    _ = target * (target⁻¹ * inner ℂ state.fst
        (positiveMellinQuarterEnergyTranslation
          (Real.log stageZeroSqrtScale) state.fst)) := by
          field_simp [targetNe]
    _ = _ := by rw [normalizedEnergy]

theorem selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    1 < ‖selectedStageZeroRawRieszTarget observation nontrivial‖ := by
  unfold selectedStageZeroRawRieszTarget
  rw [occurrence_selectedDilationTrace_eq_character,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos]
  apply Real.one_lt_rpow stageZeroSqrtScale_one_lt
  simp [selectedCoPoissonMuntzParameter]
  linarith

theorem reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    1 < ‖reversalStageZeroRawRieszTarget observation nontrivial‖ := by
  unfold reversalStageZeroRawRieszTarget
  rw [occurrence_reversalDilationTrace_eq_character,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos]
  apply Real.one_lt_rpow stageZeroSqrtScale_one_lt
  simp [reversalCoPoissonMuntzParameter, coordinateReversal]
  linarith

theorem selectedRieszEnergy_eq_zero_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    (selectedStageZeroJointState observation nontrivial).fst = 0 := by
  exact energy_eq_zero_of_isometric_stationary_character_norm_gt_one
    (positiveMellinQuarterEnergyTranslationIsometry
      (Real.log stageZeroSqrtScale))
    (selectedStageZeroJointState observation nontrivial).fst
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedRieszEnergy_expectation observation nontrivial)
    (selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
      observation nontrivial left)

theorem reversalRieszEnergy_eq_zero_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    (reversalStageZeroJointState observation nontrivial).fst = 0 := by
  exact energy_eq_zero_of_isometric_stationary_character_norm_gt_one
    (positiveMellinQuarterEnergyTranslationIsometry
      (Real.log stageZeroSqrtScale))
    (reversalStageZeroJointState observation nontrivial).fst
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalRieszEnergy_expectation observation nontrivial)
    (reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
      observation nontrivial right)

/-- Exact representation residual: one involutive Riesz state has lost its
entire energy face while retaining a nonzero measurement face. -/
inductive PairedRieszMeasurementOnlyResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Type where
  | selected
      (energy_zero :
        (selectedStageZeroJointState observation nontrivial).fst = 0)
      (measurement_ne_zero :
        (selectedStageZeroJointState observation nontrivial).snd ≠ 0)
  | reversal
      (energy_zero :
        (reversalStageZeroJointState observation nontrivial).fst = 0)
      (measurement_ne_zero :
        (reversalStageZeroJointState observation nontrivial).snd ≠ 0)

/-- Every off-line zero generates the no-third-sink residual; no branch is
chosen by a caller. -/
def pairedRieszMeasurementOnlyResidual_of_offCenter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    PairedRieszMeasurementOnlyResidual observation nontrivial := by
  by_cases left : observation.coordinate.re < 1 / 2
  · exact .selected
      (selectedRieszEnergy_eq_zero_of_re_lt_half
        observation nontrivial left)
      (selectedStageZeroJointState_snd_ne_zero observation nontrivial)
  · have right : 1 / 2 < observation.coordinate.re :=
      lt_of_le_of_ne (le_of_not_gt left) (Ne.symm offCenter)
    exact .reversal
      (reversalRieszEnergy_eq_zero_of_half_lt_re
        observation nontrivial right)
      (reversalStageZeroJointState_snd_ne_zero observation nontrivial)

/-- If the source-generated paired state has no measurement-only branch,
the zero is forced onto the half-density line. -/
theorem coordinate_re_eq_half_of_pairedRiesz_energy_supported
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (selectedEnergy :
      (selectedStageZeroJointState observation nontrivial).fst ≠ 0)
    (reversalEnergy :
      (reversalStageZeroJointState observation nontrivial).fst ≠ 0) :
    observation.coordinate.re = 1 / 2 := by
  by_contra offCenter
  cases pairedRieszMeasurementOnlyResidual_of_offCenter
      observation nontrivial offCenter with
  | selected energyZero _ => exact selectedEnergy energyZero
  | reversal energyZero _ => exact reversalEnergy energyZero

end


end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
