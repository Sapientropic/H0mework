import H0mework.Realization.Coherent.ExpandingOrbitClosure
import H0mework.Arithmetic.RiemannGraph.IntegralGraphKernelCompatibility
import H0mework.Arithmetic.RiemannGraph.MeasurementOnlyOrbitDefectInternalizationNoGo

/-!
# Expanding Riesz state: exact algebraic residual and closed admission

The same zero-owned integral graph orbit supplies an explicit inverse-character
power sequence.  Off center, the expanding sibling is excluded from the
literal integral range by the actual Mellin kernel law, but the normalized
power sequence lies in the complexified range and converges to that Riesz
state.  Hence the state is an exact algebraic-to-topological compression
residual, and its existing orbit defect has no external component.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

open Character.GlobalCoPoissonCurrent
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedExpandingGraphOrbitClosure
open SourceGeneratedIntegralOrbitClosedDefectPort
open ThetaJRoleRepresentation
open scoped TensorProduct

noncomputable section

private theorem quarterDilationCharacter_scaleSquare_pow
    (z : ℂ) (scale : Units NNReal) (n : ℕ) :
    quarterDilationCharacter z (scaleSquare (scale ^ n)) =
      quarterDilationCharacter z (scaleSquare scale) ^ n := by
  induction n with
  | zero =>
      simp [scaleSquare, scaleValue, quarterDilationCharacter]
  | succ n ih =>
      rw [pow_succ, quarterDilationCharacter_scaleSquare_mul, ih, pow_succ]

private theorem selected_stageZero_character_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare stageZeroQuarterScaleUnit) =
      selectedStageZeroRawRieszTarget observation nontrivial := by
  rw [stageZeroQuarterScaleUnit_square]
  unfold selectedStageZeroRawRieszTarget
  exact (occurrence_selectedDilationTrace_eq_character
    observation nontrivial stageZeroSqrtScale stageZeroSqrtScale_pos).symm

private theorem reversal_stageZero_character_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare stageZeroQuarterScaleUnit) =
      reversalStageZeroRawRieszTarget observation nontrivial := by
  rw [stageZeroQuarterScaleUnit_square]
  unfold reversalStageZeroRawRieszTarget
  exact (occurrence_reversalDilationTrace_eq_character
    observation nontrivial stageZeroSqrtScale stageZeroSqrtScale_pos).symm

private theorem selected_stageZero_power_energy_norm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    ‖(selectedIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ n))).fst‖ =
      ‖(selectedIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ 0))).fst‖ := by
  rw [selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_fst,
    positiveMellinQuarterEnergyTranslation_norm,
    selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_fst,
    positiveMellinQuarterEnergyTranslation_norm]

private theorem reversal_stageZero_power_energy_norm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    ‖(reversalIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ n))).fst‖ =
      ‖(reversalIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ 0))).fst‖ := by
  rw [reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_fst,
    positiveMellinQuarterEnergyTranslation_norm,
    reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_fst,
    positiveMellinQuarterEnergyTranslation_norm]

private theorem selected_stageZero_power_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    (selectedIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ n))).snd =
      selectedStageZeroRawRieszTarget observation nontrivial ^ n := by
  rw [selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd,
    quarterDilationCharacter_scaleSquare_pow,
    selected_stageZero_character_eq]

private theorem reversal_stageZero_power_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    (reversalIntegralGraphOrbit observation nontrivial
        (delta (stageZeroQuarterScaleUnit ^ n))).snd =
      reversalStageZeroRawRieszTarget observation nontrivial ^ n := by
  rw [reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_snd,
    quarterDilationCharacter_scaleSquare_pow,
    reversal_stageZero_character_eq]

/-- Explicit same-occurrence selected approximant. -/
def selectedExpandingRieszRangeApproximant
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) : JointGraphTarget :=
  expandingRangeApproximant
    (selectedIntegralGraphOrbit observation nontrivial)
    (fun k => delta (stageZeroQuarterScaleUnit ^ k))
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial).snd n

/-- Explicit same-occurrence reversal approximant. -/
def reversalExpandingRieszRangeApproximant
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) : JointGraphTarget :=
  expandingRangeApproximant
    (reversalIntegralGraphOrbit observation nontrivial)
    (fun k => delta (stageZeroQuarterScaleUnit ^ k))
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroJointState observation nontrivial).snd n

theorem selectedExpandingRieszRangeApproximant_mem_complexifiedRange
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    selectedExpandingRieszRangeApproximant observation nontrivial n ∈
      LinearMap.range (complexifiedFeature
        (selectedIntegralGraphOrbit observation nontrivial)) := by
  exact expandingRangeApproximant_mem_range
    (selectedIntegralGraphOrbit observation nontrivial)
    (fun k => delta (stageZeroQuarterScaleUnit ^ k))
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial).snd n

theorem reversalExpandingRieszRangeApproximant_mem_complexifiedRange
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (n : ℕ) :
    reversalExpandingRieszRangeApproximant observation nontrivial n ∈
      LinearMap.range (complexifiedFeature
        (reversalIntegralGraphOrbit observation nontrivial)) := by
  exact expandingRangeApproximant_mem_range
    (reversalIntegralGraphOrbit observation nontrivial)
    (fun k => delta (stageZeroQuarterScaleUnit ^ k))
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroJointState observation nontrivial).snd n

theorem selectedExpandingRieszRangeApproximant_tendsto
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    Filter.Tendsto
      (selectedExpandingRieszRangeApproximant observation nontrivial)
      Filter.atTop
      (nhds (selectedStageZeroJointState observation nontrivial)) := by
  exact expandingRangeApproximant_tendsto
    (selectedIntegralGraphOrbit observation nontrivial)
    (fun n => delta (stageZeroQuarterScaleUnit ^ n))
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)
    (selectedRieszEnergy_eq_zero_of_re_lt_half observation nontrivial left)
    (selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
      observation nontrivial left)
    (selected_stageZero_power_energy_norm observation nontrivial)
    (selected_stageZero_power_measurement observation nontrivial)

theorem reversalExpandingRieszRangeApproximant_tendsto
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    Filter.Tendsto
      (reversalExpandingRieszRangeApproximant observation nontrivial)
      Filter.atTop
      (nhds (reversalStageZeroJointState observation nontrivial)) := by
  exact expandingRangeApproximant_tendsto
    (reversalIntegralGraphOrbit observation nontrivial)
    (fun n => delta (stageZeroQuarterScaleUnit ^ n))
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)
    (reversalRieszEnergy_eq_zero_of_half_lt_re observation nontrivial right)
    (reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
      observation nontrivial right)
    (reversal_stageZero_power_energy_norm observation nontrivial)
    (reversal_stageZero_power_measurement observation nontrivial)

/-- On the expanding selected side, the same zero/Müntz occurrence's
measurement-only Riesz point is in the actual complexified integral-orbit
closure.  The witnesses are the character-normalized power-orbit points. -/
theorem selectedExpandingRieszState_mem_complexifiedOrbitClosure
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    selectedStageZeroJointState observation nontrivial ∈
      selectedStageZeroOrbitClosedRange observation nontrivial := by
  exact measurementOnly_mem_orbitClosedRange_of_expandingOrbit
    (selectedIntegralGraphOrbit observation nontrivial)
    (fun n => delta (stageZeroQuarterScaleUnit ^ n))
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)
    (selectedRieszEnergy_eq_zero_of_re_lt_half observation nontrivial left)
    (selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
      observation nontrivial left)
    (selected_stageZero_power_energy_norm observation nontrivial)
    (selected_stageZero_power_measurement observation nontrivial)

/-- Reversal is the sibling construction from the same occurrence. -/
theorem reversalExpandingRieszState_mem_complexifiedOrbitClosure
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    reversalStageZeroJointState observation nontrivial ∈
      reversalStageZeroOrbitClosedRange observation nontrivial := by
  exact measurementOnly_mem_orbitClosedRange_of_expandingOrbit
    (reversalIntegralGraphOrbit observation nontrivial)
    (fun n => delta (stageZeroQuarterScaleUnit ^ n))
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)
    (reversalRieszEnergy_eq_zero_of_half_lt_re observation nontrivial right)
    (reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
      observation nontrivial right)
    (reversal_stageZero_power_energy_norm observation nontrivial)
    (reversal_stageZero_power_measurement observation nontrivial)

/-- The off-center occurrence itself chooses the expanding sibling; no
range witness or target-side classifier is supplied by the caller. -/
theorem offCenter_expandingRieszState_mem_complexifiedOrbitClosure
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      selectedStageZeroJointState observation nontrivial ∈
        selectedStageZeroOrbitClosedRange observation nontrivial) ∨
    (1 / 2 < observation.coordinate.re ∧
      reversalStageZeroJointState observation nontrivial ∈
        reversalStageZeroOrbitClosedRange observation nontrivial) := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · exact Or.inl ⟨left,
      selectedExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial left⟩
  · exact Or.inr ⟨right,
      reversalExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial right⟩

/-- Exact off-center representation disposition: the occurrence-selected
expanding state is not a literal integral-orbit value, but it is the limit of
the displayed complexified power-orbit points. -/
theorem offCenter_expandingRieszState_finiteComplexResidual_and_closedAdmission
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      selectedStageZeroJointState observation nontrivial ∉ LinearMap.range
        (complexifiedFeature
          (selectedIntegralGraphOrbit observation nontrivial)) ∧
      selectedStageZeroJointState observation nontrivial ∈
        selectedStageZeroOrbitClosedRange observation nontrivial) ∨
    (1 / 2 < observation.coordinate.re ∧
      reversalStageZeroJointState observation nontrivial ∉ LinearMap.range
        (complexifiedFeature
          (reversalIntegralGraphOrbit observation nontrivial)) ∧
      reversalStageZeroJointState observation nontrivial ∈
        reversalStageZeroOrbitClosedRange observation nontrivial) := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · have disposition :=
      measurementOnly_complexResidual_and_closedAdmission
        (selectedIntegralGraphOrbit observation nontrivial)
        (fun n => delta (stageZeroQuarterScaleUnit ^ n))
        (selectedStageZeroRawRieszTarget observation nontrivial)
        (selectedStageZeroJointState observation nontrivial)
        (selectedRieszEnergy_eq_zero_of_re_lt_half
          observation nontrivial left)
        (selectedStageZeroJointState_snd_ne_zero observation nontrivial)
        (selectedComplexifiedIntegralGraphOrbit_energy_zero_imp_measurement_zero
          observation nontrivial)
        (selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
          observation nontrivial left)
        (selected_stageZero_power_energy_norm observation nontrivial)
        (selected_stageZero_power_measurement observation nontrivial)
    exact Or.inl ⟨left, disposition.1, disposition.2⟩
  · have disposition :=
      measurementOnly_complexResidual_and_closedAdmission
        (reversalIntegralGraphOrbit observation nontrivial)
        (fun n => delta (stageZeroQuarterScaleUnit ^ n))
        (reversalStageZeroRawRieszTarget observation nontrivial)
        (reversalStageZeroJointState observation nontrivial)
        (reversalRieszEnergy_eq_zero_of_half_lt_re
          observation nontrivial right)
        (reversalStageZeroJointState_snd_ne_zero observation nontrivial)
        (reversalComplexifiedIntegralGraphOrbit_energy_zero_imp_measurement_zero
          observation nontrivial)
        (reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
          observation nontrivial right)
        (reversal_stageZero_power_energy_norm observation nontrivial)
        (reversal_stageZero_power_measurement observation nontrivial)
    exact Or.inr ⟨right, disposition.1, disposition.2⟩

/-- The actual selected orbit closure now satisfies the existing conservative
port's state premise, so the expanding incidence has no external component. -/
theorem selectedExpandingActualOrbit_externalDefect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    SourceGeneratedCompressedUnitaryDefectPort.externalDefect
        (selectedStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (selectedStageZeroOrbitIdentitySeed observation nontrivial) = 0 := by
  exact selectedExternalDefect_zero_of_measurementOnly_internal
    observation nontrivial
    (selectedStageZeroOrbitClosedRange observation nontrivial)
    (feature_mem_orbitClosedRange
      (selectedIntegralGraphOrbit observation nontrivial) (delta 1))
    (selectedStageZeroOrbitNextPoint_mem observation nontrivial)
    (selectedExpandingRieszState_mem_complexifiedOrbitClosure
      observation nontrivial left)
    (selectedRieszEnergy_eq_zero_of_re_lt_half observation nontrivial left)
    (selectedStageZeroJointState_snd_ne_zero observation nontrivial)

/-- Reversal sibling of the same direct consumer. -/
theorem reversalExpandingActualOrbit_externalDefect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    SourceGeneratedCompressedUnitaryDefectPort.externalDefect
        (reversalStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (reversalStageZeroOrbitIdentitySeed observation nontrivial) = 0 := by
  exact reversalExternalDefect_zero_of_measurementOnly_internal
    observation nontrivial
    (reversalStageZeroOrbitClosedRange observation nontrivial)
    (feature_mem_orbitClosedRange
      (reversalIntegralGraphOrbit observation nontrivial) (delta 1))
    (reversalStageZeroOrbitNextPoint_mem observation nontrivial)
    (reversalExpandingRieszState_mem_complexifiedOrbitClosure
      observation nontrivial right)
    (reversalRieszEnergy_eq_zero_of_half_lt_re observation nontrivial right)
    (reversalStageZeroJointState_snd_ne_zero observation nontrivial)

theorem offCenter_expandingActualOrbit_externalDefect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      SourceGeneratedCompressedUnitaryDefectPort.externalDefect
          (selectedStageZeroOrbitClosedRange observation nontrivial)
          stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
          (selectedStageZeroOrbitIdentitySeed observation nontrivial) = 0) ∨
    (1 / 2 < observation.coordinate.re ∧
      SourceGeneratedCompressedUnitaryDefectPort.externalDefect
          (reversalStageZeroOrbitClosedRange observation nontrivial)
          stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
          (reversalStageZeroOrbitIdentitySeed observation nontrivial) = 0) := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · exact Or.inl ⟨left,
      selectedExpandingActualOrbit_externalDefect_zero
        observation nontrivial left⟩
  · exact Or.inr ⟨right,
      reversalExpandingActualOrbit_externalDefect_zero
        observation nontrivial right⟩

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
