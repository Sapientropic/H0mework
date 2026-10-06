import H0mework.Arithmetic.RiemannGraph.StageZeroOrbitClosedDefectPort
import H0mework.Arithmetic.RiemannRuntime.PairedRieszEnergySupportResidual

/-!
# A measurement-only state internalizes the orbit defect

If one closed carrier contains the actual identity and next orbit points and
the corresponding measurement-only Riesz state, the raw coupling incidence
is a scalar multiple of that state.  It is therefore internal, and the
canonical external defect of the evolved identity seed is zero.

Off center, the existing energy-support theorem chooses a selected or
reversal measurement-only state on exactly the side whose character norm is
greater than one.  Thus the expanding channel is not controlled by the
external port; it is absorbed by any common closed carrier containing that
state.  This is a scoped no-go for eliminating the third sink by orthogonal
leakage alone, not for a future source-generated internal action law.
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

open SourceGeneratedCompressedUnitaryDefectPort
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

theorem selectedRawIncidence_eq_measurementOnly_smul
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (energy_zero :
      (selectedStageZeroJointState observation nontrivial).fst = 0)
    (measurement_ne_zero :
      (selectedStageZeroJointState observation nontrivial).snd ≠ 0) :
    selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      ((1 - selectedStageZeroRawRieszTarget observation nontrivial) *
          (selectedStageZeroJointState observation nontrivial).snd⁻¹) •
        selectedStageZeroJointState observation nontrivial := by
  apply (WithLp.linearEquiv 2 ℂ
    (PositiveMellinQuarterEnergy × ℂ)).injective
  apply Prod.ext
  · change
      (selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).fst = _
    rw [selectedOwnerFreeCouplingResidual_delta_fst]
    change 0 =
      ((1 - selectedStageZeroRawRieszTarget observation nontrivial) *
        (selectedStageZeroJointState observation nontrivial).snd⁻¹) •
          (selectedStageZeroJointState observation nontrivial).fst
    rw [energy_zero, smul_zero]
  · change
      (selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).snd = _
    rw [selected_stageZero_detectorResidual_at_identity]
    change 1 - selectedStageZeroRawRieszTarget observation nontrivial =
      ((1 - selectedStageZeroRawRieszTarget observation nontrivial) *
        (selectedStageZeroJointState observation nontrivial).snd⁻¹) *
          (selectedStageZeroJointState observation nontrivial).snd
    field_simp

theorem reversalRawIncidence_eq_measurementOnly_smul
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (energy_zero :
      (reversalStageZeroJointState observation nontrivial).fst = 0)
    (measurement_ne_zero :
      (reversalStageZeroJointState observation nontrivial).snd ≠ 0) :
    reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      ((1 - reversalStageZeroRawRieszTarget observation nontrivial) *
          (reversalStageZeroJointState observation nontrivial).snd⁻¹) •
        reversalStageZeroJointState observation nontrivial := by
  apply (WithLp.linearEquiv 2 ℂ
    (PositiveMellinQuarterEnergy × ℂ)).injective
  apply Prod.ext
  · change
      (reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).fst = _
    rw [reversalOwnerFreeCouplingResidual_delta_fst]
    change 0 =
      ((1 - reversalStageZeroRawRieszTarget observation nontrivial) *
        (reversalStageZeroJointState observation nontrivial).snd⁻¹) •
          (reversalStageZeroJointState observation nontrivial).fst
    rw [energy_zero, smul_zero]
  · change
      (reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).snd = _
    rw [reversal_stageZero_detectorResidual_at_identity]
    change 1 - reversalStageZeroRawRieszTarget observation nontrivial =
      ((1 - reversalStageZeroRawRieszTarget observation nontrivial) *
        (reversalStageZeroJointState observation nontrivial).snd⁻¹) *
          (reversalStageZeroJointState observation nontrivial).snd
    field_simp

theorem selectedExternalDefect_zero_of_measurementOnly_internal
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (K : ClosedSubmodule ℂ JointGraphTarget)
    (seed_mem : selectedIntegralGraphOrbit observation nontrivial (delta 1) ∈ K)
    (next_mem : selectedStageZeroOrbitNextPoint observation nontrivial ∈ K)
    (state_mem : selectedStageZeroJointState observation nontrivial ∈ K)
    (energy_zero :
      (selectedStageZeroJointState observation nontrivial).fst = 0)
    (measurement_ne_zero :
      (selectedStageZeroJointState observation nontrivial).snd ≠ 0) :
    externalDefect K stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        ⟨selectedIntegralGraphOrbit observation nontrivial (delta 1), seed_mem⟩ = 0 := by
  apply (externalDefect_eq_zero_iff K
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry _).2
  have incidence_mem :
      selectedOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta 1) ∈ K := by
    rw [selectedRawIncidence_eq_measurementOnly_smul observation nontrivial
      energy_zero measurement_ne_zero]
    exact K.smul_mem _ state_mem
  have split :
      stageZeroOwnerFreeGraphTargetAction
          (selectedIntegralGraphOrbit observation nontrivial (delta 1)) =
        selectedOwnerFreeCouplingResidual observation nontrivial
            stageZeroQuarterScaleUnit (delta 1) +
          selectedStageZeroOrbitNextPoint observation nontrivial := by
    rw [selectedStageZeroCouplingResidual_eq_action_sub_next]
    exact (sub_add_cancel _ _).symm
  change stageZeroOwnerFreeGraphTargetAction
      (selectedIntegralGraphOrbit observation nontrivial (delta 1)) ∈ K
  rw [split]
  exact K.add_mem incidence_mem next_mem

theorem reversalExternalDefect_zero_of_measurementOnly_internal
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (K : ClosedSubmodule ℂ JointGraphTarget)
    (seed_mem : reversalIntegralGraphOrbit observation nontrivial (delta 1) ∈ K)
    (next_mem : reversalStageZeroOrbitNextPoint observation nontrivial ∈ K)
    (state_mem : reversalStageZeroJointState observation nontrivial ∈ K)
    (energy_zero :
      (reversalStageZeroJointState observation nontrivial).fst = 0)
    (measurement_ne_zero :
      (reversalStageZeroJointState observation nontrivial).snd ≠ 0) :
    externalDefect K stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        ⟨reversalIntegralGraphOrbit observation nontrivial (delta 1), seed_mem⟩ = 0 := by
  apply (externalDefect_eq_zero_iff K
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry _).2
  have incidence_mem :
      reversalOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta 1) ∈ K := by
    rw [reversalRawIncidence_eq_measurementOnly_smul observation nontrivial
      energy_zero measurement_ne_zero]
    exact K.smul_mem _ state_mem
  have split :
      stageZeroOwnerFreeGraphTargetAction
          (reversalIntegralGraphOrbit observation nontrivial (delta 1)) =
        reversalOwnerFreeCouplingResidual observation nontrivial
            stageZeroQuarterScaleUnit (delta 1) +
          reversalStageZeroOrbitNextPoint observation nontrivial := by
    rw [reversalStageZeroCouplingResidual_eq_action_sub_next]
    exact (sub_add_cancel _ _).symm
  change stageZeroOwnerFreeGraphTargetAction
      (reversalIntegralGraphOrbit observation nontrivial (delta 1)) ∈ K
  rw [split]
  exact K.add_mem incidence_mem next_mem

/-- Off center, any common closed carrier containing both orbit points and
the relevant Riesz state absorbs the expanding channel internally. -/
theorem offCenter_expandingChannel_externalDefect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (selectedK reversalK : ClosedSubmodule ℂ JointGraphTarget)
    (selectedSeed : selectedIntegralGraphOrbit observation nontrivial (delta 1) ∈ selectedK)
    (selectedNext : selectedStageZeroOrbitNextPoint observation nontrivial ∈ selectedK)
    (selectedState : selectedStageZeroJointState observation nontrivial ∈ selectedK)
    (reversalSeed : reversalIntegralGraphOrbit observation nontrivial (delta 1) ∈ reversalK)
    (reversalNext : reversalStageZeroOrbitNextPoint observation nontrivial ∈ reversalK)
    (reversalState : reversalStageZeroJointState observation nontrivial ∈ reversalK)
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (‖selectedStageZeroRawRieszTarget observation nontrivial‖ > 1 ∧
      externalDefect selectedK
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
          ⟨selectedIntegralGraphOrbit observation nontrivial (delta 1), selectedSeed⟩ = 0) ∨
    (‖reversalStageZeroRawRieszTarget observation nontrivial‖ > 1 ∧
      externalDefect reversalK
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
          ⟨reversalIntegralGraphOrbit observation nontrivial (delta 1), reversalSeed⟩ = 0) := by
  by_cases left : observation.coordinate.re < 1 / 2
  · exact Or.inl ⟨
      selectedStageZeroRawRieszTarget_norm_gt_one_of_re_lt_half
        observation nontrivial left,
      selectedExternalDefect_zero_of_measurementOnly_internal
        observation nontrivial selectedK selectedSeed selectedNext selectedState
        (selectedRieszEnergy_eq_zero_of_re_lt_half observation nontrivial left)
        (selectedStageZeroJointState_snd_ne_zero observation nontrivial)⟩
  · have right : 1 / 2 < observation.coordinate.re :=
      lt_of_le_of_ne (le_of_not_gt left) (Ne.symm offCenter)
    exact Or.inr ⟨
      reversalStageZeroRawRieszTarget_norm_gt_one_of_half_lt_re
        observation nontrivial right,
      reversalExternalDefect_zero_of_measurementOnly_internal
        observation nontrivial reversalK reversalSeed reversalNext reversalState
        (reversalRieszEnergy_eq_zero_of_half_lt_re observation nontrivial right)
        (reversalStageZeroJointState_snd_ne_zero observation nontrivial)⟩

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
