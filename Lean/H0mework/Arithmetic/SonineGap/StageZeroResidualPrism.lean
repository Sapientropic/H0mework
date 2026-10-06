import H0mework.Arithmetic.RiemannGraph.IntegralGraphCouplingResidual
import H0mework.Arithmetic.RiemannGraph.StageZeroCenteredGramDisposition

/-!
# Stage-zero detector/centered residual prism

The fourth-root integral charge scale puts the stored integral orbit and the
actual stage-zero owner-free action on exactly the same graph target.  The
complex detector residual recovers the raw Riesz target, while its radial fold
recovers the existing no-flux coordinate.  The remaining phase-sensitive
coordinate is split exactly into the retained detector residual plus the
centered-state trace; no phase-zero or RH premise enters.
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

open Character.GlobalCoPoissonCurrent
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedCenteredGram
open SourceGeneratedPositiveRealCharacter
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

/-- The integral charge scale whose square is the actual stage-zero
Archimedean scale used by the centered Gram action. -/
def stageZeroQuarterScaleUnit : Units NNReal :=
  positiveRealUnit (Real.sqrt stageZeroSqrtScale)
    (Real.sqrt_pos.2 stageZeroSqrtScale_pos)

theorem stageZeroQuarterScaleUnit_square :
    scaleSquare stageZeroQuarterScaleUnit = stageZeroSqrtScale := by
  unfold scaleSquare scaleValue stageZeroQuarterScaleUnit
  rw [positiveRealUnit_val, sq, Real.mul_self_sqrt]
  exact stageZeroSqrtScale_pos.le

theorem stageZeroQuarterScale_ownerFreeAction :
    ownerFreeGraphProductAction stageZeroQuarterScaleUnit =
      stageZeroOwnerFreeGraphTargetAction.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro value
  apply (WithLp.linearEquiv 2 ℂ
    (PositiveMellinQuarterEnergy × ℂ)).injective
  apply Prod.ext
  · change positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare stageZeroQuarterScaleUnit)) value.fst =
      positiveMellinQuarterEnergyTranslation
        (Real.log (positiveUnitValue (stageSqrtScaleUnit 0))) value.fst
    rw [stageZeroQuarterScaleUnit_square, stageZeroSqrtScale_unit_value]
  · rfl

/-- Detector residual evaluated directly from the integral orbit stored in
the joint occurrence root. -/
def selectedStageZeroJointRootDetectorResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  (ownerFreeGraphProductAction stageZeroQuarterScaleUnit
        (((zeroOwnedJointStateModuleOccurrence
          observation nontrivial).root.2).selectedIntegralOrbit (delta 1)) -
      ((zeroOwnedJointStateModuleOccurrence
          observation nontrivial).root.2).selectedIntegralOrbit
        ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))).snd

def reversalStageZeroJointRootDetectorResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  (ownerFreeGraphProductAction stageZeroQuarterScaleUnit
        (((zeroOwnedJointStateModuleOccurrence
          observation nontrivial).root.2).reversalIntegralOrbit (delta 1)) -
      ((zeroOwnedJointStateModuleOccurrence
          observation nontrivial).root.2).reversalIntegralOrbit
        ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))).snd

theorem selectedStageZeroJointRootDetectorResidual_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedStageZeroJointRootDetectorResidual observation nontrivial =
      (selectedOwnerFreeCouplingResidual
        observation nontrivial stageZeroQuarterScaleUnit (delta 1)).snd := by
  rfl

theorem reversalStageZeroJointRootDetectorResidual_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalStageZeroJointRootDetectorResidual observation nontrivial =
      (reversalOwnerFreeCouplingResidual
        observation nontrivial stageZeroQuarterScaleUnit (delta 1)).snd := by
  rfl

theorem selected_stageZero_detectorResidual_at_identity
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedOwnerFreeCouplingResidual
        observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).snd =
      1 - selectedStageZeroRawRieszTarget observation nontrivial := by
  rw [selectedOwnerFreeCouplingResidual_delta_normalForm,
    stageZeroQuarterScaleUnit_square]
  unfold selectedStageZeroRawRieszTarget
  rw [occurrence_selectedDilationTrace_eq_character]
  have scaleOne : scaleSquare (1 : Units NNReal) = 1 := by
    simp [scaleSquare, scaleValue]
  rw [scaleOne]
  simp [quarterDilationCharacter]

theorem selected_stageZero_jointRoot_detectorResidual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    1 - selectedStageZeroJointRootDetectorResidual observation nontrivial =
      selectedStageZeroRawRieszTarget observation nontrivial := by
  rw [selectedStageZeroJointRootDetectorResidual_eq,
    selected_stageZero_detectorResidual_at_identity]
  ring

theorem reversal_stageZero_detectorResidual_at_identity
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalOwnerFreeCouplingResidual
        observation nontrivial
        stageZeroQuarterScaleUnit (delta 1)).snd =
      1 - reversalStageZeroRawRieszTarget observation nontrivial := by
  rw [reversalOwnerFreeCouplingResidual_delta_normalForm,
    stageZeroQuarterScaleUnit_square]
  unfold reversalStageZeroRawRieszTarget
  rw [occurrence_reversalDilationTrace_eq_character]
  have scaleOne : scaleSquare (1 : Units NNReal) = 1 := by
    simp [scaleSquare, scaleValue]
  rw [scaleOne]
  simp [quarterDilationCharacter]

theorem reversal_stageZero_jointRoot_detectorResidual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    1 - reversalStageZeroJointRootDetectorResidual observation nontrivial =
      reversalStageZeroRawRieszTarget observation nontrivial := by
  rw [reversalStageZeroJointRootDetectorResidual_eq,
    reversal_stageZero_detectorResidual_at_identity]
  ring

/-- Radial readout on the actual raw Riesz targets used by the centered
state measurement.  It forgets only phase. -/
def stageZeroRawRadialCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℝ :=
  ‖selectedStageZeroRawRieszTarget observation nontrivial‖ -
    ‖reversalStageZeroRawRieszTarget observation nontrivial‖

theorem stageZeroRawRadialCurrent_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    stageZeroRawRadialCurrent observation nontrivial = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  unfold stageZeroRawRadialCurrent
  rw [sub_eq_zero]
  unfold selectedStageZeroRawRieszTarget reversalStageZeroRawRieszTarget
  rw [occurrence_selectedDilationTrace_eq_character,
    occurrence_reversalDilationTrace_eq_character,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos]
  constructor
  · intro normEq
    have exponentEq :=
      (Real.strictMono_rpow_of_base_gt_one
        stageZeroSqrtScale_one_lt).injective normEq
    simp [selectedCoPoissonMuntzParameter,
      reversalCoPoissonMuntzParameter, coordinateReversal] at exponentEq
    linarith
  · intro critical
    congr 1
    simp [selectedCoPoissonMuntzParameter,
      reversalCoPoissonMuntzParameter, coordinateReversal]
    linarith

theorem stageZeroRawRadialCurrent_eq_zero_iff_rieszFlux
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    stageZeroRawRadialCurrent observation nontrivial = 0 ↔
      radialRieszFluxResidual observation nontrivial 0 = 0 := by
  rw [stageZeroRawRadialCurrent_eq_zero_iff]
  constructor
  · intro critical
    exact (radialRieszFluxResidual_eq_zero_iff_groupRingRadialCurrent_eq_zero
      observation nontrivial 0).2
        ((groupRingRadialCurrent_eq_zeroOwnedPositiveMellinRadialDefect
          observation nontrivial 0).trans
          (QRich.zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
            observation nontrivial 0 critical))
  · intro radialZero
    have groupZero :=
      (radialRieszFluxResidual_eq_zero_iff_groupRingRadialCurrent_eq_zero
        observation nontrivial 0).1 radialZero
    have mellinZero :
        QRich.zeroOwnedPositiveMellinRadialDefect
            observation nontrivial 0 = 0 := by
      rw [← groupRingRadialCurrent_eq_zeroOwnedPositiveMellinRadialDefect]
      exact groupZero
    exact (QRich.zeroOwnedPositiveMellinRadialDefect_eq_zero_iff
      observation nontrivial 0).1 mellinZero

theorem stageZeroRawRadialCurrent_detector_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    stageZeroRawRadialCurrent observation nontrivial =
      ‖1 - selectedStageZeroJointRootDetectorResidual
          observation nontrivial‖ -
        ‖1 - reversalStageZeroJointRootDetectorResidual
          observation nontrivial‖ := by
  rw [selected_stageZero_jointRoot_detectorResidual_readback,
    reversal_stageZero_jointRoot_detectorResidual_readback]
  unfold stageZeroRawRadialCurrent
  rfl

/-- Phase-sensitive balance coordinate.  Its zero is stronger than radial
neutrality; it is retained only so the radial measurement does not silently
discard phase. -/
def selectedStageZeroPhaseBalanceResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  1 - normalizedAutocorrelation
    (selectedStageZeroJointState observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction

def reversalStageZeroPhaseBalanceResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  1 - normalizedAutocorrelation
    (reversalStageZeroJointState observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction

/-- Exact residual prism: the total closed-system defect is the retained
integral detector-covariance residual plus the forced centered-state trace. -/
theorem selected_stageZero_phase_residual_split
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedStageZeroPhaseBalanceResidual observation nontrivial =
      selectedStageZeroJointRootDetectorResidual observation nontrivial +
        selectedStageZeroCenteredGramResidual observation nontrivial := by
  rw [selectedStageZeroJointRootDetectorResidual_eq,
    selected_stageZero_detectorResidual_at_identity]
  unfold selectedStageZeroPhaseBalanceResidual
    selectedStageZeroCenteredGramResidual centeredGramResidual
  ring

theorem reversal_stageZero_phase_residual_split
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalStageZeroPhaseBalanceResidual observation nontrivial =
      reversalStageZeroJointRootDetectorResidual observation nontrivial +
        reversalStageZeroCenteredGramResidual observation nontrivial := by
  rw [reversalStageZeroJointRootDetectorResidual_eq,
    reversal_stageZero_detectorResidual_at_identity]
  unfold reversalStageZeroPhaseBalanceResidual
    reversalStageZeroCenteredGramResidual centeredGramResidual
  ring

theorem stageZero_detectorRadial_eq_zero_of_centeredGram_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (realized : StageZeroBothCenteredGramRealized observation nontrivial) :
    ‖1 - selectedStageZeroJointRootDetectorResidual
          observation nontrivial‖ -
        ‖1 - reversalStageZeroJointRootDetectorResidual
          observation nontrivial‖ = 0 := by
  rw [← stageZeroRawRadialCurrent_detector_readback]
  unfold stageZeroRawRadialCurrent
  exact sub_eq_zero.mpr realized.target_norms_eq

end

end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
