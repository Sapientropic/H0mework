import H0mework.Versions.V2.Arithmetic.RiemannRuntime.PairedIntegralGraphJointActionOccurrence
import H0mework.Versions.V2.Arithmetic.SonineGap.StageZeroResidualPrism
import H0mework.Versions.R2.Arithmetic.MuntzAction.LocalEndpointDifferentialResidual
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ParitySeparator

/-!
# Root-update effect on the paired Omega incidence

The actual unit-root successor fixes the q-rich scale.  At that scale the
measurement face of the same-occurrence paired `Omega` incidence is the
retained detector term.  Removing the generated quarter-density weight
recovers the existing selected/reversal Mellin pair, and its logarithmic
norm current is exactly the endpoint differential coefficient.

At the centered contact scale, the existing phase prism now reads literally

`phase residual = paired Omega incidence + centered trace`.

Thus this file projects an already generated root update/effect into the
joint-action face; it neither classifies nor assumes that the retained term
vanishes.
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
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open Complex
open InverseZeroFibre
open LocalEndpointDifferentialResidual
open QRich
open SourceGeneratedCenteredGram
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation
open scoped TensorProduct

noncomputable section

/-- The q-rich scale is the cardinal shadow of the compiler-generated next
unit history, not an independently chosen analytic constant. -/
theorem blockQRichSuccessorScale_eq_nextRootHistory (stage : Nat) :
    blockQRichSuccessorScale stage =
      (CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory
        (stage + 1)).cardinalShadow := by
  rw [blockQRichSuccessorScale_eq_stage_add_three,
    CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory_cardinalShadow]

theorem stageSqrtScaleUnit_square_eq_rootScale (stage : Nat) :
    scaleSquare (stageSqrtScaleUnit stage) =
      (blockQRichSuccessorScale stage : ℝ) := by
  unfold scaleSquare scaleValue stageSqrtScaleUnit
  rw [SourceGeneratedPositiveRealCharacter.positiveRealUnit_val,
    Real.sq_sqrt]
  positivity

def pairedOne : QRich.ClozelJPair := (1, 1)

/-- Retained detector coordinate of the paired action at the identity event. -/
def pairedOmegaMeasurementResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : QRich.ClozelJPair :=
  let input := pairedJointInput observation nontrivial scale
  input.measurementFace (input.incidenceResidual (delta 1))

theorem pairedOmegaMeasurementResidual_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    pairedOmegaMeasurementResidual observation nontrivial scale =
      ((selectedOwnerFreeCouplingResidual observation nontrivial scale
          (delta 1)).snd,
        (reversalOwnerFreeCouplingResidual observation nontrivial scale
          (delta 1)).snd) := by
  rfl

theorem pairedMeasurementRead_delta_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (pairedJointInput observation nontrivial (1 : Units NNReal)).measurementRead
        (delta 1) = pairedOne := by
  apply Prod.ext
  · change (selectedIntegralGraphOrbit observation nontrivial (delta 1)).snd = 1
    rw [selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]
  · change (reversalIntegralGraphOrbit observation nontrivial (delta 1)).snd = 1
    rw [reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]

/-- The target of the root-scale action is reconstructed from `1 - residual`
and normalized only by the source-generated quarter-density weight. -/
def normalizedRetainedPair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : QRich.ClozelJPair :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ •
    (pairedOne - pairedOmegaMeasurementResidual observation nontrivial scale)

theorem normalizedRetainedPair_eq_jointStateModulePairEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    normalizedRetainedPair observation nontrivial scale =
      jointStateModulePairEvaluation observation nontrivial (delta scale) := by
  rw [normalizedRetainedPair, pairedOmegaMeasurementResidual_eq]
  change
    (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ •
      (pairedOne -
        ((selectedOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd,
          (reversalOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd)) = _
  rw [show pairedOne -
        ((selectedOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd,
          (reversalOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd) =
      (pairedJointInput observation nontrivial scale).measurementRead
        (delta scale) by
    apply Prod.ext
    · rw [Prod.fst_sub]
      change 1 -
          (selectedOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd =
        (selectedIntegralGraphOrbit observation nontrivial (delta scale)).snd
      rw [selectedOwnerFreeCouplingResidual_delta_snd,
        selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd]
      simp [quarterDilationCharacter, scaleSquare, scaleValue]
    · rw [Prod.snd_sub]
      change 1 -
          (reversalOwnerFreeCouplingResidual observation nontrivial scale
            (delta 1)).snd =
        (reversalIntegralGraphOrbit observation nontrivial (delta scale)).snd
      rw [reversalOwnerFreeCouplingResidual_delta_snd,
        reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_snd]
      simp [quarterDilationCharacter, scaleSquare, scaleValue]]
  exact paired_normalized_measurement_reads_jointStateModulePair
    observation nontrivial scale

def pairedRawActionTarget
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : QRich.ClozelJPair :=
  (pairedJointInput observation nontrivial scale).measurementRead (delta scale)

theorem pairedOmegaMeasurementResidual_eq_one_sub_target
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    pairedOmegaMeasurementResidual observation nontrivial scale =
      pairedOne - pairedRawActionTarget observation nontrivial scale := by
  rw [pairedOmegaMeasurementResidual_eq]
  apply Prod.ext
  · change
      (selectedOwnerFreeCouplingResidual observation nontrivial scale
          (delta 1)).snd =
        1 - (selectedIntegralGraphOrbit observation nontrivial
          (delta scale)).snd
    rw [selectedOwnerFreeCouplingResidual_delta_snd,
      selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]
  · change
      (reversalOwnerFreeCouplingResidual observation nontrivial scale
          (delta 1)).snd =
        1 - (reversalIntegralGraphOrbit observation nontrivial
          (delta scale)).snd
    rw [reversalOwnerFreeCouplingResidual_delta_snd,
      reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]

def pairedRootPhaseResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : QRich.ClozelJPair :=
  let source := (zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root
  let action := positiveMellinQuarterGraphTargetIsometry
    (Real.log (scaleSquare scale))
  (1 - normalizedAutocorrelation source.2.selectedSpectralState action,
    1 - normalizedAutocorrelation source.2.reversalSpectralState action)

def pairedRootCenteredTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : QRich.ClozelJPair :=
  let source := (zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root
  let target := pairedRawActionTarget observation nontrivial scale
  let action := positiveMellinQuarterGraphTargetIsometry
    (Real.log (scaleSquare scale))
  (centeredGramResidual target.1 source.2.selectedSpectralState action,
    centeredGramResidual target.2 source.2.reversalSpectralState action)

/-- At every compiler-generated q-scale, the old phase residual is the
retained paired-`Omega` incidence plus the centered forced trace. -/
theorem pairedRootPhaseResidual_eq_incidence_add_centeredTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    pairedRootPhaseResidual observation nontrivial scale =
      pairedOmegaMeasurementResidual observation nontrivial scale +
        pairedRootCenteredTrace observation nontrivial scale := by
  rw [pairedOmegaMeasurementResidual_eq_one_sub_target]
  apply Prod.ext <;>
    simp [pairedRootPhaseResidual, pairedRootCenteredTrace,
      pairedRawActionTarget, pairedOne, centeredGramResidual]

def stageZeroPhaseResidualPair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QRich.ClozelJPair :=
  (selectedStageZeroPhaseBalanceResidual observation nontrivial,
    reversalStageZeroPhaseBalanceResidual observation nontrivial)

def stageZeroCenteredTracePair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QRich.ClozelJPair :=
  (selectedStageZeroCenteredGramResidual observation nontrivial,
    reversalStageZeroCenteredGramResidual observation nontrivial)

/-- Existing residual conservation with its retained term identified as the
measurement face of the one paired `Omega` incidence. -/
theorem stageZero_phase_eq_pairedOmega_add_centeredTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    stageZeroPhaseResidualPair observation nontrivial =
      pairedOmegaMeasurementResidual observation nontrivial
          stageZeroQuarterScaleUnit +
        stageZeroCenteredTracePair observation nontrivial := by
  apply Prod.ext
  · exact selected_stageZero_phase_residual_split observation nontrivial
  · exact reversal_stageZero_phase_residual_split observation nontrivial

theorem normalizedRetainedPair_fst_eq_selectedReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (normalizedRetainedPair observation nontrivial
        (stageSqrtScaleUnit stage)).1 =
      selectedPositiveMellinDilationReadback observation nontrivial stage := by
  rw [normalizedRetainedPair_eq_jointStateModulePairEvaluation]
  change jointStateModuleSelectedEvaluation observation nontrivial
      (delta (stageSqrtScaleUnit stage)) = _
  rw [jointStateModuleSelectedEvaluation_eq_graph,
    selectedGraphCharacterEvaluation_eq_integralOccurrence]
  exact selected_sqrt_basis_readback observation nontrivial stage

theorem normalizedRetainedPair_snd_eq_reversalReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (normalizedRetainedPair observation nontrivial
        (stageSqrtScaleUnit stage)).2 =
      reversalPositiveMellinDilationReadback observation nontrivial stage := by
  rw [normalizedRetainedPair_eq_jointStateModulePairEvaluation]
  change jointStateModuleReversalEvaluation observation nontrivial
      (delta (stageSqrtScaleUnit stage)) = _
  rw [jointStateModuleReversalEvaluation_eq_graph,
    reversalGraphCharacterEvaluation_eq_integralOccurrence]
  exact reversal_sqrt_basis_readback observation nontrivial stage

/-- Logarithmic current extracted from the actual retained `Omega` target. -/
def omegaLogNormEffect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℝ :=
  let retained := normalizedRetainedPair observation nontrivial
    (stageSqrtScaleUnit stage)
  (2 / Real.log (blockQRichSuccessorScale stage : ℝ)) *
    (Real.log ‖retained.2‖ - Real.log ‖retained.1‖)

theorem omegaLogNormEffect_eq_coordinateResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    omegaLogNormEffect observation nontrivial stage =
      2 * observation.coordinate.re - 1 := by
  let q : ℝ := blockQRichSuccessorScale stage
  have qOne : 1 < q := by
    dsimp [q]
    exact qRichSuccessorScale_real_one_lt stage
  have qPos : 0 < q := lt_trans zero_lt_one qOne
  have qLogNe : Real.log q ≠ 0 := ne_of_gt (Real.log_pos qOne)
  rw [omegaLogNormEffect,
    normalizedRetainedPair_snd_eq_reversalReadback,
    normalizedRetainedPair_fst_eq_selectedReadback,
    reversalPositiveMellinDilationReadback_eq_character,
    selectedPositiveMellinDilationReadback_eq_character]
  change (2 / Real.log q) *
      (Real.log ‖(q : ℂ) ^
          (-(coordinateReversal observation.coordinate / 2))‖ -
        Real.log ‖(q : ℂ) ^ (-(observation.coordinate / 2))‖) = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos qPos,
    Complex.norm_cpow_eq_rpow_re_of_pos qPos,
    Real.log_rpow qPos, Real.log_rpow qPos]
  simp only [neg_re, div_ofNat_re]
  simp [coordinateReversal]
  field_simp [qLogNe]
  ring

theorem omegaLogNormEffect_complex_eq_endpointCoefficient
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (omegaLogNormEffect observation nontrivial stage : ℂ) =
      observation.coordinate - coordinateReversal observation.coordinate := by
  rw [omegaLogNormEffect_eq_coordinateResidual]
  apply Complex.ext
  · simp [coordinateReversal]
    ring
  · simp [coordinateReversal]

theorem omegaLogNormEffect_eq_zero_iff_fixed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    omegaLogNormEffect observation nontrivial stage = 0 ↔
      observation.coordinate = coordinateReversal observation.coordinate := by
  constructor
  · intro effectZero
    have complexZero :
        (omegaLogNormEffect observation nontrivial stage : ℂ) = 0 := by
      rw [effectZero]
      norm_num
    rw [omegaLogNormEffect_complex_eq_endpointCoefficient] at complexZero
    exact sub_eq_zero.mp complexZero
  · intro fixed
    have complexZero :
        (omegaLogNormEffect observation nontrivial stage : ℂ) = 0 := by
      rw [omegaLogNormEffect_complex_eq_endpointCoefficient]
      exact sub_eq_zero.mpr fixed
    exact Complex.ofReal_eq_zero.mp complexZero

/-- The existing arithmetic endpoint relation write is the image of the
retained paired-`Omega` log current, not a parallel scalar comparison. -/
theorem endpointDifferential_eq_pairedOmegaRootEffect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (characterStage endpointStage : Nat) :
    complexLocalFactorizationDifferential endpointStage
        (zeroPayloadLocalEndpointValue endpointStage
          (zeroOwnedProperMellinLowHighRelativeOccurrence
            observation nontrivial).root.1) =
      (omegaLogNormEffect observation nontrivial characterStage : ℂ) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation endpointStage := by
  rw [occurrence_root_differential_normalForm,
    omegaLogNormEffect_complex_eq_endpointCoefficient]

/-- Direct q-rich consumer: the branch-normalized separator is exactly the
faithful row coefficient times the retained paired-`Omega` root effect. -/
theorem branchNormalizedSeparator_eq_pairedOmegaRootEffect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation) stage row =
      -(quotientCoefficient row : ℂ) *
        (omegaLogNormEffect observation nontrivial characterStage : ℂ) := by
  rw [mathlibLeft_branchNormalizedSeparator_eq_clozelCross,
    clozelJCrossCoefficient_eq_coordinateResidual,
    omegaLogNormEffect_complex_eq_endpointCoefficient]

theorem branchNormalizedSeparator_eq_zero_iff_omegaRootEffect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator
          (mathlibLeftRegressionComponent observation) stage row = 0 ↔
      omegaLogNormEffect observation nontrivial characterStage = 0 := by
  rw [branchNormalizedSeparator_eq_pairedOmegaRootEffect
    observation nontrivial characterStage stage row]
  have coefficientNe : -(quotientCoefficient row : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
      (blockQRichQuotientCoefficient_ne_zero stage row))
  constructor
  · intro productZero
    have effectComplexZero :=
      (mul_eq_zero.mp productZero).resolve_left coefficientNe
    exact Complex.ofReal_eq_zero.mp effectComplexZero
  · intro effectZero
    rw [effectZero]
    norm_num

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
