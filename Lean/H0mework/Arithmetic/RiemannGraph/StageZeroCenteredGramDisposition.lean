import H0mework.Realization.Topology.GramDisposition
import H0mework.Arithmetic.RiemannCharacter.ZeroRieszJConservation
import H0mework.Arithmetic.RiemannGraph.GraphTargetOwnerFreeDilation
import H0mework.Arithmetic.RiemannGraph.ZeroJointStateModuleOccurrence
import H0mework.Arithmetic.RiemannLineage.SeparatorFixednessConsumer

/-!
# Stage-zero centered Gram disposition

At the actual `√3` scale, both source.2-generated Riesz states are tested by
one owner-free graph-target dilation.  Existing J stationarity supplies paired
conservation.  The generic total disposition either produces exact neutral
centered-Gram readback or retains a labelled hidden-channel coordinate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open Character.GlobalCoPoissonCurrent
open SourceGeneratedCenteredGram
open SourceGeneratedFunctionalGraphPerfectification
open QRich
open InverseZeroFibre

noncomputable section

/-- Actual Archimedean square-root scale attached to q-rich stage zero. -/
def stageZeroSqrtScale : ℝ :=
  Real.sqrt (QRich.blockQRichSuccessorScale 0 : ℝ)

theorem stageZeroSqrtScale_pos : 0 < stageZeroSqrtScale := by
  unfold stageZeroSqrtScale
  rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
  positivity

theorem stageZeroSqrtScale_one_lt : 1 < stageZeroSqrtScale := by
  have square : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    rw [sq, Real.mul_self_sqrt]
    norm_num
  have nonnegative : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  unfold stageZeroSqrtScale
  rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
  norm_num
  nlinarith

theorem stageZeroSqrtScale_unit_value :
    positiveUnitValue (stageSqrtScaleUnit 0) = stageZeroSqrtScale := by
  unfold stageSqrtScaleUnit positiveUnitValue stageZeroSqrtScale
  rw [SourceGeneratedPositiveRealCharacter.positiveRealUnit_val]

def selectedStageZeroRawRieszTarget
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  selectedDilationTrace observation nontrivial
    (zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root
    stageZeroSqrtScale stageZeroSqrtScale_pos

def reversalStageZeroRawRieszTarget
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  reversalDilationTrace observation nontrivial
    (zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root
    stageZeroSqrtScale stageZeroSqrtScale_pos

/-- Both states see this one action; it has no zero/character input. -/
def stageZeroOwnerFreeGraphTargetAction :
    GraphTarget PositiveMellinQuarterEnergy ≃ₗᵢ[ℂ]
      GraphTarget PositiveMellinQuarterEnergy :=
  positiveMellinQuarterGraphTargetPositiveDilationAction
    (stageSqrtScaleUnit 0)

/-- Selected state read from the installed joint occurrence, rather than
reconstructed along a parallel route. -/
def selectedStageZeroJointState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GraphTarget PositiveMellinQuarterEnergy :=
  ((zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root.2).selectedSpectralState

def reversalStageZeroJointState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GraphTarget PositiveMellinQuarterEnergy :=
  ((zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root.2).reversalSpectralState

theorem selectedStageZeroJointState_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedStageZeroJointState observation nontrivial ≠ 0 :=
  zeroOwnedJointStateModuleOccurrence_root_selectedState_ne_zero
    observation nontrivial

theorem reversalStageZeroJointState_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalStageZeroJointState observation nontrivial ≠ 0 :=
  zeroOwnedJointStateModuleOccurrence_root_reversalState_ne_zero
    observation nontrivial

theorem stageZeroOwnerFreeGraphTargetAction_eq_rawScale :
    stageZeroOwnerFreeGraphTargetAction =
      positiveMellinQuarterGraphTargetIsometry
        (Real.log stageZeroSqrtScale) := by
  apply LinearIsometryEquiv.ext
  intro value
  apply (WithLp.linearEquiv 2 ℂ
    (PositiveMellinQuarterEnergy × ℂ)).injective
  apply Prod.ext
  · change positiveMellinQuarterEnergyTranslationIsometry
        (Real.log (positiveUnitValue (stageSqrtScaleUnit 0))) value.fst =
      positiveMellinQuarterEnergyTranslationIsometry
        (Real.log stageZeroSqrtScale) value.fst
    rw [stageZeroSqrtScale_unit_value]
  · rfl

def selectedStageZeroCenteredGramResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  centeredGramResidual
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction

def reversalStageZeroCenteredGramResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : ℂ :=
  centeredGramResidual
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction

theorem stageZeroRawRieszTargets_paired_stationarity
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedStageZeroRawRieszTarget observation nontrivial *
        star (reversalStageZeroRawRieszTarget observation nontrivial) = 1 := by
  exact Character.GlobalCoPoissonCurrent.occurrence_rawRieszAmplitude_paired_stationarity
    observation nontrivial stageZeroSqrtScale stageZeroSqrtScale_pos

/-- Total same-action disposition; no neutrality premise enters. -/
def stageZeroCenteredGramDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  settleCenteredGram_sameAction
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)
    (selectedStageZeroJointState_ne_zero observation nontrivial)
    (reversalStageZeroJointState_ne_zero observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction
    (stageZeroRawRieszTargets_paired_stationarity observation nontrivial)

abbrev StageZeroBothCenteredGramRealized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  BothCenteredGramRealized
    (selectedStageZeroRawRieszTarget observation nontrivial)
    (reversalStageZeroRawRieszTarget observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction
    stageZeroOwnerFreeGraphTargetAction

theorem coordinate_re_eq_half_of_stageZeroCenteredGram_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (realized : StageZeroBothCenteredGramRealized observation nontrivial) :
    observation.coordinate.re = 1 / 2 := by
  have targetNorms := realized.target_norms_eq
  unfold selectedStageZeroRawRieszTarget
    reversalStageZeroRawRieszTarget at targetNorms
  rw [occurrence_selectedDilationTrace_eq_character,
    occurrence_reversalDilationTrace_eq_character,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos stageZeroSqrtScale_pos] at targetNorms
  have exponentEquality :=
    (Real.strictMono_rpow_of_base_gt_one
      stageZeroSqrtScale_one_lt).injective targetNorms
  simp [selectedCoPoissonMuntzParameter,
    reversalCoPoissonMuntzParameter, coordinateReversal] at exponentEquality
  linarith

theorem radialRieszFluxResidual_eq_zero_of_stageZeroCenteredGram_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (realized : StageZeroBothCenteredGramRealized observation nontrivial) :
    radialRieszFluxResidual observation nontrivial 0 = 0 := by
  have critical :=
    coordinate_re_eq_half_of_stageZeroCenteredGram_realized
      observation nontrivial realized
  have radialZero :=
    QRich.zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
      observation nontrivial 0 critical
  calc
    radialRieszFluxResidual observation nontrivial 0 =
        groupRingRadialCurrent observation 0 :=
      (groupRingRadialCurrent_eq_radialRieszFluxResidual
        observation nontrivial 0).symm
    _ = QRich.zeroOwnedPositiveMellinRadialDefect
          observation nontrivial 0 :=
      groupRingRadialCurrent_eq_zeroOwnedPositiveMellinRadialDefect
        observation nontrivial 0
    _ = 0 := radialZero

theorem terminalSeparator_eq_zero_of_stageZeroCenteredGram_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (realized : StageZeroBothCenteredGramRealized observation nontrivial) :
    branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation)
        terminalReadbackStage terminalReadbackRow = 0 := by
  have critical :=
    coordinate_re_eq_half_of_stageZeroCenteredGram_realized
      observation nontrivial realized
  have radialZero :=
    QRich.zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
      observation nontrivial 0 critical
  exact branchNormalizedQRichSeparator_eq_zero_of_radialDefect_zero
    observation nontrivial 0 terminalReadbackStage terminalReadbackRow
      radialZero

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
