import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaQuarterScaleRuntimeReadback

/-!
# Quarter-scale runtime modulus current

The fixed-root quarter rows do not need their raw incidence to vanish.  The
faithful radial read is the selected/reversal modulus imbalance of the target
reconstructed as `1 - retained`.  This scratch file proves that the same read
is available from the retained row, the incidence measurement, and the
phase-minus-centered-trace conservation projection, and identifies its zero
fibre with the existing Mellin radial defect, Omega log-norm effect, and
q-rich separator.  This is the faithful nonlinear read of the already
installed fixed-root relation, not a new classifier or a raw-incidence zero
claim.
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
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open Character.GlobalCoPoissonCurrent
open QRich
open InverseZeroFibre

noncomputable section

/-- Radial detector on a retained paired incidence.  It measures the modulus
imbalance of the reconstructed action target, not the incidence itself. -/
def retainedTargetModulusImbalance (retained : QRich.ClozelJPair) : ℝ :=
  ‖1 - retained.1‖ - ‖1 - retained.2‖

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

/-- The named retained row reads the already installed stage-zero raw radial
current exactly. -/
theorem runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent :
    retainedTargetModulusImbalance
        (runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterRetained))) =
      stageZeroRawRadialCurrent observation nontrivial := by
  change retainedTargetModulusImbalance
      (runtimeJointQuarterRetainedAt observation nontrivial 0) = _
  unfold runtimeJointQuarterRetainedAt
  rw [runtimeJointQuarterScaleUnit_zero]
  rw [pairedOmegaMeasurementResidual_eq]
  unfold retainedTargetModulusImbalance stageZeroRawRadialCurrent
  rw [selected_stageZero_detectorResidual_at_identity,
    reversal_stageZero_detectorResidual_at_identity]
  ring_nf

/-- The measurement projection of the named incidence has the same radial
read; no zero equation is asserted for the raw graph incidence. -/
theorem runtimeQuarterIncidence_modulusImbalance_eq_stageZeroRawRadialCurrent :
    retainedTargetModulusImbalance
        (runtimeJointMeasurementFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterIncidence))) =
      stageZeroRawRadialCurrent observation nontrivial := by
  rw [runtimeQuarterIncidence_measurement_eq_retained]
  exact runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent
    observation nontrivial

/-- Conservation reconstructs the same retained target from the phase and
centered-trace rows. -/
theorem runtimeQuarterPhase_sub_centeredTrace_eq_retained :
    runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterPhase)) -
        runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterCenteredTrace)) =
      runtimeJointBalanceFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .quarterRetained)) := by
  change runtimeJointQuarterPhaseAt observation nontrivial 0 -
      runtimeJointQuarterCenteredTraceAt observation nontrivial 0 =
    runtimeJointQuarterRetainedAt observation nontrivial 0
  rw [runtimeJointQuarterEffect_conservation]
  abel

theorem runtimeQuarterPhaseTrace_modulusImbalance_eq_stageZeroRawRadialCurrent :
    retainedTargetModulusImbalance
        (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterPhase)) -
          runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterCenteredTrace))) =
      stageZeroRawRadialCurrent observation nontrivial := by
  rw [runtimeQuarterPhase_sub_centeredTrace_eq_retained]
  exact runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent
    observation nontrivial

/-- The fixed-root quarter current and the existing positive-Mellin radial
defect have exactly the same zero fibre. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_radialDefect_zero :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      zeroOwnedPositiveMellinRadialDefect observation nontrivial 0 = 0 := by
  rw [runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent,
    stageZeroRawRadialCurrent_eq_zero_iff,
    zeroOwnedPositiveMellinRadialDefect_eq_zero_iff]

/-- The same zero fibre is the integral-character radial current carried by
the common source occurrence. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_groupRingRadialCurrent_zero :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      groupRingRadialCurrent observation 0 = 0 := by
  rw [runtimeQuarterModulusImbalance_eq_zero_iff_radialDefect_zero,
    groupRingRadialCurrent_eq_zeroOwnedPositiveMellinRadialDefect]

/-- And it is the zero fibre of the already coupled Riesz flux current. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_radialRieszFlux_zero :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      radialRieszFluxResidual observation nontrivial 0 = 0 := by
  rw [runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent,
    stageZeroRawRadialCurrent_eq_zero_iff_rieszFlux]

/-- The same zero fibre is the already generated Omega log-norm effect. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_omegaLogNormEffect_zero
    (characterStage : Nat) :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      omegaLogNormEffect observation nontrivial characterStage = 0 := by
  rw [runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent,
    stageZeroRawRadialCurrent_eq_zero_iff,
    omegaLogNormEffect_eq_zero_iff_fixed]
  constructor
  · intro critical
    apply Complex.ext
    · simp [coordinateReversal]
      linarith
    · simp [coordinateReversal]
  · intro fixed
    have realFixed := congrArg Complex.re fixed
    simp [coordinateReversal] at realFixed
    linarith

/-- The same zero fibre is already stored in the emitted root effect row's
`logNorm` field. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_installedLogNorm_zero
    (depth : Nat) :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      (installedRuntimeEffectValueAt observation nontrivial depth).logNorm = 0 := by
  rw [installedRuntimeEffectValueAt_logNorm]
  exact runtimeQuarterModulusImbalance_eq_zero_iff_omegaLogNormEffect_zero
    observation nontrivial depth

/-- Direct q-rich consumer: separator vanishing is equivalent to vanishing
of the one faithful modulus imbalance projected from the fixed-root quarter
rows. -/
theorem runtimeQuarterModulusImbalance_eq_zero_iff_separator_zero
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0 ↔
      branchNormalizedQRichSeparator
          (mathlibLeftRegressionComponent observation) stage row = 0 := by
  rw [runtimeQuarterModulusImbalance_eq_zero_iff_omegaLogNormEffect_zero
      observation nontrivial characterStage,
    branchNormalizedSeparator_eq_zero_iff_omegaRootEffect_zero]

/-- Strongest typed readback: all three installed presentations expose one
and the same target modulus imbalance, and its vanishing is exactly the
existing terminal separator condition. -/
theorem runtimeQuarterFixedRoot_modulusCurrent_terminal_readback
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    let retained := runtimeJointBalanceFace
      (runtimeJointRelationGeneratorValue observation nontrivial
        (0, .quarterRetained))
    let incidence := runtimeJointMeasurementFace
      (runtimeJointRelationGeneratorValue observation nontrivial
        (0, .quarterIncidence))
    let phaseTrace :=
      runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterPhase)) -
        runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterCenteredTrace))
    retainedTargetModulusImbalance retained =
        stageZeroRawRadialCurrent observation nontrivial ∧
      retainedTargetModulusImbalance incidence =
        stageZeroRawRadialCurrent observation nontrivial ∧
      retainedTargetModulusImbalance phaseTrace =
        stageZeroRawRadialCurrent observation nontrivial ∧
      (retainedTargetModulusImbalance retained = 0 ↔
        zeroOwnedPositiveMellinRadialDefect observation nontrivial 0 = 0) ∧
      (retainedTargetModulusImbalance retained = 0 ↔
        groupRingRadialCurrent observation 0 = 0) ∧
      (retainedTargetModulusImbalance retained = 0 ↔
        omegaLogNormEffect observation nontrivial characterStage = 0) ∧
      (retainedTargetModulusImbalance retained = 0 ↔
        (installedRuntimeEffectValueAt observation nontrivial
          characterStage).logNorm = 0) ∧
      (retainedTargetModulusImbalance retained = 0 ↔
        branchNormalizedQRichSeparator
          (mathlibLeftRegressionComponent observation) stage row = 0) := by
  dsimp only
  refine ⟨runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent
      observation nontrivial, ?_⟩
  refine ⟨runtimeQuarterIncidence_modulusImbalance_eq_stageZeroRawRadialCurrent
      observation nontrivial, ?_⟩
  refine ⟨runtimeQuarterPhaseTrace_modulusImbalance_eq_stageZeroRawRadialCurrent
      observation nontrivial, ?_⟩
  refine ⟨runtimeQuarterModulusImbalance_eq_zero_iff_radialDefect_zero
      observation nontrivial, ?_⟩
  refine ⟨runtimeQuarterModulusImbalance_eq_zero_iff_groupRingRadialCurrent_zero
      observation nontrivial, ?_⟩
  refine ⟨runtimeQuarterModulusImbalance_eq_zero_iff_omegaLogNormEffect_zero
      observation nontrivial characterStage, ?_⟩
  refine ⟨runtimeQuarterModulusImbalance_eq_zero_iff_installedLogNorm_zero
      observation nontrivial characterStage,
    runtimeQuarterModulusImbalance_eq_zero_iff_separator_zero
      observation nontrivial characterStage stage row⟩

/-- Named terminal consumer.  The remaining producer contract is exactly
uniform vanishing of the fixed-root quarter modulus current; no raw incidence
or character-value equality is requested. -/
theorem riemannHypothesis_of_all_runtimeQuarterModulusImbalance_zero
    (allZero : ∀ (observation : GeneratedRiemannZeroObservation)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)),
      retainedTargetModulusImbalance
          (runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterRetained))) = 0) :
    RiemannHypothesis := by
  apply QRich.riemannHypothesis_of_branchNormalizedQRichSeparator_zero
  intro coordinate zetaZero nontrivial _notPole
  let observation :=
    GeneratedRiemannZeroObservation.ofMathlibZero coordinate zetaZero
  have observationNontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1) := by
    simpa [observation] using nontrivial
  apply (runtimeQuarterModulusImbalance_eq_zero_iff_separator_zero
    observation observationNontrivial 0 terminalReadbackStage
      terminalReadbackRow).1
  exact allZero observation observationNontrivial

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
