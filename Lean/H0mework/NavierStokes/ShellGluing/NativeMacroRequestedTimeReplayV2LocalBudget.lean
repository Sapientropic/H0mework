import H0mework.NavierStokes.InitialData.SourceOwnedLocalCompactnessBudget
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2Runtime
import H0mework.NavierStokes.ShellSources.InfiniteLineageHilbertCompletion

/-!
# Source-owned local budgets on the unconditional V2 replay

Every V2 Galerkin stage starts from the same actual physical state.  Support
refinement adds only initially zero rows, so the source-generated local
duration and every compactness constant are independent of the stage.

This module puts that fact on the exact V2 runtime.  It does not accept a
trajectory, cutoff, support target, smallness margin, or analytic budget.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget

open scoped BigOperators Topology Interval ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime

noncomputable section

/-- The positive local horizon is selected once from the exact physical
state at the native macro contact. -/
def sourceOwnedLocalReplayV2Duration
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  sourceOwnedLocalDuration ν
    (lineageReceiptModes lineage 0)
    (commonTimeReplayInitialState lineage)

theorem sourceOwnedLocalReplayV2Duration_pos
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    0 < sourceOwnedLocalReplayV2Duration lineage :=
  sourceOwnedLocalDuration_pos ν
    (lineageReceiptModes lineage 0)
    (commonTimeReplayInitialState lineage)

/-- Every support-refined stage measures exactly the same initial
coefficient enstrophy as the first native support. -/
theorem requestedTimeReplayV2Stage_initialCoefficientEnstrophy
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage : GeneratedRequestedTimeReplayV2Stage lineage requestedTime) :
    finiteStateVorticityCoefficientEnstrophy
        stage.modes (stage.trajectory 0) =
      finiteStateVorticityCoefficientEnstrophy
        (lineageReceiptModes lineage 0)
        (commonTimeReplayInitialState lineage) := by
  rw [stage.initial]
  apply le_antisymm
  · exact
      finiteStateVorticityCoefficientEnstrophy_le_of_supported
        stage.modes (lineageReceiptModes lineage 0)
        (commonTimeReplayInitialState lineage)
        (commonTimeReplayInitialState_supported lineage)
  · exact
      finiteStateVorticityCoefficientEnstrophy_mono
        stage.initialModes_subset
        (commonTimeReplayInitialState lineage)

/-- The local lifespan is a whole-family invariant, not a stage-dependent
cutoff. -/
theorem requestedTimeReplayV2Stage_sourceOwnedLocalDuration
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage : GeneratedRequestedTimeReplayV2Stage lineage requestedTime) :
    sourceOwnedLocalDuration ν stage.modes (stage.trajectory 0) =
      sourceOwnedLocalReplayV2Duration lineage := by
  unfold sourceOwnedLocalReplayV2Duration sourceOwnedLocalDuration
    sourceOwnedLocalBarrierSlope sourceOwnedLocalEnstrophyCeiling
  rw [requestedTimeReplayV2Stage_initialCoefficientEnstrophy stage]

/-- One actual V2 stage on the generated local horizon carries all four
uniform local compactness ledgers. -/
theorem requestedTimeReplayV2Stage_sourceOwnedLocalCompactnessBudget
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage :
      GeneratedRequestedTimeReplayV2Stage lineage
        (sourceOwnedLocalReplayV2Duration lineage)) :
    (∀ t ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
        finiteStateVorticityCoefficientEnstrophy
            stage.modes (stage.trajectory t) ≤
          sourceOwnedLocalEnstrophyCeiling
            (lineageReceiptModes lineage 0)
            (commonTimeReplayInitialState lineage)) ∧
      (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
              finiteStateVorticityEnstrophyMass
                stage.modes (stage.trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
            (lineageReceiptModes lineage 0)
            (commonTimeReplayInitialState lineage) +
          sourceOwnedLocalQuadraticCoefficient ν
              (sourceOwnedLocalEnstrophyCeiling
                (lineageReceiptModes lineage 0)
                (commonTimeReplayInitialState lineage)) *
            sourceOwnedLocalEnstrophyCeiling
                (lineageReceiptModes lineage 0)
                (commonTimeReplayInitialState lineage) ^ 2 *
            sourceOwnedLocalReplayV2Duration lineage ∧
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVelocityMajorant stage.modes (stage.trajectory t) ^ 2) ≤
        2 * sourceOwnedLocalCoreVelocityCoefficient ν
              (sourceOwnedLocalEnstrophyCeiling
                (lineageReceiptModes lineage 0)
                (commonTimeReplayInitialState lineage)) *
            sourceOwnedLocalEnstrophyCeiling
              (lineageReceiptModes lineage 0)
              (commonTimeReplayInitialState lineage) *
            sourceOwnedLocalReplayV2Duration lineage +
          2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν
              (sourceOwnedLocalEnstrophyCeiling
                (lineageReceiptModes lineage 0)
                (commonTimeReplayInitialState lineage)) *
            (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
              finiteStateVorticityEnstrophyMass
                stage.modes (stage.trajectory t)) ∧
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVorticityNegativeOneMass stage.modes
            (finiteStateVorticityGenerator
              stage.modes ν.coeff (stage.trajectory t))) ≤
        8 * sourceOwnedLocalEnstrophyCeiling
              (lineageReceiptModes lineage 0)
              (commonTimeReplayInitialState lineage) *
            (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
              finiteStateVelocityMajorant
                stage.modes (stage.trajectory t) ^ 2) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
              finiteStateVorticityEnstrophyMass
                stage.modes (stage.trajectory t)) := by
  have budget :=
    finiteStateVorticity_sourceOwnedLocalCompactnessBudget_on_Icc
      stage.modes stage.waveNeg_mem ν stage.trajectory
      (sourceOwnedLocalReplayV2Duration lineage)
      (sourceOwnedLocalReplayV2Duration_pos lineage).le
      (requestedTimeReplayV2Stage_sourceOwnedLocalDuration stage).ge
      (fun t tMem => (stage.physical t tMem).1)
      (fun t tMem => (stage.physical t tMem).2.2.2)
      (fun t tMem wave waveMem =>
        (stage.physical t tMem).2.2.1 wave)
  have initialEnstrophy :=
    requestedTimeReplayV2Stage_initialCoefficientEnstrophy stage
  simpa [sourceOwnedLocalEnstrophyCeiling,
    finiteStateVorticityHalfEnstrophy, initialEnstrophy] using budget

/-! ## Uniform whole-family constants generated by the same source contact -/

def sourceOwnedLocalReplayV2EnstrophyCeiling
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  sourceOwnedLocalEnstrophyCeiling
    (lineageReceiptModes lineage 0)
    (commonTimeReplayInitialState lineage)

def sourceOwnedLocalReplayV2GradientCeiling
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  let ceiling := sourceOwnedLocalReplayV2EnstrophyCeiling lineage
  (finiteStateVorticityHalfEnstrophy
        (lineageReceiptModes lineage 0)
        (commonTimeReplayInitialState lineage) +
      sourceOwnedLocalQuadraticCoefficient ν ceiling * ceiling ^ 2 *
        sourceOwnedLocalReplayV2Duration lineage) /
    ((3 * ν.coeff / 8) * (2 * Real.pi) ^ 2)

def sourceOwnedLocalReplayV2VelocityCeiling
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  let ceiling := sourceOwnedLocalReplayV2EnstrophyCeiling lineage
  2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling * ceiling *
      sourceOwnedLocalReplayV2Duration lineage +
    2 * biotSavartSerrinConstant *
      sourceOwnedKernelTailTolerance ν ceiling *
      sourceOwnedLocalReplayV2GradientCeiling lineage

def sourceOwnedLocalReplayV2NegativeOneCeiling
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  8 * sourceOwnedLocalReplayV2EnstrophyCeiling lineage *
      sourceOwnedLocalReplayV2VelocityCeiling lineage +
    2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
      sourceOwnedLocalReplayV2GradientCeiling lineage

theorem sourceOwnedLocalReplayV2GradientCoefficient_pos
    (ν : Viscosity) :
    0 < (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 := by
  exact mul_pos
    (div_pos (mul_pos (by norm_num) ν.coeff_pos) (by norm_num))
    (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))

theorem sourceOwnedLocalReplayV2GradientCeiling_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    0 ≤ sourceOwnedLocalReplayV2GradientCeiling lineage := by
  unfold sourceOwnedLocalReplayV2GradientCeiling
  apply div_nonneg
  · apply add_nonneg
    · exact finiteStateVorticityHalfEnstrophy_nonneg _ _
    · exact mul_nonneg
        (mul_nonneg
          (sourceOwnedLocalQuadraticCoefficient_nonneg ν _)
          (sq_nonneg _))
        (sourceOwnedLocalReplayV2Duration_pos lineage).le
  · exact (sourceOwnedLocalReplayV2GradientCoefficient_pos ν).le

theorem sourceOwnedLocalReplayV2VelocityCeiling_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    0 ≤ sourceOwnedLocalReplayV2VelocityCeiling lineage := by
  unfold sourceOwnedLocalReplayV2VelocityCeiling
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (sourceOwnedLocalCoreVelocityCoefficient_nonneg ν _))
        (sourceOwnedLocalEnstrophyCeiling_pos _ _).le)
      (sourceOwnedLocalReplayV2Duration_pos lineage).le)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (sourceOwnedKernelTailTolerance_pos ν _).le)
      (sourceOwnedLocalReplayV2GradientCeiling_nonneg lineage))

theorem sourceOwnedLocalReplayV2NegativeOneCeiling_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    0 ≤ sourceOwnedLocalReplayV2NegativeOneCeiling lineage := by
  unfold sourceOwnedLocalReplayV2NegativeOneCeiling
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (sourceOwnedLocalEnstrophyCeiling_pos _ _).le)
      (sourceOwnedLocalReplayV2VelocityCeiling_nonneg lineage))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (sq_nonneg _))
      (sourceOwnedLocalReplayV2GradientCeiling_nonneg lineage))

/-- Uniform compactness package for an arbitrary actual V2 stage.  Every
constant is computed from the common source contact, while the integrals
remain attached to this exact stage trajectory. -/
theorem requestedTimeReplayV2Stage_uniformLocalCompactnessBudget
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage :
      GeneratedRequestedTimeReplayV2Stage lineage
        (sourceOwnedLocalReplayV2Duration lineage)) :
    (∀ t ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
        finiteStateVorticityCoefficientEnstrophy
            stage.modes (stage.trajectory t) ≤
          sourceOwnedLocalReplayV2EnstrophyCeiling lineage) ∧
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVorticityEnstrophyMass
            stage.modes (stage.trajectory t)) ≤
        sourceOwnedLocalReplayV2GradientCeiling lineage ∧
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVelocityMajorant
            stage.modes (stage.trajectory t) ^ 2) ≤
        sourceOwnedLocalReplayV2VelocityCeiling lineage ∧
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVorticityNegativeOneMass stage.modes
            (finiteStateVorticityGenerator
              stage.modes ν.coeff (stage.trajectory t))) ≤
        sourceOwnedLocalReplayV2NegativeOneCeiling lineage := by
  obtain ⟨enstrophy, gradientWeighted, velocityRaw, negativeRaw⟩ :=
    requestedTimeReplayV2Stage_sourceOwnedLocalCompactnessBudget stage
  have gradient :
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVorticityEnstrophyMass
            stage.modes (stage.trajectory t)) ≤
        sourceOwnedLocalReplayV2GradientCeiling lineage := by
    apply (le_div_iff₀
      (sourceOwnedLocalReplayV2GradientCoefficient_pos ν)).2
    simpa [sourceOwnedLocalReplayV2GradientCeiling,
      sourceOwnedLocalReplayV2EnstrophyCeiling, mul_comm, mul_left_comm,
      mul_assoc] using gradientWeighted
  have velocityCoefficientNonneg :
      0 ≤ 2 * biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν
          (sourceOwnedLocalReplayV2EnstrophyCeiling lineage) :=
    mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (sourceOwnedKernelTailTolerance_pos ν _).le
  have velocity :
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVelocityMajorant
            stage.modes (stage.trajectory t) ^ 2) ≤
        sourceOwnedLocalReplayV2VelocityCeiling lineage := by
    refine velocityRaw.trans ?_
    unfold sourceOwnedLocalReplayV2VelocityCeiling
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left gradient velocityCoefficientNonneg)
  have negativeVelocityCoefficientNonneg :
      0 ≤ 8 * sourceOwnedLocalReplayV2EnstrophyCeiling lineage :=
    mul_nonneg (by norm_num)
      (sourceOwnedLocalEnstrophyCeiling_pos _ _).le
  have negativeGradientCoefficientNonneg :
      0 ≤ 2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have negative :
      (∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          finiteStateVorticityNegativeOneMass stage.modes
            (finiteStateVorticityGenerator
              stage.modes ν.coeff (stage.trajectory t))) ≤
        sourceOwnedLocalReplayV2NegativeOneCeiling lineage := by
    refine negativeRaw.trans ?_
    unfold sourceOwnedLocalReplayV2NegativeOneCeiling
    exact add_le_add
      (mul_le_mul_of_nonneg_left velocity
        negativeVelocityCoefficientNonneg)
      (mul_le_mul_of_nonneg_left gradient
        negativeGradientCoefficientNonneg)
  exact
    ⟨by simpa [sourceOwnedLocalReplayV2EnstrophyCeiling] using enstrophy,
      gradient, velocity, negative⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
end NavierStokes
end SaturationMonoid
