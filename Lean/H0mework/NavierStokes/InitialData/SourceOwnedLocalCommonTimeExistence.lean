import H0mework.NavierStokes.InitialData.SourceOwnedLocalKernelAbsorption
import H0mework.NavierStokes.Galerkin.CommonTimeExistence

/-!
# Source-owned supercritical common-time Galerkin existence

The generated local kernel barrier supplies a positive time depending only
on viscosity and the actual initial coefficient enstrophy, not on the finite
Galerkin inventory beyond its restriction of that same initial state.

This module feeds that barrier into the existing native Picard restart and
physical splice mechanism.  Every fixed finite physical carrier therefore
produces an actual unforced trajectory on the complete generated local time.
The source chooses the kernel core, ceiling, restart radius, local Picard
windows, number of splices, and final restriction.  No continuation path,
cutoff, tail bound, smallness knob, or target trajectory is a premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalCommonTimeExistence

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption

noncomputable section

/-- Every finite physical Galerkin carrier generates an actual unforced
trajectory on the cutoff-independent time selected by its actual initial
enstrophy and viscosity. -/
theorem exists_finitePhysicalTrajectory_on_sourceOwnedLocalDuration
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (initialState : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ modes → initialState wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ initialState wave = 0)
    (reality : FiniteStateFourierReality initialState) :
    ∃ trajectory : ℝ → ComplexVorticityHilbertState,
      trajectory 0 = initialState ∧
        ∀ t ∈ Icc (0 : ℝ)
            (sourceOwnedLocalDuration ν modes initialState),
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                modes ν.coeff (trajectory t)) t ∧
            (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) := by
  let ceiling := sourceOwnedLocalEnstrophyCeiling modes initialState
  let duration := sourceOwnedLocalDuration ν modes initialState
  let innerRadius : NNReal :=
    ⟨Real.sqrt ceiling, Real.sqrt_nonneg ceiling⟩
  have ceilingPos : 0 < ceiling := by
    exact sourceOwnedLocalEnstrophyCeiling_pos modes initialState
  have durationPos : 0 < duration := by
    exact sourceOwnedLocalDuration_pos ν modes initialState
  have initialEnstrophyLe :
      finiteStateVorticityCoefficientEnstrophy modes initialState ≤
        ceiling := by
    dsimp [ceiling, sourceOwnedLocalEnstrophyCeiling]
    linarith
  have initialMem :
      initialState ∈
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) innerRadius := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    exact
      (complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes initialState supported).trans initialEnstrophyLe
  obtain
      ⟨uniformTime, uniformTimePos, uniformLocal⟩ :=
    exists_uniform_finitePhysicalTrajectory
      modes zeroNotMem negClosed ν.coeff innerRadius
  have generatedPrefixes :
      ∀ step : ℕ,
        (step : ℝ) * uniformTime < duration →
          ∃ trajectory : ℝ → ComplexVorticityHilbertState,
            trajectory 0 = initialState ∧
              ∀ t ∈ Icc (0 : ℝ)
                  (((step : ℝ) + 1) * uniformTime),
                HasDerivAt trajectory
                    (finiteStateVorticityGenerator
                      modes ν.coeff (trajectory t)) t ∧
                  (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
                  (∀ wave,
                    complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
                  FiniteStateFourierReality (trajectory t) := by
    intro step
    induction step with
    | zero =>
        intro zeroBeforeDuration
        obtain
            ⟨trajectory, trajectoryInitial, physicalProperties⟩ :=
          uniformLocal initialState initialMem supported transverse reality
        refine ⟨trajectory, trajectoryInitial, ?_⟩
        simpa using physicalProperties
    | succ step inductionHypothesis =>
        intro joinBeforeDuration
        have priorBeforeDuration :
            (step : ℝ) * uniformTime < duration := by
          have stepLe : (step : ℝ) ≤ (step.succ : ℝ) := by
            exact_mod_cast Nat.le_succ step
          have timeNonneg : 0 ≤ uniformTime := uniformTimePos.le
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right stepLe timeNonneg)
            joinBeforeDuration
        obtain
            ⟨trajectory, trajectoryInitial, physicalProperties⟩ :=
          inductionHypothesis priorBeforeDuration
        let joinTime : ℝ :=
          (((step : ℝ) + 1) * uniformTime)
        have joinTimeEq :
            joinTime = (step.succ : ℝ) * uniformTime := by
          dsimp [joinTime]
          push_cast
          ring
        have joinTimeNonneg : 0 ≤ joinTime := by
          dsimp [joinTime]
          positivity
        have joinTimeLtDuration : joinTime < duration := by
          rw [joinTimeEq]
          exact joinBeforeDuration
        have joinMem : joinTime ∈ Icc (0 : ℝ) joinTime :=
          ⟨joinTimeNonneg, le_rfl⟩
        have endpointProperties :=
          physicalProperties joinTime joinMem
        have barrier :=
          finiteStateVorticity_sourceOwnedLocalBarrier_on_Icc
            modes negClosed ν trajectory joinTime
            (by
              rw [trajectoryInitial]
              simpa [duration] using joinTimeLtDuration.le)
            (fun t timeMem => (physicalProperties t timeMem).1)
            (fun t timeMem => (physicalProperties t timeMem).2.2.2)
            (fun t timeMem wave waveMem =>
              (physicalProperties t timeMem).2.2.1 wave)
        have endpointEnstrophyLe :
            finiteStateVorticityCoefficientEnstrophy
                modes (trajectory joinTime) ≤ ceiling := by
          have atJoin := (barrier joinTime joinMem).2
          simpa [ceiling, trajectoryInitial] using atJoin
        have endpointAmbientSqLe :=
          complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
            modes (trajectory joinTime) endpointProperties.2.1
        have endpointMem :
            trajectory joinTime ∈
              Metric.closedBall
                (0 : ComplexVorticityHilbertState) innerRadius := by
          rw [Metric.mem_closedBall, dist_zero_right]
          change ‖trajectory joinTime‖ ≤ Real.sqrt ceiling
          exact Real.le_sqrt_of_sq_le
            (endpointAmbientSqLe.trans endpointEnstrophyLe)
        obtain
            ⟨restart, restartInitial, restartProperties⟩ :=
          uniformLocal (trajectory joinTime) endpointMem
            endpointProperties.2.1
            (fun wave waveMem => endpointProperties.2.2.1 wave)
            endpointProperties.2.2.2
        obtain
            ⟨extended, extendedEqPrior, extendedProperties⟩ :=
          finitePhysicalTrajectory_splice
            modes ν.coeff trajectory restart
            joinTime uniformTime joinTimeNonneg uniformTimePos
            physicalProperties restartInitial restartProperties
        have zeroJoinMem : (0 : ℝ) ∈ Icc (0 : ℝ) joinTime :=
          ⟨le_rfl, joinTimeNonneg⟩
        refine ⟨extended, ?_, ?_⟩
        · calc
            extended 0 = trajectory 0 :=
              extendedEqPrior 0 zeroJoinMem
            _ = initialState := trajectoryInitial
        · intro t timeMem
          apply extendedProperties t
          have nextHorizon :
              (((step.succ : ℝ) + 1) * uniformTime) =
                joinTime + uniformTime := by
            dsimp [joinTime]
            push_cast
            ring
          rwa [nextHorizon] at timeMem
  let stepCount : ℕ := Nat.ceil (duration / uniformTime)
  have quotientPos : 0 < duration / uniformTime :=
    div_pos durationPos uniformTimePos
  have stepCountPos : 0 < stepCount := by
    exact Nat.ceil_pos.mpr quotientPos
  let lastStep : ℕ := stepCount.pred
  have lastStepLt : lastStep < stepCount := by
    exact Nat.pred_lt (ne_of_gt stepCountPos)
  have lastStepBeforeDuration :
      (lastStep : ℝ) * uniformTime < duration := by
    have castLt : (lastStep : ℝ) < duration / uniformTime := by
      exact (Nat.lt_ceil).mp (by simpa [stepCount] using lastStepLt)
    exact (lt_div_iff₀ uniformTimePos).mp castLt
  obtain
      ⟨trajectory, trajectoryInitial, physicalProperties⟩ :=
    generatedPrefixes lastStep lastStepBeforeDuration
  have durationLeStepCount :
      duration ≤ (stepCount : ℝ) * uniformTime := by
    apply (div_le_iff₀ uniformTimePos).mp
    exact Nat.le_ceil (duration / uniformTime)
  have lastHorizonEq :
      ((lastStep : ℝ) + 1) * uniformTime =
        (stepCount : ℝ) * uniformTime := by
    have successorEq : lastStep + 1 = stepCount := by
      simpa [lastStep] using Nat.succ_pred_eq_of_pos stepCountPos
    rw [← Nat.cast_one, ← Nat.cast_add, successorEq]
  refine ⟨trajectory, trajectoryInitial, ?_⟩
  intro t timeMem
  apply physicalProperties t
  refine ⟨timeMem.1, ?_⟩
  rw [lastHorizonEq]
  exact timeMem.2.trans durationLeStepCount

end

end
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalCommonTimeExistence
end NavierStokes
end SaturationMonoid
