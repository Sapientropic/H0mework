import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart

/-!
# Actual endpoint restart and trajectory splice

Every finite physical endpoint can already be canonically reconstructed as
a raw source and can generate a new positive-time local Galerkin segment.
This module performs the missing join.

The old segment and the shifted restart segment have the same state and the
same generator derivative at the join.  Their piecewise splice is therefore
genuinely differentiable at the endpoint, not merely continuous there.

This is a qualitative one-step endpoint extension.  The generated restart
time may depend on the endpoint; no uniform lifespan or global continuation
is asserted.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice

open scoped BigOperators Topology ENNReal

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart

noncomputable section

/-- Retain the old trajectory through `joinTime`, then use the restart
trajectory with its time origin shifted to the join. -/
def endpointSplice
    {E : Type*}
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (time : ℝ) : E :=
  if time ≤ joinTime then prior time
  else restart (time - joinTime)

@[simp] theorem endpointSplice_of_le
    {E : Type*}
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (time : ℝ)
    (timeLe : time ≤ joinTime) :
    endpointSplice joinTime prior restart time =
      prior time := by
  simp [endpointSplice, timeLe]

@[simp] theorem endpointSplice_of_lt
    {E : Type*}
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (time : ℝ)
    (joinLt : joinTime < time) :
    endpointSplice joinTime prior restart time =
      restart (time - joinTime) := by
  simp [endpointSplice, not_le.mpr joinLt]

/-- Shifting a vector-valued real trajectory preserves its derivative. -/
private theorem hasDerivAt_comp_sub_const
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (trajectory : ℝ → E)
    (joinTime time : ℝ)
    (tangent : E)
    (derivative :
      HasDerivAt trajectory tangent (time - joinTime)) :
    HasDerivAt
      (fun shiftedTime => trajectory (shiftedTime - joinTime))
      tangent time := by
  have shiftDerivative :
      HasDerivAt
        (fun shiftedTime : ℝ => shiftedTime - joinTime)
        1 time := by
    simpa only [id_eq] using
      (hasDerivAt_id time).sub_const joinTime
  have composed :=
    derivative.hasFDerivAt.comp_hasDerivAt time shiftDerivative
  simpa only [Function.comp_def,
    ContinuousLinearMap.toSpanSingleton_apply_one] using composed

/-- If the two values and their vector derivatives agree at the join, the
endpoint splice has that derivative in the full two-sided sense. -/
private theorem endpointSplice_hasDerivAt_join
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (tangent : E)
    (sameValue : restart 0 = prior joinTime)
    (priorDerivative :
      HasDerivAt prior tangent joinTime)
    (restartDerivative :
      HasDerivAt restart tangent 0) :
    HasDerivAt
      (endpointSplice joinTime prior restart)
      tangent joinTime := by
  have priorWithin :
      HasDerivWithinAt
        (endpointSplice joinTime prior restart)
        tangent (Iic joinTime) joinTime := by
    apply priorDerivative.hasDerivWithinAt.congr
    · intro time timeMem
      exact endpointSplice_of_le
        joinTime prior restart time timeMem
    · exact endpointSplice_of_le
        joinTime prior restart joinTime le_rfl
  have shiftedRestartDerivative :
      HasDerivAt
        (fun time => restart (time - joinTime))
        tangent joinTime := by
    have atJoin :
        joinTime - joinTime = 0 := sub_self joinTime
    rw [← atJoin] at restartDerivative
    exact hasDerivAt_comp_sub_const
      restart joinTime joinTime tangent restartDerivative
  have restartWithin :
      HasDerivWithinAt
        (endpointSplice joinTime prior restart)
        tangent (Ici joinTime) joinTime := by
    apply shiftedRestartDerivative.hasDerivWithinAt.congr
    · intro time timeMem
      by_cases timeEq : time = joinTime
      · subst time
        simp [endpointSplice, sameValue]
      · have joinLt : joinTime < time :=
          lt_of_le_of_ne timeMem (Ne.symm timeEq)
        exact endpointSplice_of_lt
          joinTime prior restart time joinLt
    · simp [endpointSplice, sameValue]
  have joined := priorWithin.union restartWithin
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at joined
  exact joined

/-- Every actual finite physical Galerkin segment admits one canonical
positive-time endpoint restart and a genuine differentiable splice.

The extension trajectory and its additional lifespan are generated in the
conclusion.  The theorem mouth contains no next trajectory, restart source,
uniform lifespan, cutoff, target state, or continuation certificate. -/
theorem finitePhysicalTrajectory_exists_endpointSplice
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (endpointTime : ℝ)
    (endpointTimeNonneg : 0 ≤ endpointTime)
    (physicalProperties :
      ∀ t ∈ Icc (0 : ℝ) endpointTime,
        HasDerivAt trajectory
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) t ∧
          (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
          (∀ wave,
            complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
          FiniteStateFourierReality (trajectory t)) :
    ∃ (extended : ℝ → ComplexVorticityHilbertState)
        (additionalTime : ℝ),
      0 < additionalTime ∧
        (∀ t ∈ Icc (0 : ℝ) endpointTime,
          extended t = trajectory t) ∧
        ∀ t ∈ Icc (0 : ℝ) (endpointTime + additionalTime),
          HasDerivAt extended
              (finiteStateVorticityGenerator
                modes ν (extended t)) t ∧
            (∀ wave, wave ∉ modes → extended t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ extended t wave = 0) ∧
            FiniteStateFourierReality (extended t) := by
  have endpointMem :
      endpointTime ∈ Icc (0 : ℝ) endpointTime :=
    ⟨endpointTimeNonneg, le_rfl⟩
  have endpointProperties :=
    physicalProperties endpointTime endpointMem
  obtain
      ⟨restart, additionalTime, additionalTimePos,
        restartInitial, restartProperties⟩ :=
    finitePhysicalState_transverseRealityLocalTrajectory
      modes zeroNotMem negClosed ν (trajectory endpointTime)
      endpointProperties.2.1
      (fun wave waveMem =>
        endpointProperties.2.2.1 wave)
      endpointProperties.2.2.2
  let extended : ℝ → ComplexVorticityHilbertState :=
    endpointSplice endpointTime trajectory restart
  have restartZeroMem :
      (0 : ℝ) ∈ Icc (0 : ℝ) additionalTime :=
    ⟨le_rfl, additionalTimePos.le⟩
  have priorDerivativeAtJoin :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν (trajectory endpointTime))
        endpointTime :=
    endpointProperties.1
  have restartDerivativeAtJoin :
      HasDerivAt restart
        (finiteStateVorticityGenerator
          modes ν (trajectory endpointTime))
        0 := by
    simpa only [restartInitial] using
      (restartProperties 0 restartZeroMem).1
  have extendedDerivativeAtJoin :
      HasDerivAt extended
        (finiteStateVorticityGenerator
          modes ν (extended endpointTime))
        endpointTime := by
    have joined :=
      endpointSplice_hasDerivAt_join
        endpointTime trajectory restart
        (finiteStateVorticityGenerator
          modes ν (trajectory endpointTime))
        restartInitial priorDerivativeAtJoin
        restartDerivativeAtJoin
    simpa [extended, endpointSplice] using joined
  have extendedDerivative :
      ∀ t ∈ Icc (0 : ℝ) (endpointTime + additionalTime),
        HasDerivAt extended
          (finiteStateVorticityGenerator
            modes ν (extended t)) t := by
    intro t tMem
    rcases lt_trichotomy t endpointTime with tLt | tEq | endpointLt
    · have priorMem :
          t ∈ Icc (0 : ℝ) endpointTime :=
        ⟨tMem.1, tLt.le⟩
      have priorDerivative :=
        (physicalProperties t priorMem).1
      have eventuallyPrior :
          extended =ᶠ[𝓝 t] trajectory := by
        filter_upwards [Iio_mem_nhds tLt] with time timeLt
        exact endpointSplice_of_le
          endpointTime trajectory restart time timeLt.le
      have derivative :=
        priorDerivative.congr_of_eventuallyEq eventuallyPrior
      simpa [extended, endpointSplice, tLt.le] using derivative
    · subst t
      exact extendedDerivativeAtJoin
    · have shiftedMem :
          t - endpointTime ∈ Icc (0 : ℝ) additionalTime := by
        constructor
        · linarith
        · linarith [tMem.2]
      have restartDerivative :=
        (restartProperties
          (t - endpointTime) shiftedMem).1
      have shiftedDerivative :=
        hasDerivAt_comp_sub_const
          restart endpointTime t
          (finiteStateVorticityGenerator
            modes ν (restart (t - endpointTime)))
          restartDerivative
      have eventuallyRestart :
          extended =ᶠ[𝓝 t]
            (fun time => restart (time - endpointTime)) := by
        filter_upwards [Ioi_mem_nhds endpointLt] with time timeLt
        exact endpointSplice_of_lt
          endpointTime trajectory restart time timeLt
      have derivative :=
        shiftedDerivative.congr_of_eventuallyEq
          eventuallyRestart
      simpa [extended, endpointSplice,
        not_le.mpr endpointLt] using derivative
  refine
    ⟨extended, additionalTime, additionalTimePos, ?_, ?_⟩
  · intro t tMem
    exact endpointSplice_of_le
      endpointTime trajectory restart t tMem.2
  · intro t tMem
    refine ⟨extendedDerivative t tMem, ?_⟩
    by_cases tLe : t ≤ endpointTime
    · have priorMem :
          t ∈ Icc (0 : ℝ) endpointTime :=
        ⟨tMem.1, tLe⟩
      have prior := physicalProperties t priorMem
      have stateEq : extended t = trajectory t :=
        endpointSplice_of_le
          endpointTime trajectory restart t tLe
      refine ⟨?_, ?_, ?_⟩
      · intro wave waveNotMem
        rw [stateEq]
        exact prior.2.1 wave waveNotMem
      · intro wave
        rw [stateEq]
        exact prior.2.2.1 wave
      · rw [stateEq]
        exact prior.2.2.2
    · have endpointLt : endpointTime < t :=
        lt_of_not_ge tLe
      have shiftedMem :
          t - endpointTime ∈ Icc (0 : ℝ) additionalTime := by
        constructor
        · linarith
        · linarith [tMem.2]
      have restarted :=
        restartProperties
          (t - endpointTime) shiftedMem
      have stateEq :
          extended t = restart (t - endpointTime) :=
        endpointSplice_of_lt
          endpointTime trajectory restart t endpointLt
      refine ⟨?_, ?_, ?_⟩
      · intro wave waveNotMem
        rw [stateEq]
        exact restarted.2.1 wave waveNotMem
      · intro wave
        rw [stateEq]
        exact restarted.2.2.1 wave
      · rw [stateEq]
        exact restarted.2.2.2

end

end ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
end NavierStokes
end SaturationMonoid
