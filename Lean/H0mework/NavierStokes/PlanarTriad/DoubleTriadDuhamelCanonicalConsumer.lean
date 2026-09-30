import Mathlib.Analysis.ODE.ExistUnique
import H0mework.NavierStokes.PlanarTriad.DoubleTriadLocalTrajectory
import H0mework.NavierStokes.PlanarTriad.DoubleTriadDuhamelReadout

/-!
# Canonical source consumers for the middle-cutoff Duhamel ledger

This module generates the canonical full/filtered trajectories and applies
the readout layer to the resulting source-owned data.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual

noncomputable section

open scoped Interval Topology

open Set
open Filter
open TwoDimensionalVorticityDoubleTriadRealScalarExtension
open TwoDimensionalVorticityDoubleTriadLocalTrajectory

/-! ## Canonical initial data and generated paths -/

/-- The filtered local path is generated from the projected canonical
source; neither the path nor its radius is supplied. -/
theorem exists_realCanonicalDoubleTriad_middleFilteredLocalTrajectory :
    ∃ trajectory : ℝ → RealDoubleTriadState,
      trajectory 0 =
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource ∧
        ∃ ε > (0 : ℝ),
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt trajectory
              (realDoubleTriadMiddleFilteredGenerator
                (1 / 100) (trajectory t)) t := by
  obtain ⟨trajectory, initial, ε, εPos, evolves⟩ :=
    (realDoubleTriadMiddleFilteredGenerator_contDiff
      (1 / 100)).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
        (x₀ :=
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource)
        0
  exact
    ⟨trajectory, initial, ε, εPos,
      by simpa using evolves⟩

theorem realCanonicalDoubleTriad_initialMiddlePropagationResidual :
    realDoubleTriadMiddlePropagationResidual
        (1 / 100)
        realCanonicalDoubleTriadSource
        (realDoubleTriadMiddlePass
          realCanonicalDoubleTriadSource) = 0 := by
  simp [realDoubleTriadMiddlePropagationResidual]

theorem realCanonicalDoubleTriad_initialUpperTrace :
    realDoubleTriadUpperTrace
        (1 / 100) realCanonicalDoubleTriadSource =
      ![(1 / 20 : ℝ), 0, 9 / 20, 0] := by
  rw [realDoubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;> simp <;> norm_num

theorem realCanonicalDoubleTriad_initialUpperTrace_two :
    realDoubleTriadUpperTrace
        (1 / 100) realCanonicalDoubleTriadSource 2 =
      9 / 20 := by
  rw [realDoubleTriadUpperTrace_coordinates]
  simp
  norm_num

theorem realCanonicalDoubleTriad_initialMiddleDefectRateTwo :
    realDoubleTriadMiddleDefectRateTwo
        (1 / 100)
        realCanonicalDoubleTriadSource
        (realDoubleTriadMiddlePass
          realCanonicalDoubleTriadSource) =
      9 / 20 := by
  change
    realDoubleTriadUpperTrace
          (1 / 100) realCanonicalDoubleTriadSource 2 +
        realDoubleTriadMiddlePropagationResidual
          (1 / 100)
          realCanonicalDoubleTriadSource
          (realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource) 2 =
      9 / 20
  rw [realCanonicalDoubleTriad_initialUpperTrace_two]
  have propagationTwo :=
    congrFun
      realCanonicalDoubleTriad_initialMiddlePropagationResidual 2
  simp at propagationTwo
  have propagationTwo' :
      realDoubleTriadMiddlePropagationResidual
          (1 / 100)
          realCanonicalDoubleTriadSource
          (realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource) 2 = 0 := by
    simpa only [one_div] using propagationTwo
  rw [propagationTwo']
  norm_num

/-- Both actual paths are generated on one common nonzero interval. -/
theorem exists_realCanonicalDoubleTriad_fullAndMiddleFilteredLocalTrajectories :
    ∃ (full filtered : ℝ → RealDoubleTriadState) (ε : ℝ),
      0 < ε ∧
        full 0 = realCanonicalDoubleTriadSource ∧
        filtered 0 =
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource ∧
        ∀ t, |t| < ε →
          HasDerivAt full
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (full t)) t ∧
            HasDerivAt filtered
              (realDoubleTriadMiddleFilteredGenerator
                (1 / 100) (filtered t)) t := by
  obtain ⟨full, fullInitial, fullRadius, fullRadiusPos,
      fullEvolves⟩ :=
    exists_realCanonicalDoubleTriad_localTrajectory
  obtain ⟨filtered, filteredInitial, filteredRadius,
      filteredRadiusPos, filteredEvolves⟩ :=
    exists_realCanonicalDoubleTriad_middleFilteredLocalTrajectory
  let ε := min fullRadius filteredRadius
  have εPos : 0 < ε :=
    lt_min fullRadiusPos filteredRadiusPos
  refine
    ⟨full, filtered, ε, εPos, fullInitial,
      filteredInitial, ?_⟩
  intro t membership
  have fullMembership :
      t ∈ Ioo (-fullRadius) fullRadius :=
    abs_lt.mp
      (lt_of_lt_of_le membership (min_le_left _ _))
  have filteredMembership :
      t ∈ Ioo (-filteredRadius) filteredRadius :=
    abs_lt.mp
      (lt_of_lt_of_le membership (min_le_right _ _))
  exact
    ⟨fullEvolves t fullMembership,
      filteredEvolves t filteredMembership⟩

/-! ## Canonical Duhamel and gap consumers -/

/-- The first full/filtered endpoint defect has an exact two-term Duhamel
ledger.  The propagation residual is zero at the generated initial event,
while the source-owned instantaneous upper trace is nonzero. -/
theorem exists_realCanonicalDoubleTriad_middleDuhamelDefect :
    ∃ (full filtered : ℝ → RealDoubleTriadState) (T : ℝ),
      0 < T ∧
        full 0 = realCanonicalDoubleTriadSource ∧
        filtered 0 =
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivAt full
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (full t)) t ∧
            HasDerivAt filtered
              (realDoubleTriadMiddleFilteredGenerator
                (1 / 100) (filtered t)) t) ∧
        realDoubleTriadMiddlePass (full T) - filtered T =
          (∫ t in 0..T,
              realDoubleTriadUpperTrace
                (1 / 100) (full t)) +
            ∫ t in 0..T,
              realDoubleTriadMiddlePropagationResidual
                (1 / 100) (full t) (filtered t) ∧
        realDoubleTriadMiddlePropagationResidual
            (1 / 100) (full 0) (filtered 0) = 0 ∧
        realDoubleTriadUpperTrace
            (1 / 100) (full 0) ≠ 0 := by
  obtain ⟨full, filtered, ε, εPos,
      fullInitial, filteredInitial, evolves⟩ :=
    exists_realCanonicalDoubleTriad_fullAndMiddleFilteredLocalTrajectories
  let T := ε / 2
  have TPos : 0 < T := by
    dsimp [T]
    linarith
  have TLt : T < ε := by
    dsimp [T]
    linarith
  have evolvesIcc :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (full t)) t ∧
          HasDerivAt filtered
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered t)) t := by
    intro t membership
    exact evolves t
      (by
        rw [abs_of_nonneg membership.1]
        exact lt_of_le_of_lt membership.2 TLt)
  have duhamel :
      realDoubleTriadMiddlePass (full T) - filtered T =
        (∫ t in 0..T,
            realDoubleTriadUpperTrace
              (1 / 100) (full t)) +
          ∫ t in 0..T,
            realDoubleTriadMiddlePropagationResidual
              (1 / 100) (full t) (filtered t) := by
    apply realDoubleTriad_middleDuhamel_identity
      full filtered T TPos
    · intro t membership
      exact (evolvesIcc t membership).1
    · intro t membership
      exact (evolvesIcc t membership).2
    · rw [fullInitial, filteredInitial]
  have initialPropagation :
      realDoubleTriadMiddlePropagationResidual
          (1 / 100) (full 0) (filtered 0) = 0 := by
    rw [fullInitial, filteredInitial]
    simp [realDoubleTriadMiddlePropagationResidual,
      realDoubleTriadMiddleFilteredGenerator]
  have initialUpperTrace :
      realDoubleTriadUpperTrace
          (1 / 100) (full 0) ≠ 0 := by
    intro traceZero
    have coordinateZero := congrFun traceZero 0
    rw [fullInitial,
      realDoubleTriadUpperTrace_coordinates] at coordinateZero
    have sourceTwo :
        realCanonicalDoubleTriadSource 2 = -1 := by
      rfl
    have sourceThree :
        realCanonicalDoubleTriadSource 3 = 1 / 2 := by
      rfl
    simp [sourceTwo, sourceThree] at coordinateZero
  exact
    ⟨full, filtered, T, TPos, fullInitial,
      filteredInitial, evolvesIcc, duhamel,
      initialPropagation, initialUpperTrace⟩

/-- The source-generated mode-two quantum `9/20` leaves a concrete
`9/40` margin on a generated common time window. -/
theorem exists_realCanonicalDoubleTriad_middleDefectRateGap :
    ∃ (full filtered : ℝ → RealDoubleTriadState) (T : ℝ),
      0 < T ∧
        full 0 = realCanonicalDoubleTriadSource ∧
        filtered 0 =
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivAt full
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (full t)) t ∧
            HasDerivAt filtered
              (realDoubleTriadMiddleFilteredGenerator
                (1 / 100) (filtered t)) t) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          9 / 40 <
            realDoubleTriadMiddleDefectRateTwo
              (1 / 100) (full t) (filtered t)) := by
  obtain ⟨full, filtered, ε, εPos,
      fullInitial, filteredInitial, evolves⟩ :=
    exists_realCanonicalDoubleTriad_fullAndMiddleFilteredLocalTrajectories
  have zeroInWindow : |(0 : ℝ)| < ε := by
    simpa using εPos
  have fullContinuousAtZero :
      ContinuousAt full 0 :=
    (evolves 0 zeroInWindow).1.continuousAt
  have filteredContinuousAtZero :
      ContinuousAt filtered 0 :=
    (evolves 0 zeroInWindow).2.continuousAt
  have rateContinuousAtZero :
      ContinuousAt
        (fun t =>
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t)) 0 := by
    simpa [Function.comp_def] using
      realDoubleTriadMiddleDefectRateTwo_continuous.continuousAt.comp
        (fullContinuousAtZero.prodMk
          filteredContinuousAtZero)
  have rateAtZero :
      realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full 0) (filtered 0) =
        9 / 20 := by
    rw [fullInitial, filteredInitial]
    exact realCanonicalDoubleTriad_initialMiddleDefectRateTwo
  have gapAtZero :
      (9 / 40 : ℝ) <
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full 0) (filtered 0) := by
    rw [rateAtZero]
    norm_num
  have eventuallyGap :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        9 / 40 <
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t) :=
    continuousAt_const.eventually_lt
      rateContinuousAtZero gapAtZero
  obtain ⟨rateRadius, rateRadiusPos, rateGap⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyGap
  let T := min ε rateRadius / 2
  have commonRadiusPos :
      0 < min ε rateRadius :=
    lt_min εPos rateRadiusPos
  have TPos : 0 < T := by
    dsimp [T]
    linarith
  have TLtCommon : T < min ε rateRadius := by
    dsimp [T]
    linarith
  have TLtEpsilon : T < ε :=
    lt_of_lt_of_le TLtCommon (min_le_left _ _)
  have TLtRateRadius : T < rateRadius :=
    lt_of_lt_of_le TLtCommon (min_le_right _ _)
  have evolvesIcc :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (full t)) t ∧
          HasDerivAt filtered
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered t)) t := by
    intro t membership
    exact evolves t
      (by
        rw [abs_of_nonneg membership.1]
        exact lt_of_le_of_lt membership.2 TLtEpsilon)
  have rateGapIcc :
      ∀ t ∈ Icc (0 : ℝ) T,
        9 / 40 <
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t) := by
    intro t membership
    apply rateGap
    rw [Real.dist_eq, sub_zero, abs_of_nonneg membership.1]
    exact lt_of_le_of_lt membership.2 TLtRateRadius
  exact
    ⟨full, filtered, T, TPos, fullInitial,
      filteredInitial, evolvesIcc, rateGapIcc⟩

/-- No-premise composition of the source-generated `9/40` gap with the
independent FTC consumer. -/
theorem exists_realCanonicalDoubleTriad_middleDuhamelEndpointKernelEscape :
    ∃ (full filtered : ℝ → RealDoubleTriadState) (T : ℝ),
      0 < T ∧
        full 0 = realCanonicalDoubleTriadSource ∧
        filtered 0 =
          realDoubleTriadMiddlePass
            realCanonicalDoubleTriadSource ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivAt full
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (full t)) t ∧
            HasDerivAt filtered
              (realDoubleTriadMiddleFilteredGenerator
                (1 / 100) (filtered t)) t) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          9 / 40 <
            realDoubleTriadMiddleDefectRateTwo
              (1 / 100) (full t) (filtered t)) ∧
        0 <
          (realDoubleTriadMiddlePass (full T) -
            filtered T) 2 := by
  obtain ⟨full, filtered, T, TPos,
      fullInitial, filteredInitial, evolves, rateGap⟩ :=
    exists_realCanonicalDoubleTriad_middleDefectRateGap
  have endpointPositive :=
    realDoubleTriad_middleDefectRateGap_forces_endpointKernelEscape
      full filtered T TPos
        (by rw [fullInitial, filteredInitial])
        evolves rateGap
  exact
    ⟨full, filtered, T, TPos, fullInitial,
      filteredInitial, evolves, rateGap, endpointPositive⟩

end

end TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual
end SaturationMonoid.NavierStokes
