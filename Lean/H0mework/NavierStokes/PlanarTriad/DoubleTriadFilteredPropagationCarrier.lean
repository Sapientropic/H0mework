import Mathlib.Tactic.FunProp
import H0mework.NavierStokes.PlanarTriad.DoubleTriadRealScalarExtension

/-!
# The filtered propagation carrier for the double triad

This module defines the actual `P₅`-filtered vector field, the propagation
residual it leaves against the full field, and the pointwise differential
and continuity laws needed by downstream Duhamel readouts.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual

noncomputable section

open scoped Topology

open Set
open TwoDimensionalVorticityDoubleTriadRealScalarExtension

/-! ## The actual filtered vector field -/

def realDoubleTriadMiddlePassCLM :
    RealDoubleTriadState →L[ℝ] RealDoubleTriadState :=
  LinearMap.toContinuousLinearMap realDoubleTriadMiddlePass

@[simp] theorem realDoubleTriadMiddlePassCLM_apply
    (state : RealDoubleTriadState) :
    realDoubleTriadMiddlePassCLM state =
      realDoubleTriadMiddlePass state :=
  rfl

/-- Ambient presentation of the actual `P₅` Galerkin vector field. -/
def realDoubleTriadMiddleFilteredGenerator
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadMiddlePass
    (realDoubleTriadNavierStokesGalerkinGenerator ν
      (realDoubleTriadMiddlePass state))

theorem realDoubleTriadMiddleFilteredGenerator_contDiff
    (ν : ℝ) :
    ContDiff ℝ 1
      (realDoubleTriadMiddleFilteredGenerator ν) := by
  rw [contDiff_pi]
  intro mode
  fin_cases mode <;>
    simp [realDoubleTriadMiddleFilteredGenerator,
      realDoubleTriadMiddlePass,
      realDoubleTriadNavierStokesGalerkinGenerator,
      realDoubleTriadNonlinearGenerator,
      realDoubleTriadViscousGenerator] <;>
    fun_prop

@[simp] theorem realDoubleTriadMiddlePass_filteredGenerator
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddlePass
        (realDoubleTriadMiddleFilteredGenerator ν state) =
      realDoubleTriadMiddleFilteredGenerator ν state := by
  simp [realDoubleTriadMiddleFilteredGenerator]

@[simp] theorem realDoubleTriadMiddleFilteredGenerator_middlePass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleFilteredGenerator ν
        (realDoubleTriadMiddlePass state) =
      realDoubleTriadMiddleFilteredGenerator ν state := by
  simp [realDoubleTriadMiddleFilteredGenerator]

/-! ## The propagation carrier and pointwise decomposition -/

/-- Nonlinear propagation responsibility left after the instantaneous
upper scale trace is removed. -/
def realDoubleTriadMiddlePropagationResidual
    (ν : ℝ) (full filtered : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadMiddleFilteredGenerator ν full -
    realDoubleTriadMiddleFilteredGenerator ν filtered

/-- Mode two is the clean source-generated leading endpoint quantum. -/
def realDoubleTriadMiddleDefectRateTwo
    (ν : ℝ) (full filtered : RealDoubleTriadState) : ℝ :=
  (realDoubleTriadUpperTrace ν full +
    realDoubleTriadMiddlePropagationResidual
      ν full filtered) 2

theorem realDoubleTriadMiddleDefectRateTwo_continuous :
    Continuous
      (fun states :
          RealDoubleTriadState × RealDoubleTriadState =>
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) states.1 states.2) := by
  change Continuous
    (fun states :
        RealDoubleTriadState × RealDoubleTriadState =>
      (realDoubleTriadUpperTrace
          (1 / 100) states.1 +
        (realDoubleTriadMiddleFilteredGenerator
            (1 / 100) states.1 -
          realDoubleTriadMiddleFilteredGenerator
            (1 / 100) states.2)) 2)
  simp_rw [realDoubleTriadUpperTrace_coordinates]
  simp [realDoubleTriadMiddleFilteredGenerator,
    realDoubleTriadMiddlePass,
    realDoubleTriadNavierStokesGalerkinGenerator,
    realDoubleTriadNonlinearGenerator,
    realDoubleTriadViscousGenerator]
  fun_prop

theorem realDoubleTriadMiddleGeneratorDefect_split
    (ν : ℝ) (full filtered : RealDoubleTriadState) :
    realDoubleTriadMiddlePass
          (realDoubleTriadNavierStokesGalerkinGenerator ν full) -
        realDoubleTriadMiddleFilteredGenerator ν filtered =
      realDoubleTriadUpperTrace ν full +
        realDoubleTriadMiddlePropagationResidual
          ν full filtered := by
  simp [realDoubleTriadMiddleFilteredGenerator,
    realDoubleTriadUpperTrace,
    realDoubleTriadMiddlePropagationResidual]

theorem realDoubleTriad_projectedTrajectory_hasDerivAt
    (trajectory : ℝ → RealDoubleTriadState)
    (t : ℝ) (tangent : RealDoubleTriadState)
    (evolves : HasDerivAt trajectory tangent t) :
    HasDerivAt
      (fun time =>
        realDoubleTriadMiddlePass (trajectory time))
      (realDoubleTriadMiddlePass tangent) t := by
  simpa [realDoubleTriadMiddlePassCLM] using
    ((hasDerivAt_const t
      realDoubleTriadMiddlePassCLM).clm_apply evolves)

theorem realDoubleTriad_middleDefect_hasDerivAt
    (full filtered : ℝ → RealDoubleTriadState) (t : ℝ)
    (fullEvolves :
      HasDerivAt full
        (realDoubleTriadNavierStokesGalerkinGenerator
          (1 / 100) (full t)) t)
    (filteredEvolves :
      HasDerivAt filtered
        (realDoubleTriadMiddleFilteredGenerator
          (1 / 100) (filtered t)) t) :
    HasDerivAt
      (fun time =>
        realDoubleTriadMiddlePass (full time) -
          filtered time)
      (realDoubleTriadUpperTrace
          (1 / 100) (full t) +
        realDoubleTriadMiddlePropagationResidual
          (1 / 100) (full t) (filtered t)) t := by
  have projectedFullDerivative :=
    realDoubleTriad_projectedTrajectory_hasDerivAt
      full t
        (realDoubleTriadNavierStokesGalerkinGenerator
          (1 / 100) (full t))
        fullEvolves
  change HasDerivAt
    ((fun time =>
      realDoubleTriadMiddlePass (full time)) - filtered)
    (realDoubleTriadUpperTrace
        (1 / 100) (full t) +
      realDoubleTriadMiddlePropagationResidual
        (1 / 100) (full t) (filtered t)) t
  simpa only [realDoubleTriadMiddleGeneratorDefect_split] using
    projectedFullDerivative.sub filteredEvolves

theorem realDoubleTriadUpperTrace_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadUpperTrace ν) := by
  have explicitTraceContinuous :
      Continuous
        (fun state : RealDoubleTriadState =>
          ![(-1 / 10 : ℝ) * state 2 * state 3, 0,
            (9 / 10 : ℝ) * state 0 * state 3, 0]) := by
    fun_prop
  exact explicitTraceContinuous.congr
    (fun state =>
      (realDoubleTriadUpperTrace_coordinates ν state).symm)

theorem realDoubleTriadMiddlePropagationResidual_continuousOn
    (ν : ℝ) {a b : ℝ}
    {full filtered : ℝ → RealDoubleTriadState}
    (fullContinuous : ContinuousOn full (Icc a b))
    (filteredContinuous : ContinuousOn filtered (Icc a b)) :
    ContinuousOn
      (fun t =>
        realDoubleTriadMiddlePropagationResidual
          ν (full t) (filtered t))
      (Icc a b) := by
  have middlePassFullContinuous :
      ContinuousOn
        (fun t => realDoubleTriadMiddlePass (full t))
        (Icc a b) := by
    exact
      (realDoubleTriadMiddlePassCLM.continuous.comp_continuousOn
        fullContinuous).congr
          (fun _ _ => rfl)
  have firstContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadMiddleFilteredGenerator ν
            (realDoubleTriadMiddlePass (full t)))
        (Icc a b) :=
    (realDoubleTriadMiddleFilteredGenerator_contDiff
      ν).continuous.comp_continuousOn
        middlePassFullContinuous
  have secondContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadMiddleFilteredGenerator ν
            (filtered t))
        (Icc a b) :=
    (realDoubleTriadMiddleFilteredGenerator_contDiff
      ν).continuous.comp_continuousOn
        filteredContinuous
  exact firstContinuous.sub secondContinuous

end

end TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual
end SaturationMonoid.NavierStokes
