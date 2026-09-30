import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FunProp
import H0mework.NavierStokes.PlanarTriad.DoubleTriadRealScalarExtension

/-!
# A local trajectory with simultaneous adjacent-scale transfer

The faithful real double-triad generator is a polynomial vector field on
`Fin 4 → ℝ`.  Picard--Lindelöf therefore generates a local integral curve
from the fixed source, without receiving a path or time radius as input.

At time zero both adjacent fluxes and the actual upper-shell energy rate are
strictly positive, while total energy decays.  Continuity generates one
common nonzero interval on which all four strict signs persist.  The
`P₅`-filtered middle-shell consumer is deliberately not reported as the
full-trajectory middle-shell derivative.  This remains neither a PDE flow
nor an inertial-range theorem.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadLocalTrajectory

noncomputable section

open scoped Topology

open Set
open Filter
open TwoDimensionalVorticityDoubleTriadRealScalarExtension

/-! ## Polynomial regularity and actual local path -/

theorem realDoubleTriadGalerkinGenerator_contDiff
    (ν : ℝ) :
    ContDiff ℝ 1
      (realDoubleTriadNavierStokesGalerkinGenerator ν) := by
  rw [contDiff_pi]
  intro mode
  fin_cases mode <;>
    simp [realDoubleTriadNavierStokesGalerkinGenerator,
      realDoubleTriadNonlinearGenerator,
      realDoubleTriadViscousGenerator] <;>
    fun_prop

theorem realDoubleTriadMiddleFlux_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadMiddleFlux ν) := by
  change Continuous
    (fun state => realDoubleTriadMiddleFlux ν state)
  simp_rw [realDoubleTriadMiddleFlux_eq]
  fun_prop

theorem realDoubleTriadUpperFlux_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadUpperFlux ν) := by
  change Continuous
    (fun state => realDoubleTriadUpperFlux ν state)
  simp_rw [realDoubleTriadUpperFlux_eq]
  fun_prop

theorem realDoubleTriadUpperShellEnergyRate_continuous
    (ν : ℝ) :
    Continuous
      (realDoubleTriadUpperShellEnergyRate ν) := by
  change Continuous
    (fun state =>
      realDoubleTriadUpperShellEnergyRate ν state)
  simp_rw [realDoubleTriadUpperShellEnergyRate_eq,
    realDoubleTriadUpperFlux_eq]
  fun_prop

theorem realDoubleTriadFullEnergyRate_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadFullEnergyRate ν) := by
  change Continuous
    (fun state => realDoubleTriadFullEnergyRate ν state)
  simp_rw [realDoubleTriadFullEnergyRate_eq]
  fun_prop

/-- The actual local trajectory is generated from the source and polynomial
vector field; neither the path nor its radius is a premise. -/
theorem exists_realCanonicalDoubleTriad_localTrajectory :
    ∃ trajectory : ℝ → RealDoubleTriadState,
      trajectory 0 = realCanonicalDoubleTriadSource ∧
        ∃ ε > (0 : ℝ),
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt trajectory
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (trajectory t)) t := by
  obtain ⟨trajectory, initial, ε, εPos, evolves⟩ :=
    (realDoubleTriadGalerkinGenerator_contDiff (1 / 100)).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
        0
  refine ⟨trajectory, initial, ε, εPos, ?_⟩
  simpa using evolves

/-! ## One common positive two-scale interval -/

/-- Both native adjacent fluxes persist positively along the same actual
trajectory.  The actual upper shell gains energy while the complete finite
system dissipates energy. -/
theorem exists_realCanonicalDoubleTriad_positiveTwoScaleTransferInterval :
    ∃ (trajectory : ℝ → RealDoubleTriadState) (ε : ℝ),
      0 < ε ∧
        trajectory 0 = realCanonicalDoubleTriadSource ∧
          ∀ t, |t| < ε →
            HasDerivAt trajectory
                (realDoubleTriadNavierStokesGalerkinGenerator
                  (1 / 100) (trajectory t)) t ∧
              0 <
                realDoubleTriadMiddleFlux
                  (1 / 100) (trajectory t) ∧
              0 <
                realDoubleTriadUpperFlux
                  (1 / 100) (trajectory t) ∧
              0 <
                realDoubleTriadUpperShellEnergyRate
                  (1 / 100) (trajectory t) ∧
              realDoubleTriadFullEnergyRate
                  (1 / 100) (trajectory t) < 0 := by
  obtain ⟨trajectory, initial, odeRadius, odeRadiusPos, evolves⟩ :=
    exists_realCanonicalDoubleTriad_localTrajectory
  have zeroInOdeInterval :
      (0 : ℝ) ∈ Ioo (-odeRadius) odeRadius := by
    constructor <;> linarith
  have trajectoryContinuousAtZero :
      ContinuousAt trajectory 0 :=
    (evolves 0 zeroInOdeInterval).continuousAt
  have middleFluxContinuousAtZero :
      ContinuousAt
        (fun t =>
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t)) 0 :=
    (realDoubleTriadMiddleFlux_continuous (1 / 100)).continuousAt.comp
      trajectoryContinuousAtZero
  have upperFluxContinuousAtZero :
      ContinuousAt
        (fun t =>
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t)) 0 :=
    (realDoubleTriadUpperFlux_continuous (1 / 100)).continuousAt.comp
      trajectoryContinuousAtZero
  have upperRateContinuousAtZero :
      ContinuousAt
        (fun t =>
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t)) 0 :=
    (realDoubleTriadUpperShellEnergyRate_continuous
      (1 / 100)).continuousAt.comp
        trajectoryContinuousAtZero
  have totalRateContinuousAtZero :
      ContinuousAt
        (fun t =>
          realDoubleTriadFullEnergyRate
            (1 / 100) (trajectory t)) 0 :=
    (realDoubleTriadFullEnergyRate_continuous
      (1 / 100)).continuousAt.comp
        trajectoryContinuousAtZero
  have middleFluxAtZero :
      0 <
        realDoubleTriadMiddleFlux
          (1 / 100) (trajectory 0) := by
    rw [initial, realCanonicalDoubleTriad_middleFlux]
    norm_num
  have upperFluxAtZero :
      0 <
        realDoubleTriadUpperFlux
          (1 / 100) (trajectory 0) := by
    rw [initial, realCanonicalDoubleTriad_upperFlux]
    norm_num
  have upperRateAtZero :
      0 <
        realDoubleTriadUpperShellEnergyRate
          (1 / 100) (trajectory 0) := by
    rw [initial,
      realCanonicalDoubleTriad_upperShellEnergyRate]
    norm_num
  have totalRateAtZero :
      realDoubleTriadFullEnergyRate
          (1 / 100) (trajectory 0) < 0 := by
    rw [initial, realCanonicalDoubleTriad_fullEnergyRate]
    norm_num
  have eventuallyMiddleFlux :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        0 <
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t) :=
    continuousAt_const.eventually_lt
      middleFluxContinuousAtZero middleFluxAtZero
  have eventuallyUpperFlux :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        0 <
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t) :=
    continuousAt_const.eventually_lt
      upperFluxContinuousAtZero upperFluxAtZero
  have eventuallyUpperRate :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        0 <
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t) :=
    continuousAt_const.eventually_lt
      upperRateContinuousAtZero upperRateAtZero
  have eventuallyTotalRate :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        realDoubleTriadFullEnergyRate
            (1 / 100) (trajectory t) < 0 :=
    totalRateContinuousAtZero.eventually_lt
      continuousAt_const totalRateAtZero
  obtain ⟨readoutRadius, readoutRadiusPos, readouts⟩ :=
    Metric.eventually_nhds_iff.mp
      (eventuallyMiddleFlux.and
        (eventuallyUpperFlux.and
          (eventuallyUpperRate.and eventuallyTotalRate)))
  let ε := min odeRadius readoutRadius
  have εPos : 0 < ε :=
    lt_min odeRadiusPos readoutRadiusPos
  refine ⟨trajectory, ε, εPos, initial, ?_⟩
  intro t tInInterval
  have tInOdeRadius : |t| < odeRadius :=
    lt_of_lt_of_le tInInterval (min_le_left _ _)
  have tInReadoutRadius : |t| < readoutRadius :=
    lt_of_lt_of_le tInInterval (min_le_right _ _)
  have tInOdeInterval :
      t ∈ Ioo (-odeRadius) odeRadius :=
    abs_lt.mp tInOdeRadius
  have readoutAtT :
      0 <
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t) ∧
        0 <
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t) ∧
        0 <
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t) ∧
        realDoubleTriadFullEnergyRate
            (1 / 100) (trajectory t) < 0 :=
    readouts
      (by simpa [Real.dist_eq] using tInReadoutRadius)
  exact ⟨evolves t tInOdeInterval, readoutAtT⟩

end

end TwoDimensionalVorticityDoubleTriadLocalTrajectory
end SaturationMonoid.NavierStokes
