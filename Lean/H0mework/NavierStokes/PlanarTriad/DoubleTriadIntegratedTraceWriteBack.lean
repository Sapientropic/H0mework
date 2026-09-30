import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.NavierStokes.PlanarTriad.DoubleTriadLocalTrajectory

/-!
# Time-integrated write-back for the connected double triad

At each physical time, the actual state carries a separate two-edge scale
path `full → P₅ → P₂`.  This file integrates that pointwise scale ledger
along the generated local Galerkin trajectory.  It does not assert that a
spectral projection commutes with nonlinear time evolution.

The two-scale trace is the forced complement of the final low keep:

```text
current residual = low live residual + two-scale trace.
```

Integration writes the live part and trace into separate memory fields and
recollection recovers the integral of the original residual.  The same
source-generated positive interval also gives strictly positive integrals
of both adjacent fluxes.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadIntegratedTraceWriteBack

noncomputable section

open scoped Interval

open Set
open intervalIntegral
open TwoDimensionalVorticityDoubleTriadRealScalarExtension
open TwoDimensionalVorticityDoubleTriadLocalTrajectory

/-! ## Pointwise actual update and forced trace -/

/-- The total two-edge scale trace is not stored independently: it is the
unique additive complement of the actual final low keep. -/
def realDoubleTriadTwoScaleTrace
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadNestedLedger :=
  realDoubleTriadNestedResidual ν state -
    realDoubleTriadLowKeep
      (realDoubleTriadNestedResidual ν state)

theorem realDoubleTriadTwoScaleTrace_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadTwoScaleTrace ν state =
      (0, realDoubleTriadMiddleTrace ν state,
        realDoubleTriadUpperTrace ν state) := by
  ext <;>
    simp [realDoubleTriadTwoScaleTrace,
      realDoubleTriadNestedResidual,
      realDoubleTriadLowKeep]

/-- The actual `P₂` state update is exactly the live part of the same
residual carrier. -/
theorem realDoubleTriadNestedResidual_actualLowUpdate
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadNestedResidual ν
        (realDoubleTriadLowPass state) =
      realDoubleTriadLowKeep
        (realDoubleTriadNestedResidual ν state) :=
  realDoubleTriadNestedResidual_lowPass ν state

/-- Residual conservation before integration. -/
theorem realDoubleTriadNestedResidual_eq_live_add_trace
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadNestedResidual ν state =
      realDoubleTriadNestedResidual ν
          (realDoubleTriadLowPass state) +
        realDoubleTriadTwoScaleTrace ν state := by
  rw [realDoubleTriadNestedResidual_actualLowUpdate]
  simp [realDoubleTriadTwoScaleTrace]

/-- Additive complements are forced by the same keep. -/
theorem realDoubleTriadTwoScaleTrace_unique
    (ν : ℝ) (state : RealDoubleTriadState)
    (candidate : RealDoubleTriadNestedLedger)
    (split :
      realDoubleTriadNestedResidual ν state =
        realDoubleTriadNestedResidual ν
            (realDoubleTriadLowPass state) +
          candidate) :
    candidate = realDoubleTriadTwoScaleTrace ν state := by
  apply add_left_cancel
    (a :=
      realDoubleTriadNestedResidual ν
        (realDoubleTriadLowPass state))
  calc
    realDoubleTriadNestedResidual ν
          (realDoubleTriadLowPass state) + candidate =
        realDoubleTriadNestedResidual ν state :=
      split.symm
    _ =
        realDoubleTriadNestedResidual ν
            (realDoubleTriadLowPass state) +
          realDoubleTriadTwoScaleTrace ν state :=
      realDoubleTriadNestedResidual_eq_live_add_trace ν state

/-! ## Integrated live/memory carrier -/

abbrev RealDoubleTriadIntegratedWriteBack :=
  RealDoubleTriadNestedLedger × RealDoubleTriadNestedLedger

def realDoubleTriadIntegratedWriteBack
    (ν a b : ℝ) (trajectory : ℝ → RealDoubleTriadState) :
    RealDoubleTriadIntegratedWriteBack :=
  (∫ t in a..b,
      realDoubleTriadNestedResidual ν
        (realDoubleTriadLowPass (trajectory t)),
    ∫ t in a..b,
      realDoubleTriadTwoScaleTrace ν (trajectory t))

def realDoubleTriadIntegratedRecollect :
    RealDoubleTriadIntegratedWriteBack →ₗ[ℝ]
      RealDoubleTriadNestedLedger where
  toFun ledger := ledger.1 + ledger.2
  map_add' := by
    intro left right
    simp
    abel
  map_smul' := by
    intro scalar ledger
    simp [smul_add]

/-! ## Continuity needed by the generated trajectory -/

theorem realDoubleTriadNestedResidual_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadNestedResidual ν) := by
  change Continuous
    (fun state =>
      (realDoubleTriadBaseClosure ν state,
        realDoubleTriadMiddleTrace ν state,
        realDoubleTriadUpperTrace ν state))
  simp_rw [realDoubleTriadBaseClosure_coordinates,
    realDoubleTriadMiddleTrace_coordinates,
    realDoubleTriadUpperTrace_coordinates]
  fun_prop

theorem realDoubleTriadLowLiveResidual_continuous
    (ν : ℝ) :
    Continuous
      (fun state =>
        realDoubleTriadNestedResidual ν
          (realDoubleTriadLowPass state)) := by
  have lowPassContinuous :
      Continuous realDoubleTriadLowPass := by
    change Continuous
      (fun state : RealDoubleTriadState =>
        ![state 0, state 1, 0, 0])
    fun_prop
  exact
    (realDoubleTriadNestedResidual_continuous ν).comp
      lowPassContinuous

theorem realDoubleTriadTwoScaleTrace_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadTwoScaleTrace ν) := by
  have explicitTraceContinuous :
      Continuous
        (fun state : RealDoubleTriadState =>
          ((0 : RealDoubleTriadState),
            realDoubleTriadMiddleTrace ν state,
            realDoubleTriadUpperTrace ν state)) := by
    simp_rw [realDoubleTriadMiddleTrace_coordinates,
      realDoubleTriadUpperTrace_coordinates]
    fun_prop
  exact explicitTraceContinuous.congr
    (fun state =>
      (realDoubleTriadTwoScaleTrace_eq ν state).symm)

/-! ## Actual upper-shell endpoint consumer -/

/-- Kinetic energy in the physical top shell `|k|² = 10`. -/
def realDoubleTriadUpperShellKineticEnergy
    (state : RealDoubleTriadState) : ℝ :=
  state 3 ^ 2 / 10

def realDoubleTriadUpperShellDissipation
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  2 * ν * state 3 ^ 2

theorem realDoubleTriadUpperShellEnergyRate_eq_flux_sub_dissipation
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperShellEnergyRate ν state =
      realDoubleTriadUpperFlux ν state -
        realDoubleTriadUpperShellDissipation ν state := by
  rw [realDoubleTriadUpperShellEnergyRate_eq]
  rfl

theorem realDoubleTriadUpperShellDissipation_continuous
    (ν : ℝ) :
    Continuous (realDoubleTriadUpperShellDissipation ν) := by
  change Continuous
    (fun state : RealDoubleTriadState =>
      2 * ν * state 3 ^ 2)
  fun_prop

/-- Along an actual state derivative, the derivative of top-shell kinetic
energy is the previously generated actual shell rate. -/
theorem realDoubleTriadUpperShellKineticEnergy_hasDerivAt
    (trajectory : ℝ → RealDoubleTriadState)
    (t : ℝ) (tangent : RealDoubleTriadState)
    (evolves : HasDerivAt trajectory tangent t) :
    HasDerivAt
      (fun time =>
        realDoubleTriadUpperShellKineticEnergy
          (trajectory time))
      ((1 / 5 : ℝ) * trajectory t 3 * tangent 3) t := by
  have coordinateDerivative :
      HasDerivAt (fun time => trajectory time 3)
        (tangent 3) t := by
    simpa using
      ((hasDerivAt_const t
        (ContinuousLinearMap.proj
          (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3)).clm_apply
            evolves)
  rw [show
      (1 / 5 : ℝ) * trajectory t 3 * tangent 3 =
        (2 * trajectory t 3 * tangent 3) / 10 by
      ring]
  simpa [realDoubleTriadUpperShellKineticEnergy] using
    (coordinateDerivative.pow 2).div_const 10

/-! ## Time-integrated residual conservation -/

theorem realDoubleTriad_intervalIntegral_writeBack
    (ν a b : ℝ) (trajectory : ℝ → RealDoubleTriadState)
    (trajectoryContinuous :
      ContinuousOn trajectory (uIcc a b)) :
    (∫ t in a..b,
        realDoubleTriadNestedResidual ν (trajectory t)) =
      realDoubleTriadIntegratedRecollect
        (realDoubleTriadIntegratedWriteBack
          ν a b trajectory) := by
  have liveContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadNestedResidual ν
            (realDoubleTriadLowPass (trajectory t)))
        (uIcc a b) :=
    (realDoubleTriadLowLiveResidual_continuous ν).continuousOn.comp
      trajectoryContinuous
      (fun _ _ => Set.mem_univ _)
  have traceContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadTwoScaleTrace ν (trajectory t))
        (uIcc a b) :=
    (realDoubleTriadTwoScaleTrace_continuous ν).continuousOn.comp
      trajectoryContinuous
      (fun _ _ => Set.mem_univ _)
  have liveIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadNestedResidual ν
            (realDoubleTriadLowPass (trajectory t)))
        MeasureTheory.volume a b :=
    liveContinuous.intervalIntegrable
  have traceIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadTwoScaleTrace ν (trajectory t))
        MeasureTheory.volume a b :=
    traceContinuous.intervalIntegrable
  rw [show
      (∫ t in a..b,
          realDoubleTriadNestedResidual ν (trajectory t)) =
        ∫ t in a..b,
          (realDoubleTriadNestedResidual ν
              (realDoubleTriadLowPass (trajectory t)) +
            realDoubleTriadTwoScaleTrace ν
              (trajectory t)) by
        apply intervalIntegral.integral_congr
        intro t _
        exact realDoubleTriadNestedResidual_eq_live_add_trace
          ν (trajectory t)]
  rw [intervalIntegral.integral_add liveIntegrable traceIntegrable]
  rfl

/-! ## Source-generated positive integrated adjacent fluxes -/

/-- The actual local producer supplies the path, time horizon, ODE law,
integrated write-back, and two strictly positive adjacent flux integrals.
No path, radius, positivity, or integrability witness is a premise. -/
theorem exists_realCanonicalDoubleTriad_positiveIntegratedTwoScaleTransfer :
    ∃ (trajectory : ℝ → RealDoubleTriadState) (T : ℝ),
      0 < T ∧
        trajectory 0 = realCanonicalDoubleTriadSource ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            HasDerivAt trajectory
              (realDoubleTriadNavierStokesGalerkinGenerator
                (1 / 100) (trajectory t)) t) ∧
          (∫ t in 0..T,
              realDoubleTriadNestedResidual
                (1 / 100) (trajectory t)) =
            realDoubleTriadIntegratedRecollect
              (realDoubleTriadIntegratedWriteBack
                (1 / 100) 0 T trajectory) ∧
          0 <
            ∫ t in 0..T,
              realDoubleTriadMiddleFlux
                (1 / 100) (trajectory t) ∧
          0 <
            ∫ t in 0..T,
              realDoubleTriadUpperFlux
                (1 / 100) (trajectory t) ∧
          (∫ t in 0..T,
              realDoubleTriadUpperShellEnergyRate
                (1 / 100) (trajectory t)) =
            (∫ t in 0..T,
                realDoubleTriadUpperFlux
                  (1 / 100) (trajectory t)) -
              ∫ t in 0..T,
                realDoubleTriadUpperShellDissipation
                  (1 / 100) (trajectory t) ∧
          realDoubleTriadUpperShellKineticEnergy
              realCanonicalDoubleTriadSource <
            realDoubleTriadUpperShellKineticEnergy
              (trajectory T) := by
  obtain ⟨trajectory, ε, εPos, initial, persists⟩ :=
    exists_realCanonicalDoubleTriad_positiveTwoScaleTransferInterval
  let T := ε / 2
  have TPos : 0 < T := by
    dsimp [T]
    linarith
  have TLt : T < ε := by
    dsimp [T]
    linarith
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt trajectory
          (realDoubleTriadNavierStokesGalerkinGenerator
            (1 / 100) (trajectory t)) t := by
    intro t membership
    exact (persists t
      (by
        rw [abs_of_nonneg membership.1]
        exact lt_of_le_of_lt membership.2 TLt)).1
  have trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) T) := by
    intro t membership
    exact (evolves t membership).continuousAt.continuousWithinAt
  have middleContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t))
        (Icc (0 : ℝ) T) :=
    (realDoubleTriadMiddleFlux_continuous
      (1 / 100)).continuousOn.comp
        trajectoryContinuous
        (fun _ _ => Set.mem_univ _)
  have upperContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t))
        (Icc (0 : ℝ) T) :=
    (realDoubleTriadUpperFlux_continuous
      (1 / 100)).continuousOn.comp
        trajectoryContinuous
        (fun _ _ => Set.mem_univ _)
  have upperRateContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t))
        (Icc (0 : ℝ) T) :=
    (realDoubleTriadUpperShellEnergyRate_continuous
      (1 / 100)).continuousOn.comp
        trajectoryContinuous
        (fun _ _ => Set.mem_univ _)
  have upperDissipationContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadUpperShellDissipation
            (1 / 100) (trajectory t))
        (Icc (0 : ℝ) T) :=
    (realDoubleTriadUpperShellDissipation_continuous
      (1 / 100)).continuousOn.comp
        trajectoryContinuous
        (fun _ _ => Set.mem_univ _)
  have middleIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t))
        MeasureTheory.volume 0 T :=
    middleContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have upperIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t))
        MeasureTheory.volume 0 T :=
    upperContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have upperRateIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t))
        MeasureTheory.volume 0 T :=
    upperRateContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have upperDissipationIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadUpperShellDissipation
            (1 / 100) (trajectory t))
        MeasureTheory.volume 0 T :=
    upperDissipationContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have middlePositive :
      0 <
        ∫ t in 0..T,
          realDoubleTriadMiddleFlux
            (1 / 100) (trajectory t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      middleIntegrable
    · intro t membership
      exact (persists t
        (by
          rw [abs_of_pos membership.1]
          exact lt_trans membership.2 TLt)).2.1
    · exact TPos
  have upperPositive :
      0 <
        ∫ t in 0..T,
          realDoubleTriadUpperFlux
            (1 / 100) (trajectory t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      upperIntegrable
    · intro t membership
      exact (persists t
        (by
          rw [abs_of_pos membership.1]
          exact lt_trans membership.2 TLt)).2.2.1
    · exact TPos
  have upperRatePositive :
      0 <
        ∫ t in 0..T,
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      upperRateIntegrable
    · intro t membership
      exact (persists t
        (by
          rw [abs_of_pos membership.1]
          exact lt_trans membership.2 TLt)).2.2.2.1
    · exact TPos
  have upperIntegratedBudget :
      (∫ t in 0..T,
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t)) =
        (∫ t in 0..T,
            realDoubleTriadUpperFlux
              (1 / 100) (trajectory t)) -
          ∫ t in 0..T,
            realDoubleTriadUpperShellDissipation
              (1 / 100) (trajectory t) := by
    rw [show
      (∫ t in 0..T,
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t)) =
        ∫ t in 0..T,
          (realDoubleTriadUpperFlux
              (1 / 100) (trajectory t) -
            realDoubleTriadUpperShellDissipation
              (1 / 100) (trajectory t)) by
        apply intervalIntegral.integral_congr
        intro t _
        exact
          realDoubleTriadUpperShellEnergyRate_eq_flux_sub_dissipation
            (1 / 100) (trajectory t)]
    exact intervalIntegral.integral_sub
      upperIntegrable upperDissipationIntegrable
  have upperEnergyFTC :
      (∫ t in 0..T,
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory t)) =
        realDoubleTriadUpperShellKineticEnergy
            (trajectory T) -
          realDoubleTriadUpperShellKineticEnergy
            (trajectory 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f :=
        fun time =>
          realDoubleTriadUpperShellKineticEnergy
            (trajectory time))
      (f' :=
        fun time =>
          realDoubleTriadUpperShellEnergyRate
            (1 / 100) (trajectory time))
      ?_ upperRateIntegrable
    · intro t membership
      have membershipIcc :
          t ∈ Icc (0 : ℝ) T := by
        simpa [uIcc_of_le (le_of_lt TPos)] using membership
      simpa [realDoubleTriadUpperShellEnergyRate] using
        realDoubleTriadUpperShellKineticEnergy_hasDerivAt
          trajectory t
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (trajectory t))
            (evolves t membershipIcc)
  have upperEnergyGain :
      realDoubleTriadUpperShellKineticEnergy
          realCanonicalDoubleTriadSource <
        realDoubleTriadUpperShellKineticEnergy
          (trajectory T) := by
    rw [← initial]
    linarith
  have writeBack :=
    realDoubleTriad_intervalIntegral_writeBack
      (1 / 100) 0 T trajectory
        (by simpa [uIcc_of_le (le_of_lt TPos)] using
          trajectoryContinuous)
  exact
    ⟨trajectory, T, TPos, initial, evolves,
      writeBack, middlePositive, upperPositive,
      upperIntegratedBudget, upperEnergyGain⟩

end

end TwoDimensionalVorticityDoubleTriadIntegratedTraceWriteBack
end SaturationMonoid.NavierStokes
