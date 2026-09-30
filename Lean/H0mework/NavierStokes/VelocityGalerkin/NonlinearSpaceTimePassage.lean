import H0mework.NavierStokes.VelocityGalerkin.StrongSpaceTimeSubsequence
import H0mework.NavierStokes.Fourier.WholeVelocityNonlinearTimePassage

/-!
# Nonlinear space-time passage for the generated velocity Galerkin family

The whole-restart source already generates a compact family of actual
unforced velocity Galerkin paths in `L²_t(ℓ²)`.  At every fixed output
frequency, the whole velocity convection constructed before the Fourier
quotient is locally Lipschitz from that carrier to `L¹_t`.

This module installs the actual nonlinear rows in their `L¹` carrier,
proves the exact whole-space-time difference estimate, transports every
whole-state Cauchy sequence to a nonlinear-row Cauchy sequence, and finally
generates the nonlinear limit on the same source-selected strong
subsequence.  No target limit, subsequence, critical margin, cutoff, or
compactness witness occurs in the source-facing mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeVelocityNonlinearTimePassage

noncomputable section

/-! ## Actual whole velocity nonlinear rows -/

theorem generatedVelocityEndpointGalerkinWholeStateAtTime_transverse
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : ℝ) :
    WholeStateTransverse
      (generatedVelocityEndpointGalerkinWholeStateAtTime
        ledger radius time) := by
  simpa [generatedVelocityEndpointGalerkinWholeStateAtTime,
    finiteStateWholeVelocity] using
      finiteStateWholeVelocity_transverse
        (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory time)

/-- The actual unprojected whole velocity convection row as one continuous
bounded path on the common physical interval. -/
def generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) 1) ComplexCoordinateVector :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time =>
        wholeStateVelocityNonlinearCoefficientAt
          (generatedVelocityEndpointGalerkinWholeState
            ledger radius time) output,
      by
        have velocityContinuousOn :
            ContinuousOn
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger radius) (Icc (0 : ℝ) 1) := by
          rw [continuousOn_iff_continuous_restrict]
          change Continuous
            (generatedVelocityEndpointGalerkinWholeState ledger radius)
          exact
            generatedVelocityEndpointGalerkinWholeState_continuous
              ledger radius
        exact
          (wholeStateVelocityNonlinearCoefficientAt_comp_continuousOn
            (generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger radius)
            output 0 1 velocityContinuousOn
            (fun time _timeMem =>
              generatedVelocityEndpointGalerkinWholeStateAtTime_transverse
                ledger radius time)).restrict⟩

/-- The same actual unprojected row in the complete `L¹_t` carrier. -/
def generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector) :
    NonlinearRowSpaceTimeState 1 :=
  BoundedContinuousFunction.toLp 1 (commonTimeMeasure 1) ℂ
    (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
      ledger radius output)

/-! ## Exact `L²` and `L¹` integral ledgers -/

theorem generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_eq_intervalIntegral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius‖ ^ 2 =
      ∫ time in (0 : ℝ)..1,
        ‖generatedVelocityEndpointGalerkinWholeStateAtTime
          ledger radius time‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)
  calc
    (∫ time,
        ‖generatedVelocityEndpointGalerkinSpaceTimePath
          ledger radius time‖ ^ 2 ∂(commonTimeMeasure 1)) =
      ∫ time : Icc (0 : ℝ) 1,
        ‖generatedVelocityEndpointGalerkinWholeState
          ledger radius time‖ ^ 2 ∂(commonTimeMeasure 1) := by
      apply integral_congr_ae
      filter_upwards [pathAE] with time pathEq
      change
        ‖((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure 1) ℂ)
          (generatedVelocityEndpointGalerkinWholeBoundedPath
            ledger radius)) time‖ ^ 2 = _
      rw [pathEq]
      rfl
    _ = _ := by
      simpa [generatedVelocityEndpointGalerkinWholeState] using
        commonTime_integral_eq_intervalIntegral
          1 (by norm_num)
          (fun time =>
            ‖generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger radius time‖ ^ 2)

theorem generatedVelocityEndpointGalerkinSpaceTimePath_sub_norm_sq_eq_intervalIntegral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (leftRadius rightRadius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius -
        generatedVelocityEndpointGalerkinSpaceTimePath ledger rightRadius‖ ^ 2 =
      ∫ time in (0 : ℝ)..1,
        ‖generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger leftRadius time -
            generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger rightRadius time‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  have leftAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath
        ledger leftRadius)
  have rightAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath
        ledger rightRadius)
  have subAE := MeasureTheory.Lp.coeFn_sub
    (generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius)
    (generatedVelocityEndpointGalerkinSpaceTimePath ledger rightRadius)
  calc
    (∫ time,
        ‖(generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius -
            generatedVelocityEndpointGalerkinSpaceTimePath
              ledger rightRadius) time‖ ^ 2
          ∂(commonTimeMeasure 1)) =
      ∫ time : Icc (0 : ℝ) 1,
        ‖generatedVelocityEndpointGalerkinWholeState
              ledger leftRadius time -
            generatedVelocityEndpointGalerkinWholeState
              ledger rightRadius time‖ ^ 2
          ∂(commonTimeMeasure 1) := by
      apply integral_congr_ae
      filter_upwards [subAE, leftAE, rightAE] with
        time subEq leftEq rightEq
      rw [subEq]
      change
        ‖((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure 1) ℂ)
              (generatedVelocityEndpointGalerkinWholeBoundedPath
                ledger leftRadius)) time -
            ((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure 1) ℂ)
              (generatedVelocityEndpointGalerkinWholeBoundedPath
                ledger rightRadius)) time‖ ^ 2 = _
      rw [leftEq, rightEq]
      rfl
    _ = _ := by
      simpa [generatedVelocityEndpointGalerkinWholeState] using
        commonTime_integral_eq_intervalIntegral
          1 (by norm_num)
          (fun time =>
            ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger leftRadius time -
                generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger rightRadius time‖ ^ 2)

theorem generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath_sub_norm_eq_intervalIntegral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (leftRadius rightRadius : ℕ)
    (output : IntegerWavevector) :
    ‖generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger leftRadius output -
        generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger rightRadius output‖ =
      ∫ time in (0 : ℝ)..1,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger leftRadius time) output -
            wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger rightRadius time) output‖ := by
  rw [nonlinearRowSpaceTimeState_norm_eq_integral]
  have leftAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
        ledger leftRadius output)
  have rightAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
        ledger rightRadius output)
  have subAE := MeasureTheory.Lp.coeFn_sub
    (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
      ledger leftRadius output)
    (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
      ledger rightRadius output)
  calc
    (∫ time,
        ‖(generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
              ledger leftRadius output -
            generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
              ledger rightRadius output) time‖
          ∂(commonTimeMeasure 1)) =
      ∫ time : Icc (0 : ℝ) 1,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeState
                ledger leftRadius time) output -
            wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeState
                ledger rightRadius time) output‖
          ∂(commonTimeMeasure 1) := by
      apply integral_congr_ae
      filter_upwards [subAE, leftAE, rightAE] with
        time subEq leftEq rightEq
      rw [subEq]
      change
        ‖((BoundedContinuousFunction.toLp 1
              (commonTimeMeasure 1) ℂ)
              (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
                ledger leftRadius output)) time -
            ((BoundedContinuousFunction.toLp 1
              (commonTimeMeasure 1) ℂ)
              (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
                ledger rightRadius output)) time‖ = _
      rw [leftEq, rightEq]
      rfl
    _ = _ := by
      simpa [generatedVelocityEndpointGalerkinWholeState] using
        commonTime_integral_eq_intervalIntegral
          1 (by norm_num)
          (fun time =>
            ‖wholeStateVelocityNonlinearCoefficientAt
                  (generatedVelocityEndpointGalerkinWholeStateAtTime
                    ledger leftRadius time) output -
                wholeStateVelocityNonlinearCoefficientAt
                  (generatedVelocityEndpointGalerkinWholeStateAtTime
                    ledger rightRadius time) output‖)

/-! ## Whole `L²` to nonlinear-row `L¹` passage -/

theorem generatedVelocityEndpointGalerkinWholeNonlinearRow_intervalIntegral_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (leftRadius rightRadius : ℕ)
    (output : IntegerWavevector) :
    (∫ time in (0 : ℝ)..1,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger leftRadius time) output -
            wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger rightRadius time) output‖) ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt
          (∫ time in (0 : ℝ)..1,
            ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger leftRadius time -
                generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger rightRadius time‖ ^ 2) *
        (Real.sqrt
            (∫ time in (0 : ℝ)..1,
              ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger leftRadius time‖ ^ 2) +
          Real.sqrt
            (∫ time in (0 : ℝ)..1,
              ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger rightRadius time‖ ^ 2)) := by
  let left :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger leftRadius
  let right :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger rightRadius
  have leftContinuous : ContinuousOn left (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger leftRadius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous
      ledger leftRadius
  have rightContinuous : ContinuousOn right (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger rightRadius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous
      ledger rightRadius
  simpa only [left, right] using
    wholeStateVelocityNonlinearCoefficientAt_sub_norm_intervalIntegral_le
      left right output 0 1 (by norm_num)
      leftContinuous rightContinuous
      (fun time _timeMem =>
        generatedVelocityEndpointGalerkinWholeStateAtTime_transverse
          ledger leftRadius time)
      (fun time _timeMem =>
        generatedVelocityEndpointGalerkinWholeStateAtTime_transverse
          ledger rightRadius time)

/-- Exact source-family nonlinear passage in the common carriers. -/
theorem generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath_sub_norm_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (leftRadius rightRadius : ℕ)
    (output : IntegerWavevector) :
    ‖generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger leftRadius output -
        generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger rightRadius output‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius -
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger rightRadius‖ *
        (‖generatedVelocityEndpointGalerkinSpaceTimePath
            ledger leftRadius‖ +
          ‖generatedVelocityEndpointGalerkinSpaceTimePath
            ledger rightRadius‖) := by
  have integrated :=
    generatedVelocityEndpointGalerkinWholeNonlinearRow_intervalIntegral_le
      ledger leftRadius rightRadius output
  rw [
    ← generatedVelocityEndpointGalerkinSpaceTimePath_sub_norm_sq_eq_intervalIntegral
      ledger leftRadius rightRadius,
    ← generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_eq_intervalIntegral
      ledger leftRadius,
    ← generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_eq_intervalIntegral
      ledger rightRadius,
    Real.sqrt_sq (norm_nonneg
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius -
        generatedVelocityEndpointGalerkinSpaceTimePath ledger rightRadius)),
    Real.sqrt_sq (norm_nonneg
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger leftRadius)),
    Real.sqrt_sq (norm_nonneg
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger rightRadius))]
      at integrated
  rw [
    generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath_sub_norm_eq_intervalIntegral]
  exact integrated

/-! ## Cauchy transport and internally generated nonlinear limit -/

/-- Every Cauchy sequence of actual whole velocity Galerkin paths transports
to a Cauchy sequence of complete nonlinear rows at the same fixed output. -/
theorem generatedVelocityEndpointGalerkinWholeNonlinearRow_cauchySeq_of_spaceTime_cauchySeq
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radii : ℕ → ℕ)
    (output : IntegerWavevector)
    (wholeCauchy :
      CauchySeq fun index =>
        generatedVelocityEndpointGalerkinSpaceTimePath
          ledger (radii index)) :
    CauchySeq fun index =>
      generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
        ledger (radii index) output := by
  let stateSequence : ℕ → SpaceTimeState 1 := fun index =>
    generatedVelocityEndpointGalerkinSpaceTimePath ledger (radii index)
  let nonlinearSequence : ℕ → NonlinearRowSpaceTimeState 1 := fun index =>
    generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
      ledger (radii index) output
  have stateCauchy : CauchySeq stateSequence := by
    simpa [stateSequence] using wholeCauchy
  obtain ⟨stateLimit, stateTendsto⟩ :=
    cauchySeq_tendsto_of_complete stateCauchy
  have stateDistanceTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          dist (stateSequence indices.1) (stateSequence indices.2))
        atTop (nhds 0) :=
    cauchySeq_iff_tendsto_dist_atTop_0.mp stateCauchy
  have fstAtTop :
      Tendsto (fun indices : ℕ × ℕ => indices.1)
        atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have sndAtTop :
      Tendsto (fun indices : ℕ × ℕ => indices.2)
        atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have stateNormSumTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          ‖stateSequence indices.1‖ + ‖stateSequence indices.2‖)
        atTop (nhds (‖stateLimit‖ + ‖stateLimit‖)) :=
    (stateTendsto.norm.comp fstAtTop).add
      (stateTendsto.norm.comp sndAtTop)
  let angular : ℝ :=
    (6 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  have boundTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          angular *
            dist (stateSequence indices.1) (stateSequence indices.2) *
            (‖stateSequence indices.1‖ + ‖stateSequence indices.2‖))
        atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul stateDistanceTendsto).mul
        stateNormSumTendsto)
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  apply squeeze_zero
    (g := fun indices : ℕ × ℕ =>
      angular *
        dist (stateSequence indices.1) (stateSequence indices.2) *
        (‖stateSequence indices.1‖ + ‖stateSequence indices.2‖))
  · intro indices
    exact dist_nonneg
  · intro indices
    rw [dist_eq_norm]
    have bound :=
      generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath_sub_norm_le
        ledger (radii indices.1) (radii indices.2) output
    simpa [nonlinearSequence, stateSequence, angular, dist_eq_norm] using bound
  · exact boundTendsto

/-- The source-generated strong velocity subsequence carries, at the same
fixed output and without a second extraction, one internally generated
complete nonlinear-row limit. -/
theorem generatedVelocityEndpointGalerkinSpaceTimePath_strong_subsequence_with_nonlinearRow_limit
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (output : IntegerWavevector) :
    ∃ stateLimit : SpaceTimeState 1,
      stateLimit ∈
          closure
            (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              generatedVelocityEndpointGalerkinSpaceTimePath
                ledger (subsequence index))
            atTop (nhds stateLimit) ∧
        ∃ nonlinearLimit : NonlinearRowSpaceTimeState 1,
          Tendsto
              (fun index =>
                generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
                  ledger (subsequence index) output)
              atTop (nhds nonlinearLimit) := by
  obtain
      ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
        stateTendsto, _stateStrong, _initialTendsto,
        _initialEnergyTendsto, _fixedWaveTendsto, _fixedWaveStrong⟩ :=
    generatedVelocityEndpointGalerkinSpaceTimePath_strong_subsequence_with_fixed_wave_rows
      ledger
  have stateCauchy :
      CauchySeq fun index =>
        generatedVelocityEndpointGalerkinSpaceTimePath
          ledger (subsequence index) :=
    stateTendsto.cauchy_map
  have nonlinearCauchy :
      CauchySeq fun index =>
        generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger (subsequence index) output :=
    generatedVelocityEndpointGalerkinWholeNonlinearRow_cauchySeq_of_spaceTime_cauchySeq
      ledger subsequence output stateCauchy
  obtain ⟨nonlinearLimit, nonlinearTendsto⟩ :=
    cauchySeq_tendsto_of_complete nonlinearCauchy
  exact
    ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
      stateTendsto, nonlinearLimit, nonlinearTendsto⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage
end NavierStokes
end SaturationMonoid
