import H0mework.NavierStokes.ShellGluing.NativeMacroRedirectRuntime
import H0mework.NavierStokes.Fourier.CanonicalExhaustiveGalerkinTarget

/-!
# Adaptive Duhamel residual telescope for native macro redirects

Every redirected macro owns one actual positive-time unforced Galerkin
receipt.  Adjacent endpoints glue, while the finite support may change.
Consequently the honest whole-lattice readout is not one fixed Galerkin
vector field.  It is the exact segmentwise split

```text
finite tangent = whole-lattice tangent + whole-lattice PDE residual.
```

This file integrates that split before any coefficient quotient and
telescopes it over an arbitrary prefix of the actual source-generated
lineage.  The theorem mouth contains only the lineage and prefix length.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroAdaptiveDuhamelResidualTelescope

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage

noncomputable section

/-! ## Direct readouts of one actual macro segment -/

/-- Recollected physical state at one actual macro boundary. -/
def adaptivePhysicalState
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ComplexVorticityHilbertState :=
  recollectedPhysicalState (lineage.current index)

/-- Exact finite Galerkin tangent of the actual receipt. -/
def adaptiveFiniteTangent
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (time : ℝ) :
    ComplexVorticityHilbertState :=
  finiteStateVorticityGenerator
    (generatedSupport
      (completeOmittedPhysicalLiftSource
        (lineage.current index).physicalSource))
    ν.coeff
    ((lineage.physicalReceipt index).trajectory time)

/-- Whole-lattice tangent read from the same actual state and time. -/
def adaptiveWholeTangent
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (time : ℝ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  wholeLatticeVorticityFourierTangentAt
    ν.coeff
    ((lineage.physicalReceipt index).trajectory time)
    wave

/--
Whole-lattice PDE residual of the actual finite tangent.  The sign is fixed:

```text
residual = finite tangent - whole tangent.
```
-/
def adaptiveWholeResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (time : ℝ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    ((lineage.physicalReceipt index).trajectory time)
    (adaptiveFiniteTangent lineage index time)
    wave

/-- Integrated whole-lattice tangent of one actual macro segment. -/
def adaptiveWholeTangentIntegral
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  ∫ time in (0 : ℝ)..(lineage.physicalReceipt index).duration,
    adaptiveWholeTangent lineage index time wave

/-- Integrated changing-support residual of one actual macro segment. -/
def adaptiveWholeResidualIntegral
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  ∫ time in (0 : ℝ)..(lineage.physicalReceipt index).duration,
    adaptiveWholeResidual lineage index time wave

/-! ## Segment continuity and exact Duhamel split -/

theorem adaptiveTrajectory_continuousOn
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ContinuousOn
      (lineage.physicalReceipt index).trajectory
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration) := by
  intro time timeMem
  exact
    ((lineage.physicalReceipt index).physical time timeMem).1.continuousAt
      |>.continuousWithinAt

theorem adaptiveFiniteTangent_continuousOn
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ContinuousOn
      (adaptiveFiniteTangent lineage index)
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration) := by
  exact
    (finiteStateVorticityGenerator_contDiff
      (generatedSupport
        (completeOmittedPhysicalLiftSource
          (lineage.current index).physicalSource))
      ν.coeff).continuous.comp_continuousOn
        (adaptiveTrajectory_continuousOn lineage index)

theorem adaptiveFiniteTangentCoordinate_continuousOn
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    ContinuousOn
      (fun time => adaptiveFiniteTangent lineage index time wave)
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration) := by
  exact
    (lp.evalCLM
      ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous
      |>.comp_continuousOn
        (adaptiveFiniteTangent_continuousOn lineage index)

/-- The same actual path, restricted to its physical interval and carrying
the transversality generated by the receipt. -/
private def adaptiveTransverseRestrictedPath
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Icc (0 : ℝ) (lineage.physicalReceipt index).duration →
      WholeTransverseVorticityState :=
  fun time =>
    ⟨(lineage.physicalReceipt index).trajectory time.1,
      fun wave =>
        ((lineage.physicalReceipt index).physical time.1 time.2).2.2.1
          wave⟩

private theorem adaptiveTransverseRestrictedPath_continuous
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Continuous (adaptiveTransverseRestrictedPath lineage index) := by
  apply Continuous.subtype_mk
  exact (adaptiveTrajectory_continuousOn lineage index).restrict

theorem adaptiveWholeTangent_continuousOn
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    ContinuousOn
      (fun time => adaptiveWholeTangent lineage index time wave)
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration) := by
  rw [continuousOn_iff_continuous_restrict]
  have nonlinearContinuous :
      Continuous
        (fun time :
            Icc (0 : ℝ) (lineage.physicalReceipt index).duration =>
          wholeStateVorticityNonlinearCoefficientAt
            ((lineage.physicalReceipt index).trajectory time.1)
            wave) := by
    change
      Continuous
        ((fun state : WholeTransverseVorticityState =>
            wholeStateVorticityNonlinearCoefficientAt state.1 wave) ∘
          adaptiveTransverseRestrictedPath lineage index)
    exact
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        (adaptiveTransverseRestrictedPath_continuous lineage index)
  have waveContinuous :
      Continuous
        (fun time :
            Icc (0 : ℝ) (lineage.physicalReceipt index).duration =>
          (lineage.physicalReceipt index).trajectory time.1 wave) := by
    exact
      (lp.evalCLM
        ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
          (adaptiveTrajectory_continuousOn lineage index).restrict
  change
    Continuous
      (fun time :
          Icc (0 : ℝ) (lineage.physicalReceipt index).duration =>
        wholeStateVorticityNonlinearCoefficientAt
              ((lineage.physicalReceipt index).trajectory time.1) wave -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            (lineage.physicalReceipt index).trajectory time.1 wave)
  exact
    nonlinearContinuous.sub
      (waveContinuous.const_smul
        (ν.coeff * integerWaveViscousMultiplier wave))

theorem adaptiveWholeResidual_continuousOn
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    ContinuousOn
      (fun time => adaptiveWholeResidual lineage index time wave)
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration) := by
  change
    ContinuousOn
      ((fun time => adaptiveFiniteTangent lineage index time wave) -
        fun time => adaptiveWholeTangent lineage index time wave)
      (Icc (0 : ℝ) (lineage.physicalReceipt index).duration)
  exact
    (adaptiveFiniteTangentCoordinate_continuousOn
      lineage index wave).sub
      (adaptiveWholeTangent_continuousOn lineage index wave)

theorem adaptiveFiniteTangentCoordinate_intervalIntegrable
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (fun time => adaptiveFiniteTangent lineage index time wave)
      MeasureTheory.volume
      0
      (lineage.physicalReceipt index).duration :=
  (adaptiveFiniteTangentCoordinate_continuousOn lineage index wave)
    |>.intervalIntegrable_of_Icc
      (lineage.physicalReceipt index).duration_pos.le

theorem adaptiveWholeTangent_intervalIntegrable
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (fun time => adaptiveWholeTangent lineage index time wave)
      MeasureTheory.volume
      0
      (lineage.physicalReceipt index).duration :=
  (adaptiveWholeTangent_continuousOn lineage index wave)
    |>.intervalIntegrable_of_Icc
      (lineage.physicalReceipt index).duration_pos.le

theorem adaptiveWholeResidual_intervalIntegrable
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (fun time => adaptiveWholeResidual lineage index time wave)
      MeasureTheory.volume
      0
      (lineage.physicalReceipt index).duration :=
  (adaptiveWholeResidual_continuousOn lineage index wave)
    |>.intervalIntegrable_of_Icc
      (lineage.physicalReceipt index).duration_pos.le

/-- Fundamental theorem of calculus on one exact actual receipt. -/
theorem adaptiveFiniteTangentIntegral_eq_physicalState_sub
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    (∫ time in (0 : ℝ)..(lineage.physicalReceipt index).duration,
        adaptiveFiniteTangent lineage index time wave) =
      adaptivePhysicalState lineage (index + 1) wave -
        adaptivePhysicalState lineage index wave := by
  have derivative :
      ∀ time ∈
          uIcc (0 : ℝ) (lineage.physicalReceipt index).duration,
        HasDerivAt
          (fun later =>
            (lineage.physicalReceipt index).trajectory later wave)
          (adaptiveFiniteTangent lineage index time wave)
          time := by
    intro time timeMem
    have timeMemIcc :
        time ∈
          Icc (0 : ℝ) (lineage.physicalReceipt index).duration := by
      simpa [
        uIcc_of_le
          (lineage.physicalReceipt index).duration_pos.le] using
        timeMem
    exact
      complexVorticityTrajectoryWave_hasDerivAt
        (lineage.physicalReceipt index).trajectory
        time
        (adaptiveFiniteTangent lineage index time)
        wave
        ((lineage.physicalReceipt index).physical
          time timeMemIcc).1
  have integralWrite :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      derivative
      (adaptiveFiniteTangentCoordinate_intervalIntegrable
        lineage index wave)
  have projection :=
    (lineage.step index).physicalProjection_unforced_commutes
  have initial :
      (lineage.physicalReceipt index).trajectory 0 =
        adaptivePhysicalState lineage index := by
    exact projection.1
  have endpoint :
      adaptivePhysicalState lineage (index + 1) =
        (lineage.physicalReceipt index).endpoint := by
    exact projection.2.2
  rw [integralWrite]
  change
    (lineage.physicalReceipt index).trajectory
          (lineage.physicalReceipt index).duration wave -
        (lineage.physicalReceipt index).trajectory 0 wave =
      adaptivePhysicalState lineage (index + 1) wave -
        adaptivePhysicalState lineage index wave
  rw [initial]
  simpa [GeneratedTimeAdvanceReceipt.endpoint] using
    congrArg (fun state : ComplexVorticityHilbertState => state wave)
      endpoint.symm

/--
One actual macro segment satisfies the honest whole-lattice Duhamel split.
No target trajectory or defect is supplied by the caller.
-/
theorem adaptiveSegment_duhamel_residual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    adaptivePhysicalState lineage (index + 1) wave -
        adaptivePhysicalState lineage index wave =
      adaptiveWholeTangentIntegral lineage index wave +
        adaptiveWholeResidualIntegral lineage index wave := by
  have finiteIntegrable :=
    adaptiveFiniteTangentCoordinate_intervalIntegrable
      lineage index wave
  have wholeIntegrable :=
    adaptiveWholeTangent_intervalIntegrable
      lineage index wave
  have residualIntegrable :=
    adaptiveWholeResidual_intervalIntegrable
      lineage index wave
  calc
    adaptivePhysicalState lineage (index + 1) wave -
          adaptivePhysicalState lineage index wave =
        ∫ time in (0 : ℝ)..(lineage.physicalReceipt index).duration,
          adaptiveFiniteTangent lineage index time wave := by
            symm
            exact
              adaptiveFiniteTangentIntegral_eq_physicalState_sub
                lineage index wave
    _ =
        ∫ time in (0 : ℝ)..(lineage.physicalReceipt index).duration,
          (adaptiveWholeTangent lineage index time wave +
            adaptiveWholeResidual lineage index time wave) := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              simp only [adaptiveWholeResidual, adaptiveWholeTangent,
                wholeLatticeVorticityFourierPDEResidualAt]
              abel
    _ =
        adaptiveWholeTangentIntegral lineage index wave +
          adaptiveWholeResidualIntegral lineage index wave := by
            exact
              intervalIntegral.integral_add
                wholeIntegrable residualIntegrable

/-! ## Arbitrary actual-prefix telescope -/

/-- Whole-lattice tangent integral accumulated over an actual prefix. -/
def adaptiveWholeTangentIntegralPrefix
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  fun wave =>
    ∑ index ∈ Finset.range length,
      adaptiveWholeTangentIntegral lineage index wave

/-- Source-owned changing-support residual accumulated over the same prefix. -/
def adaptiveWholeResidualIntegralPrefix
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  fun wave =>
    ∑ index ∈ Finset.range length,
      adaptiveWholeResidualIntegral lineage index wave

/--
Exact arbitrary-prefix endpoint telescope, pointwise on the complete Fourier
carrier.
-/
theorem adaptivePrefix_duhamel_residual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ (length : ℕ) (wave : IntegerWavevector),
      adaptivePhysicalState lineage length wave -
          adaptivePhysicalState lineage 0 wave =
        adaptiveWholeTangentIntegralPrefix lineage length wave +
          adaptiveWholeResidualIntegralPrefix lineage length wave
  | 0, wave => by
      simp [adaptiveWholeTangentIntegralPrefix,
        adaptiveWholeResidualIntegralPrefix]
  | length + 1, wave => by
      rw [show
        adaptivePhysicalState lineage (length + 1) wave -
              adaptivePhysicalState lineage 0 wave =
            (adaptivePhysicalState lineage (length + 1) wave -
                adaptivePhysicalState lineage length wave) +
              (adaptivePhysicalState lineage length wave -
                adaptivePhysicalState lineage 0 wave) by
          abel,
        adaptiveSegment_duhamel_residual lineage length wave,
        adaptivePrefix_duhamel_residual lineage length wave]
      simp [adaptiveWholeTangentIntegralPrefix,
        adaptiveWholeResidualIntegralPrefix,
        Finset.sum_range_succ]
      abel

/--
Whole-carrier form of the arbitrary-prefix identity.  The second summand is
the uniquely generated accumulated defect of the changing finite supports;
it has not been discarded or renamed as a target forcing.
-/
theorem adaptivePrefix_duhamel_residual_wholeCarrier
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    (fun wave =>
      adaptivePhysicalState lineage length wave -
        adaptivePhysicalState lineage 0 wave) =
      adaptiveWholeTangentIntegralPrefix lineage length +
        adaptiveWholeResidualIntegralPrefix lineage length := by
  funext wave
  exact adaptivePrefix_duhamel_residual lineage length wave

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroAdaptiveDuhamelResidualTelescope
end NavierStokes
end SaturationMonoid
