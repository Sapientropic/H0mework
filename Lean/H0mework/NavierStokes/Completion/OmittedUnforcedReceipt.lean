import H0mework.NavierStokes.Completion.OmittedSupport
import H0mework.NavierStokes.ShellSources.ConsumeBeforeQuotient

/-!
# Consume the complete generated nonlinear responsibility before quotient

One source event can generate several nonzero nonlinear rows which are absent
from its live coefficient table.  Some coordinates are already owned by the
current Galerkin carrier; the others are genuine support holes.  This module
settles both cases on the physical quantity which already owns the
Navier--Stokes equation:

```text
source-generated complete nonlive output q
→ owned dormant row: current Galerkin tangent = q
→ missing row: conservative zero-filled carrier installation
→ one actual positive-time unforced Galerkin receipt
→ time-zero derivative = q
→ full-PDE residual on the complete carrier = 0.
```

Every row is consumed before receipts from different source events can be
added at a common Fourier frequency.  No occurrence norm, completion, debt
carrier, prescribed state jump, branch witness, or smallness parameter is
introduced.  The old whole-shell source write remains authoritative; the
receipt below is its complete target-side physical consumer.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellConsumeBeforeQuotient
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

noncomputable section

/-! ## Conservative physical carrier installation -/

/--
Recompile the old physical state on the complete source-owned nonlinear
carrier.  Missing coordinates are installed at zero amplitude.
-/
def completeOmittedPhysicalLiftSource
    (source : RawVorticityFourierSource) :
    RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState
    (generatedCompleteNonlinearGalerkinModes source)
    (generatedComplexVorticityState source
      (generatedSupport source))

theorem completeOmittedPhysicalLiftSource_generatedSupport
    (source : RawVorticityFourierSource) :
    generatedSupport (completeOmittedPhysicalLiftSource source) =
      generatedCompleteNonlinearGalerkinModes source := by
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      (generatedCompleteNonlinearGalerkinModes source)
      (zero_not_mem_completeNonlinearGalerkinModes source)
      (fun wave waveMem =>
        (mem_completeNonlinearGalerkinModes_waveNeg_iff
          source wave).mpr waveMem)
      (generatedComplexVorticityState source
        (generatedSupport source))

/--
The complete support installation is conservative on the whole ambient
physical state.
-/
theorem completeOmittedPhysicalLiftSource_generatedState
    (source : RawVorticityFourierSource) :
    generatedComplexVorticityState
        (completeOmittedPhysicalLiftSource source)
        (generatedSupport (completeOmittedPhysicalLiftSource source)) =
      generatedCompleteNonlinearInitialState source := by
  calc
    generatedComplexVorticityState
        (completeOmittedPhysicalLiftSource source)
        (generatedSupport (completeOmittedPhysicalLiftSource source)) =
      generatedComplexVorticityState source
        (generatedSupport source) := by
      exact
        rawSourceOfGeneratedPhysicalState_supportLift_generatedState
          source
          (generatedCompleteNonlinearGalerkinModes source)
          (generatedSupport_subset_completeNonlinearGalerkinModes source)
          (zero_not_mem_completeNonlinearGalerkinModes source)
          (fun wave waveMem =>
            (mem_completeNonlinearGalerkinModes_waveNeg_iff
              source wave).mpr waveMem)
    _ = generatedCompleteNonlinearInitialState source :=
      (generatedCompleteNonlinearInitialState_eq_currentPhysicalState
        source).symm

/-! ## Exact current and complete-carrier tangents -/

/--
Every active nonlive output has the exact old source nonlinear row as its
complete-carrier Galerkin tangent.  The viscous row vanishes because the
coordinate starts at zero.
-/
theorem completeGalerkinGenerator_activeNonlive
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedActiveNonliveNonlinearModes source) :
    finiteStateVorticityGenerator
        (generatedCompleteNonlinearGalerkinModes source)
        ν
        (generatedCompleteNonlinearInitialState source)
        output =
      generatedVorticityNonlinearCoefficientAt source output := by
  have outputGalerkinMem :
      output ∈ generatedCompleteNonlinearGalerkinModes source :=
    generatedActiveNonliveNonlinearModes_subset_completeGalerkinModes
      source outputMem
  have nonlinearEq :
      finiteStateVorticityNonlinearCoefficientAt
          (generatedCompleteNonlinearGalerkinModes source)
          (generatedCompleteNonlinearInitialState source)
          output =
        generatedVorticityNonlinearCoefficientAt source output := by
    change
      finiteStateVorticityNonlinearCoefficientAt
          (generatedCompleteNonlinearGalerkinModes source)
          (generatedComplexVorticityState source
            (generatedCompleteNonlinearGalerkinModes source))
          output =
        generatedVorticityNonlinearCoefficientAt source output
    exact
      finiteStateVorticityNonlinearCoefficientAt_generatedSource_of_subset
        source
        (generatedCompleteNonlinearGalerkinModes source)
        (generatedSupport_subset_completeNonlinearGalerkinModes source)
        output
  have stateZero :
      generatedCompleteNonlinearInitialState source output = 0 :=
    generatedCompleteNonlinearInitialState_activeNonlive_zero
      source outputMem
  rw [finiteStateVorticityGenerator_apply, if_pos outputGalerkinMem,
    nonlinearEq, stateZero]
  simp

/--
An already owned dormant coordinate needs no support installation: its
current Galerkin tangent already equals the generated nonlinear row.
-/
theorem currentGalerkinGenerator_ownedDormant
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedOwnedDormantNonlinearModes source) :
    finiteStateVorticityGenerator
        (generatedSupport source)
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        output =
      generatedVorticityNonlinearCoefficientAt source output := by
  have supportMem :
      output ∈ generatedSupport source :=
    ((mem_generatedOwnedDormantNonlinearModes_iff
      source output).mp outputMem).2
  have activeMem :
      output ∈ generatedActiveNonliveNonlinearModes source :=
    ((mem_generatedOwnedDormantNonlinearModes_iff
      source output).mp outputMem).1
  rw [finiteStateVorticityGenerator_apply, if_pos supportMem,
    finiteStateVorticityNonlinearCoefficientAt_generatedSource]
  have stateZero :
      generatedComplexVorticityState source
          (generatedSupport source) output =
        0 := by
    rw [← generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
    exact
      generatedCompleteNonlinearInitialState_activeNonlive_zero
        source activeMem
  rw [stateZero]
  simp

/-! ## Full-PDE residual before and after installation -/

/--
A genuinely missing coordinate is an exact nonzero full-PDE residual on the
old owned carrier.
-/
theorem currentFullPDEResidual_missing_eq_neg_generated
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedMissingNonlinearModes source) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedSupport source)
          ν
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output =
      -generatedVorticityNonlinearCoefficientAt source output := by
  have outputNotSupport :
      output ∉ generatedSupport source :=
    ((mem_generatedMissingNonlinearModes_iff
      source output).mp outputMem).2
  have stateZero :
      generatedComplexVorticityState source
          (generatedSupport source) output =
        0 := by
    rw [generatedComplexVorticityState_apply, if_neg outputNotSupport]
  rw [wholeLatticeVorticityFourierPDEResidualAt,
    finiteStateVorticityGenerator_apply, if_neg outputNotSupport,
    wholeLatticeVorticityFourierTangentAt,
    wholeStateNonlinearCoefficient_generatedSource,
    stateZero]
  simp

theorem currentFullPDEResidual_missing_ne_zero
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedMissingNonlinearModes source) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedSupport source)
          ν
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output ≠
      0 := by
  rw [currentFullPDEResidual_missing_eq_neg_generated
    source ν outputMem]
  exact
    neg_ne_zero.mpr
      ((mem_generatedActiveNonliveNonlinearModes_iff
        source output).mp
          ((mem_generatedMissingNonlinearModes_iff
            source output).mp outputMem).1).2.2.2

/--
An already owned dormant responsibility has zero full-PDE residual precisely
because its current Galerkin tangent already consumes the row.
-/
theorem currentFullPDEResidual_ownedDormant_eq_zero
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedOwnedDormantNonlinearModes source) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedSupport source)
          ν
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output =
      0 := by
  have activeMem :
      output ∈ generatedActiveNonliveNonlinearModes source :=
    ((mem_generatedOwnedDormantNonlinearModes_iff
      source output).mp outputMem).1
  have stateZero :
      generatedComplexVorticityState source
          (generatedSupport source) output =
        0 := by
    rw [← generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
    exact
      generatedCompleteNonlinearInitialState_activeNonlive_zero
        source activeMem
  rw [wholeLatticeVorticityFourierPDEResidualAt,
    currentGalerkinGenerator_ownedDormant source ν outputMem,
    wholeLatticeVorticityFourierTangentAt,
    wholeStateNonlinearCoefficient_generatedSource,
    stateZero]
  simp

/--
After the complete support installation, every active responsibility has zero
full-PDE residual on the expanded carrier.
-/
theorem completeGalerkinFullPDEResidual_activeNonlive_eq_zero
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedActiveNonliveNonlinearModes source) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedCompleteNonlinearInitialState source)
        (finiteStateVorticityGenerator
          (generatedCompleteNonlinearGalerkinModes source)
          ν
          (generatedCompleteNonlinearInitialState source))
        output =
      0 := by
  have wholeNonlinearEq :
      wholeStateVorticityNonlinearCoefficientAt
          (generatedCompleteNonlinearInitialState source)
          output =
        generatedVorticityNonlinearCoefficientAt source output := by
    rw [generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
    exact wholeStateNonlinearCoefficient_generatedSource source output
  have stateZero :
      generatedCompleteNonlinearInitialState source output = 0 :=
    generatedCompleteNonlinearInitialState_activeNonlive_zero
      source outputMem
  rw [wholeLatticeVorticityFourierPDEResidualAt,
    completeGalerkinGenerator_activeNonlive source ν outputMem,
    wholeLatticeVorticityFourierTangentAt,
    wholeNonlinearEq, stateZero]
  simp

/-! ## One actual unforced receipt consumes the whole generated inventory -/

/--
Canonical actual positive-time unforced receipt on the complete generated
carrier.
-/
def completeOmittedPhysicalTimeReceipt
    (source : RawVorticityFourierSource)
    (ν : Viscosity) :
    GeneratedTimeAdvanceReceipt
      (completeOmittedPhysicalLiftSource source) ν.coeff :=
  generatedTimeAdvanceReceipt
    (completeOmittedPhysicalLiftSource source) ν.coeff

theorem completeOmittedPhysicalTimeReceipt_initial
    (source : RawVorticityFourierSource)
    (ν : Viscosity) :
    (completeOmittedPhysicalTimeReceipt source ν).trajectory 0 =
      generatedCompleteNonlinearInitialState source := by
  exact
    (completeOmittedPhysicalTimeReceipt source ν).initial.trans
      (completeOmittedPhysicalLiftSource_generatedState source)

theorem completeOmittedPhysicalTimeReceipt_activeNonlive_derivative
    (source : RawVorticityFourierSource)
    (ν : Viscosity)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedActiveNonliveNonlinearModes source) :
    HasDerivAt
        (fun time =>
          (completeOmittedPhysicalTimeReceipt source ν).trajectory
            time output)
        (generatedVorticityNonlinearCoefficientAt source output)
        0 := by
  let receipt := completeOmittedPhysicalTimeReceipt source ν
  have zeroInTime :
      (0 : ℝ) ∈ Icc (0 : ℝ) receipt.duration :=
    ⟨le_rfl, receipt.duration_pos.le⟩
  have actualLaw := (receipt.physical 0 zeroInTime).1
  have rowLaw :=
    complexVorticityTrajectoryWave_hasDerivAt
      receipt.trajectory 0
      (finiteStateVorticityGenerator
        (generatedSupport (completeOmittedPhysicalLiftSource source))
        ν.coeff
        (receipt.trajectory 0))
      output actualLaw
  rw [show receipt.trajectory 0 =
        generatedCompleteNonlinearInitialState source by
      exact completeOmittedPhysicalTimeReceipt_initial source ν,
    completeOmittedPhysicalLiftSource_generatedSupport,
    completeGalerkinGenerator_activeNonlive
      source ν.coeff outputMem] at rowLaw
  exact rowLaw

theorem completeOmittedPhysicalTimeReceipt_activeNonlive_initial_zero
    (source : RawVorticityFourierSource)
    (ν : Viscosity)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedActiveNonliveNonlinearModes source) :
    (completeOmittedPhysicalTimeReceipt source ν).trajectory 0 output =
      0 := by
  rw [completeOmittedPhysicalTimeReceipt_initial]
  exact
    generatedCompleteNonlinearInitialState_activeNonlive_zero
      source outputMem

/--
Main consume-before-quotient theorem.  One source-generated receipt settles
every active nonlive Fourier responsibility.  The carrier branch is generated
internally:

* owned dormant rows already have current tangent `q` and current residual
  zero;
* missing rows have old residual `-q`, are installed at zero, and then have
  actual tangent `q`;
* on the complete carrier every such residual is zero.

The theorem mouth reads only the source and viscosity.
-/
theorem generatedCompleteNonlinearReceipt_consumes_before_quotient
    (source : RawVorticityFourierSource)
    (ν : Viscosity) :
    ∀ output :
        {output : IntegerWavevector //
          output ∈ generatedActiveNonliveNonlinearModes source},
      (completeOmittedPhysicalTimeReceipt source ν).trajectory
          0 output.1 =
        0 ∧
      HasDerivAt
          (fun time =>
            (completeOmittedPhysicalTimeReceipt source ν).trajectory
              time output.1)
          (generatedVorticityNonlinearCoefficientAt
            source output.1)
          0 ∧
      wholeLatticeVorticityFourierPDEResidualAt
          ν.coeff
          (generatedCompleteNonlinearInitialState source)
          (finiteStateVorticityGenerator
            (generatedCompleteNonlinearGalerkinModes source)
            ν.coeff
            (generatedCompleteNonlinearInitialState source))
          output.1 =
        0 ∧
      ((output.1 ∈ generatedSupport source ∧
          finiteStateVorticityGenerator
              (generatedSupport source)
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source))
              output.1 =
            generatedVorticityNonlinearCoefficientAt
              source output.1 ∧
          wholeLatticeVorticityFourierPDEResidualAt
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source))
              (finiteStateVorticityGenerator
                (generatedSupport source)
                ν.coeff
                (generatedComplexVorticityState source
                  (generatedSupport source)))
              output.1 =
            0) ∨
        (output.1 ∉ generatedSupport source ∧
          wholeLatticeVorticityFourierPDEResidualAt
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source))
              (finiteStateVorticityGenerator
                (generatedSupport source)
                ν.coeff
                (generatedComplexVorticityState source
                  (generatedSupport source)))
              output.1 =
            -generatedVorticityNonlinearCoefficientAt
              source output.1 ∧
          wholeLatticeVorticityFourierPDEResidualAt
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source))
              (finiteStateVorticityGenerator
                (generatedSupport source)
                ν.coeff
                (generatedComplexVorticityState source
                  (generatedSupport source)))
              output.1 ≠
            0)) := by
  intro output
  refine
    ⟨completeOmittedPhysicalTimeReceipt_activeNonlive_initial_zero
        source ν output.2,
      completeOmittedPhysicalTimeReceipt_activeNonlive_derivative
        source ν output.2,
      completeGalerkinFullPDEResidual_activeNonlive_eq_zero
        source ν.coeff output.2,
      ?_⟩
  by_cases supportMem : output.1 ∈ generatedSupport source
  · have ownedMem :
        output.1 ∈ generatedOwnedDormantNonlinearModes source :=
      (mem_generatedOwnedDormantNonlinearModes_iff
        source output.1).mpr ⟨output.2, supportMem⟩
    exact Or.inl
      ⟨supportMem,
        currentGalerkinGenerator_ownedDormant
          source ν.coeff ownedMem,
        currentFullPDEResidual_ownedDormant_eq_zero
          source ν.coeff ownedMem⟩
  · have missingMem :
        output.1 ∈ generatedMissingNonlinearModes source :=
      (mem_generatedMissingNonlinearModes_iff
        source output.1).mpr ⟨output.2, supportMem⟩
    exact Or.inr
      ⟨supportMem,
        currentFullPDEResidual_missing_eq_neg_generated
          source ν.coeff missingMem,
        currentFullPDEResidual_missing_ne_zero
          source ν.coeff missingMem⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
end NavierStokes
end SaturationMonoid
