import H0mework.Realization.Process.NativeOccurrenceFold
import H0mework.NavierStokes.Completion.OmittedPreTimeRuntime

/-!
# Consume every pre-time occurrence before any Fourier quotient

The complete pre-time runtime already generates an exact chronological table
of shell and support writes.  This module consumes each row while its source
occurrence is still available:

* a shell row exposes the old nonzero full-PDE residual, its same-response
  unforced target validation, and the zero residual on the expanded carrier;
* a support row conserves the physical state and compiles the whole finite
  generator to the whole-lattice Navier--Stokes tangent.

No norm is assigned to occurrence provenance.  The chronological table is
used only before aggregation, to prevent equal Fourier frequencies from
merging or cancelling before their separately generated PDE responsibilities
have been discharged.

At a finite maximal terminal, the next authoritative complete response is
the actual positive-time unforced event.  Because the missing-support set is
then empty, that very receipt—not a replacement receipt—has the whole-lattice
tangent as its time-zero derivative and zero whole-carrier PDE residual.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeConsumeBeforeQuotient

open Set
open SourceGeneratedNativeBoundedRun
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellConsumeBeforeQuotient
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedWholeCarrierCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeRuntime

noncomputable section

/-! ## Per-edge PDE consumption -/

/-- Physical responsibility consumed by one old whole-shell source edge. -/
def ShellPDEConsumption
    (source : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep source)
    (ν : Viscosity) : Prop :=
  ∀ output ∈
      generatedOuterNonlinearShellModes source response.2.shellSq,
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedLiveVorticityModes source)
          ν.coeff
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output ≠
      0 ∧
    HasDerivAt
        (fun time =>
          (shellPhysicalTimeReceipt source response ν).trajectory
            time output)
        (-wholeLatticeVorticityFourierPDEResidualAt
          ν.coeff
          (generatedComplexVorticityState source
            (generatedSupport source))
          (finiteStateVorticityGenerator
            (generatedLiveVorticityModes source)
            ν.coeff
            (generatedComplexVorticityState source
              (generatedSupport source)))
          output)
        0 ∧
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedIntegerShellGalerkinInitialState source response)
        (finiteStateVorticityGenerator
          (generatedIntegerShellGalerkinModes source response)
          ν.coeff
          (generatedIntegerShellGalerkinInitialState source response))
        output =
      0

/-- Whole-carrier physical responsibility consumed by a support event. -/
def SupportPDEConsumption
    (source : RawVorticityFourierSource)
    (ν : Viscosity) : Prop :=
  generatedCompleteNonlinearInitialState source =
      generatedComplexVorticityState source
        (generatedSupport source) ∧
    finiteStateVorticityGenerator
        (generatedCompleteNonlinearGalerkinModes source)
        ν.coeff
        (generatedCompleteNonlinearInitialState source) =
      wholeLatticeVorticityFourierTangentAt
        ν.coeff
        (generatedCompleteNonlinearInitialState source) ∧
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedCompleteNonlinearInitialState source)
        (finiteStateVorticityGenerator
          (generatedCompleteNonlinearGalerkinModes source)
          ν.coeff
          (generatedCompleteNonlinearInitialState source)) =
      0 ∧
    ∀ output : IntegerWavevector,
      HasDerivAt
          (fun time =>
            (completeOmittedPhysicalTimeReceipt source ν).trajectory
              time output)
          (wholeLatticeVorticityFourierTangentAt
            ν.coeff
            (generatedCompleteNonlinearInitialState source)
            output)
          0

/--
The PDE obligation carried by a structural edge, before chronological
receipts are projected to common Fourier coefficients.
-/
def PreTimeStepPDEConsumption
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : PreTimeStep ν current next) : Prop :=
  match step with
  | .shell response _generated =>
      ShellPDEConsumption current.source response ν
  | .support _outerStopped _missingNonempty =>
      SupportPDEConsumption current.source ν

theorem shellPDEConsumption
    (source : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep source)
    (ν : Viscosity) :
    ShellPDEConsumption source response ν := by
  intro output outputMem
  exact
    ⟨liveGalerkin_fullPDEResidual_ne_zero
        source ν.coeff response.2.shellSq outputMem,
      shellPhysicalTimeReceipt_derivative_eq_neg_livePDEResidual
        source response ν outputMem,
      expandedGalerkin_fullPDEResidual_eq_zero
        source response ν.coeff outputMem⟩

theorem supportPDEConsumption
    (source : RawVorticityFourierSource)
    (ν : Viscosity) :
    SupportPDEConsumption source ν :=
  generatedCompleteOmittedWholeCarrierCompiler_checkpoint source ν

/-- Every generated structural edge settles its own PDE responsibility. -/
theorem preTimeStep_pdeConsumption
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : PreTimeStep ν current next) :
    PreTimeStepPDEConsumption step := by
  cases step with
  | shell response generated =>
      exact shellPDEConsumption current.source response ν
  | support outerStopped missingNonempty =>
      exact supportPDEConsumption current.source ν

/-! ## Arbitrary finite path, before quotient -/

/--
One exact occurrence of the pre-time runtime is literally the same response
and target in the authoritative complete scale/time graph.
-/
theorem actualOccurrence_fullResponse
    {ν : Viscosity}
    (occurrence :
      SourceGeneratedNativeBoundedRun.BoundedRun.ActualOccurrence
        (generatedPreTimeRespond ν)) :
    generatedCompleteScaleTimeRespond ν occurrence.current =
      ⟨occurrence.next, occurrence.transition.edge.fullStep⟩ := by
  exact
    generatedPreTimeRespond_some_fullResponse
      ν occurrence.current
      ⟨occurrence.next, occurrence.transition.edge⟩
      occurrence.transition.generated

/--
Every occurrence of an arbitrary generated finite pre-time path is first
identified with the authoritative full response and then consumed on its
own PDE carrier.  Membership in the chronological table supplies ordering;
it is not turned into a metric or energy.
-/
theorem generatedPreTimeReachable_consumes_each_PDEResponsibility_before_quotient
    {ν : Viscosity}
    {seed current : ScaleTimeCurrent}
    (arrival : GeneratedPreTimeReachable ν seed current) :
    ∀ occurrence ∈ arrival.actualOccurrenceTable,
      generatedCompleteScaleTimeRespond ν occurrence.current =
          ⟨occurrence.next, occurrence.transition.edge.fullStep⟩ ∧
        PreTimeStepPDEConsumption occurrence.transition.edge := by
  intro occurrence _occurrenceMem
  exact
    ⟨actualOccurrence_fullResponse occurrence,
      preTimeStep_pdeConsumption occurrence.transition.edge⟩

/-! ## The finite terminal's actual physical-time consumer -/

theorem completeModes_eq_support_of_missingClosed
    (source : RawVorticityFourierSource)
    (missingClosed :
      generatedMissingNonlinearModes source = ∅) :
    generatedCompleteNonlinearGalerkinModes source =
      generatedSupport source := by
  rw [generatedCompleteNonlinearGalerkinModes, missingClosed,
    Finset.union_empty]

/--
When the structural runtime is closed, the authoritative finite-support
generator already equals the whole-lattice tangent, so its full PDE residual
vanishes on the whole Fourier carrier.
-/
theorem generatedTimeAdvancePDEResidual_eq_zero_of_missingClosed
    (source : RawVorticityFourierSource)
    (ν : Viscosity)
    (missingClosed :
      generatedMissingNonlinearModes source = ∅) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedSupport source)
          ν.coeff
          (generatedComplexVorticityState source
            (generatedSupport source))) =
      0 := by
  have compiled :=
    completeGalerkinWholeLatticePDEResidual_eq_zero
      source ν.coeff
  rw [completeModes_eq_support_of_missingClosed
      source missingClosed,
    generatedCompleteNonlinearInitialState_eq_currentPhysicalState] at compiled
  exact compiled

/--
The actual time receipt selected by the authoritative responder—not an
auxiliary complete-lift receipt—differentiates by the whole-lattice tangent
once the generated missing-support set is closed.
-/
theorem generatedTimeAdvanceReceipt_wholeLatticeDerivative_of_missingClosed
    (source : RawVorticityFourierSource)
    (ν : Viscosity)
    (missingClosed :
      generatedMissingNonlinearModes source = ∅)
    (output : IntegerWavevector) :
    HasDerivAt
        (fun time =>
          (generatedTimeAdvanceReceipt source ν.coeff).trajectory
            time output)
        (wholeLatticeVorticityFourierTangentAt
          ν.coeff
          (generatedComplexVorticityState source
            (generatedSupport source))
          output)
        0 := by
  let receipt := generatedTimeAdvanceReceipt source ν.coeff
  have zeroInTime :
      (0 : ℝ) ∈ Icc (0 : ℝ) receipt.duration :=
    ⟨le_rfl, receipt.duration_pos.le⟩
  have actualLaw := (receipt.physical 0 zeroInTime).1
  have rowLaw :=
    complexVorticityTrajectoryWave_hasDerivAt
      receipt.trajectory 0
      (finiteStateVorticityGenerator
        (generatedSupport source)
        ν.coeff
        (receipt.trajectory 0))
      output actualLaw
  rw [show receipt.trajectory 0 =
        generatedComplexVorticityState source
          (generatedSupport source) by
      exact receipt.initial] at rowLaw
  have compiler :=
    completeGalerkinGenerator_eq_wholeLatticeTangent
      source ν.coeff
  rw [completeModes_eq_support_of_missingClosed
      source missingClosed,
    generatedCompleteNonlinearInitialState_eq_currentPhysicalState] at compiler
  rw [congrFun compiler output] at rowLaw
  exact rowLaw

namespace GeneratedPreTimeTerminalRun

/--
The finite maximal path ends at the actual complete-responder time event;
that same receipt owns the whole-lattice time-zero tangent and zero PDE
residual.  The terminal, branch, and support closure are generated by the
runtime itself.
-/
theorem actualTime_consumes_wholeCarrier
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedPreTimeTerminalRun ν seed) :
    generatedCompleteScaleTimeRespond ν run.terminal =
        ⟨timeTarget ν run.terminal,
          ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse.NativeStep.time
            run.outerStopped run.missingClosed⟩ ∧
      wholeLatticeVorticityFourierPDEResidualAt
          ν.coeff
          (generatedComplexVorticityState run.terminal.source
            (generatedSupport run.terminal.source))
          (finiteStateVorticityGenerator
            (generatedSupport run.terminal.source)
            ν.coeff
            (generatedComplexVorticityState run.terminal.source
              (generatedSupport run.terminal.source))) =
        0 ∧
      ∀ output : IntegerWavevector,
        HasDerivAt
            (fun time =>
              (generatedTimeAdvanceReceipt
                run.terminal.source ν.coeff).trajectory
                time output)
            (wholeLatticeVorticityFourierTangentAt
              ν.coeff
              (generatedComplexVorticityState run.terminal.source
                (generatedSupport run.terminal.source))
              output)
            0 := by
  exact
    ⟨run.fullTimeResponse,
      generatedTimeAdvancePDEResidual_eq_zero_of_missingClosed
        run.terminal.source ν run.missingClosed,
      generatedTimeAdvanceReceipt_wholeLatticeDerivative_of_missingClosed
        run.terminal.source ν run.missingClosed⟩

end GeneratedPreTimeTerminalRun

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeConsumeBeforeQuotient
end NavierStokes
end SaturationMonoid
