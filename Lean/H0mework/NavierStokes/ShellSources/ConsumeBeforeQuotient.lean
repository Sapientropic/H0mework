import H0mework.NavierStokes.Fourier.GeneratedUnforcedScaleTimeReceipt
import H0mework.NavierStokes.Fourier.PuncturedCanonicalGalerkinTarget

/-!
# Consume an old-q occurrence before the coefficient quotient

A generated shell receipt is not assigned an auxiliary occurrence norm.
Instead, its complete nonlinear row is read on the physical quantity which
already owns it.

For the current source, take the sharp Galerkin carrier consisting of its
actually live Fourier rows.  Every selected outer row is absent from that
carrier, and its full-lattice Navier--Stokes residual is exactly the negative
old-`q` row.  The same source response then selects the enlarged zero-filled
carrier.  On that carrier:

* the selected full-PDE residual is exactly zero;
* the canonical positive-time unforced receipt has time-zero derivative
  equal to the negative old residual.

Thus the actual source obstruction is consumed before any chronological
receipt list is summed or any coefficient projection can merge provenance.
The old shell update remains the authoritative source write.  The unforced
receipt is its target consumer, not a replacement source scheduler and not a
literal physical interpretation of the shell microstep.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellConsumeBeforeQuotient

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget

noncomputable section

/-! ## The current live carrier and its exact omitted residual -/

/--
The complete generated physical state is sharply supported on the genuinely
live rows.  Dormant entries of the raw support carry zero coefficients and
therefore do not enlarge the physical carrier.
-/
theorem generatedState_supported_on_liveModes
    (source : RawVorticityFourierSource) :
    ∀ wave : IntegerWavevector,
      wave ∉ generatedLiveVorticityModes source →
        generatedComplexVorticityState source
            (generatedSupport source) wave =
          0 := by
  intro wave waveNotLive
  rw [generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport source
  · rw [if_pos waveMem]
    by_contra coefficientNonzero
    exact
      waveNotLive
        ((mem_generatedLiveVorticityModes_iff source wave).mpr
          ⟨waveMem, coefficientNonzero⟩)
  · rw [if_neg waveMem]

/--
The genuine whole-lattice nonlinear row of a generated finite source is the
already generated complete pair aggregation.
-/
theorem wholeStateNonlinearCoefficient_generatedSource
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt
        (generatedComplexVorticityState source
          (generatedSupport source))
        output =
      generatedVorticityNonlinearCoefficientAt source output := by
  rw [
    wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      (generatedSupport source)
      (generatedComplexVorticityState source
        (generatedSupport source))
      (fun wave waveNotMem => by
        rw [generatedComplexVorticityState_apply, if_neg waveNotMem])
      output]
  exact
    finiteStateVorticityNonlinearCoefficientAt_generatedSource
      source output

/-- A selected outer row is absent from the current genuinely live carrier. -/
theorem outerShell_not_mem_liveModes
    (source : RawVorticityFourierSource)
    (shellSq : ℤ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedOuterNonlinearShellModes source shellSq) :
    output ∉ generatedLiveVorticityModes source := by
  have activeMem :
      output ∈ generatedActiveOuterNonlinearModes source :=
    ((mem_generatedOuterNonlinearShellModes_iff
      source shellSq output).mp outputMem).1
  unfold generatedActiveOuterNonlinearModes at activeMem
  split at activeMem
  · simp at activeMem
  · exact (Finset.mem_filter.mp activeMem).2.2.1

/--
Before support expansion, one selected old-`q` row is exactly the negative
full-lattice PDE residual of the current live Galerkin tangent.
-/
theorem liveGalerkin_fullPDEResidual_eq_neg_generatedOutput
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    (shellSq : ℤ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedOuterNonlinearShellModes source shellSq) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedLiveVorticityModes source)
          ν
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output =
      -generatedVorticityNonlinearCoefficientAt source output := by
  have outputNotLive :
      output ∉ generatedLiveVorticityModes source :=
    outerShell_not_mem_liveModes source shellSq outputMem
  have stateZero :
      generatedComplexVorticityState source
          (generatedSupport source) output =
        0 :=
    generatedState_supported_on_liveModes source output outputNotLive
  rw [
    wholeLatticeVorticityFourierPDEResidualAt,
    finiteStateVorticityGenerator_apply,
    if_neg outputNotLive,
    wholeLatticeVorticityFourierTangentAt,
    wholeStateNonlinearCoefficient_generatedSource,
    stateZero]
  simp

/--
The live-carrier PDE residual selected by a successful source response is
genuinely nonzero.  Nonzero is generated by the old source row, not supplied
to the target consumer.
-/
theorem liveGalerkin_fullPDEResidual_ne_zero
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    (shellSq : ℤ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedOuterNonlinearShellModes source shellSq) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedComplexVorticityState source
          (generatedSupport source))
        (finiteStateVorticityGenerator
          (generatedLiveVorticityModes source)
          ν
          (generatedComplexVorticityState source
            (generatedSupport source)))
        output ≠
      0 := by
  rw [
    liveGalerkin_fullPDEResidual_eq_neg_generatedOutput
      source ν shellSq outputMem]
  exact
    neg_ne_zero.mpr
      (generatedVorticityNonlinearCoefficientAt_ne_zero_of_mem_outerShell
        source shellSq outputMem)

/-! ## Same-response expansion and actual unforced consumption -/

/-- The zero-filled expanded state is sharply supported on its exact carrier. -/
theorem generatedIntegerShellGalerkinInitialState_supported
    (source : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep source) :
    ∀ wave : IntegerWavevector,
      wave ∉ generatedIntegerShellGalerkinModes source response →
        generatedIntegerShellGalerkinInitialState
            source response wave =
          0 := by
  intro wave waveNotMem
  rw [generatedIntegerShellGalerkinInitialState_apply, if_neg waveNotMem]

/--
After the same response enlarges the zero-filled Galerkin carrier, the
selected full-lattice PDE residual is exactly zero at time zero.
-/
theorem expandedGalerkin_fullPDEResidual_eq_zero
    (source : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep source)
    (ν : ℝ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈
        generatedOuterNonlinearShellModes
          source response.2.shellSq) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν
        (generatedIntegerShellGalerkinInitialState source response)
        (finiteStateVorticityGenerator
          (generatedIntegerShellGalerkinModes source response)
          ν
          (generatedIntegerShellGalerkinInitialState source response))
        output =
      0 := by
  have outputGalerkinMem :
      output ∈ generatedIntegerShellGalerkinModes source response :=
    generatedOuterNonlinearShellModes_subset_galerkinModes
      source response outputMem
  rw [
    wholeLatticeVorticityFourierPDEResidualAt,
    finiteModes_generator_eq_wholeTangent_sub_omittedDefect
      (generatedIntegerShellGalerkinModes source response)
      ν
      (generatedIntegerShellGalerkinInitialState source response)
      (generatedIntegerShellGalerkinInitialState_supported source response)
      output]
  simp [finiteModesOmittedNonlinearDefectAt, outputGalerkinMem]

/--
The actual positive-time unforced receipt generated by the same source
response consumes the old omitted residual as its exact time-zero derivative.
Both sides are Fourier tangent rows; no state increment is identified with
the old `q`.
-/
theorem shellPhysicalTimeReceipt_derivative_eq_neg_livePDEResidual
    (source : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep source)
    (ν : Viscosity)
    {output : IntegerWavevector}
    (outputMem :
      output ∈
        generatedOuterNonlinearShellModes
          source response.2.shellSq) :
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
        0 := by
  rw [
    liveGalerkin_fullPDEResidual_eq_neg_generatedOutput
      source ν.coeff response.2.shellSq outputMem,
    neg_neg]
  exact
    shellPhysicalTimeReceipt_selectedOutput_derivative
      source response ν outputMem

/-! ## Arbitrary source path: every occurrence is consumed before quotient -/

/--
Every old-`q` occurrence of an arbitrary source-generated finite path is
settled before chronological traces are added:

1. its current live Galerkin carrier has a nonzero full-PDE residual;
2. the same response's actual unforced receipt differentiates by the
   negative of that residual;
3. the response-selected expanded carrier has zero residual on that row.

The path, receipt, response, output shell, nonzero witness, expanded carrier,
and physical trajectory are all source-generated.
-/
theorem generatedIntegerShellReachable_consumes_each_PDEResidual_before_quotient
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity) :
    ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
      ∀ output ∈ receipt.wholeShellModes,
        wholeLatticeVorticityFourierPDEResidualAt
            ν.coeff
            (generatedComplexVorticityState receipt.current
              (generatedSupport receipt.current))
            (finiteStateVorticityGenerator
              (generatedLiveVorticityModes receipt.current)
              ν.coeff
              (generatedComplexVorticityState receipt.current
                (generatedSupport receipt.current)))
            output ≠
          0 ∧
        HasDerivAt
            (fun time =>
              (shellPhysicalTimeReceipt
                receipt.current receipt.response ν).trajectory
                time output)
            (-wholeLatticeVorticityFourierPDEResidualAt
              ν.coeff
              (generatedComplexVorticityState receipt.current
                (generatedSupport receipt.current))
              (finiteStateVorticityGenerator
                (generatedLiveVorticityModes receipt.current)
                ν.coeff
                (generatedComplexVorticityState receipt.current
                  (generatedSupport receipt.current)))
              output)
            0 ∧
        wholeLatticeVorticityFourierPDEResidualAt
            ν.coeff
            (generatedIntegerShellGalerkinInitialState
              receipt.current receipt.response)
            (finiteStateVorticityGenerator
              (generatedIntegerShellGalerkinModes
                receipt.current receipt.response)
              ν.coeff
              (generatedIntegerShellGalerkinInitialState
                receipt.current receipt.response))
            output =
          0 := by
  intro receipt receiptMem output outputMem
  exact
    ⟨liveGalerkin_fullPDEResidual_ne_zero
        receipt.current ν.coeff receipt.selectedShellSq outputMem,
      shellPhysicalTimeReceipt_derivative_eq_neg_livePDEResidual
        receipt.current receipt.response ν outputMem,
      expandedGalerkin_fullPDEResidual_eq_zero
        receipt.current receipt.response ν.coeff outputMem⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellConsumeBeforeQuotient
end NavierStokes
end SaturationMonoid
