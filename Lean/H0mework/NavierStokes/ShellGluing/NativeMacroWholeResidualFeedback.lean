import H0mework.NavierStokes.ShellGluing.NativeMacroBoundaryTangentGluing

/-!
# Bare-source whole-residual feedback into the native macro runtime

The shell ledger remembers the old generated `q`, but it is not itself the
feedback guard: an old shell row may already be owned by the physical
Galerkin carrier.  The actual obstruction is the whole-lattice PDE residual
of the current physical carrier.  Its source-computed support is exactly
`generatedMissingNonlinearModes`.

This module starts from a bare `UnforcedScaleTimeCurrent`.  The existing
source responder generates exactly one of:

* a genuine infinite old shell lineage; or
* an exact `NativeRedirectedCompleteRoundStep`.

In the macro branch, whole-residual silence is equivalent to an empty
missing-mode inventory.  Otherwise every missing row is a nonzero residual
row and is installed in the next receipt's Galerkin law surface.  The
complete-carrier residual is then zero, the existing whole live/trace carrier
performs its native write, and the physical projection remains the full
positive-time unforced Galerkin receipt.

No lineage, residual, branch, response, target, support, nonzero witness,
trajectory, or physical law is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualFeedback

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedWholeCarrierCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteScaleTimeRoundRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime

noncomputable section

/-! ## Actual residual before and after source-computed support feedback -/

/-- Physical Fourier state carried by one bare redirected current. -/
def currentPhysicalState
    (current : UnforcedScaleTimeCurrent) :
    ComplexVorticityHilbertState :=
  generatedComplexVorticityState current.physicalSource
    (generatedSupport current.physicalSource)

/-- Current-support Galerkin tangent before installing missing responsibility. -/
def ownedCarrierTangent
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    ComplexVorticityHilbertState :=
  finiteStateVorticityGenerator
    (generatedSupport current.physicalSource)
    ν.coeff
    (currentPhysicalState current)

/-- Complete source-computed Galerkin tangent at the unchanged physical state. -/
def completeCarrierTangent
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    ComplexVorticityHilbertState :=
  finiteStateVorticityGenerator
    (generatedCompleteNonlinearGalerkinModes current.physicalSource)
    ν.coeff
    (currentPhysicalState current)

/-- Whole-lattice PDE residual of the old owned carrier. -/
def ownedCarrierWholeResidual
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    IntegerWavevector → ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    (currentPhysicalState current)
    (ownedCarrierTangent ν current)

/-- Whole-lattice PDE residual after the source-computed support installation. -/
def completeCarrierWholeResidual
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    IntegerWavevector → ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    (currentPhysicalState current)
    (completeCarrierTangent ν current)

/--
The next receipt's Galerkin law surface is literally the old support union
the source-computed missing residual support.
-/
theorem redirectedMacroPhysicalSupport_eq_support_union_missing
    (current : UnforcedScaleTimeCurrent) :
    generatedSupport
        (completeOmittedPhysicalLiftSource current.physicalSource) =
      generatedSupport current.physicalSource ∪
        generatedMissingNonlinearModes current.physicalSource := by
  rw [completeOmittedPhysicalLiftSource_generatedSupport]
  rfl

/-- Installing the residual support does not jump the physical state. -/
theorem redirectedMacroPhysicalReceipt_initial_eq_currentPhysicalState
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    (redirectedMacroPhysicalReceipt ν current).trajectory 0 =
      currentPhysicalState current := by
  calc
    (redirectedMacroPhysicalReceipt ν current).trajectory 0 =
        generatedCompleteNonlinearInitialState
          current.physicalSource :=
      completeOmittedPhysicalTimeReceipt_initial
        current.physicalSource ν
    _ = currentPhysicalState current :=
      generatedCompleteNonlinearInitialState_eq_currentPhysicalState
        current.physicalSource

/-- The complete source-computed carrier has zero whole PDE residual. -/
theorem completeCarrierWholeResidual_eq_zero
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    completeCarrierWholeResidual ν current = 0 := by
  have compiled :=
    completeGalerkinWholeLatticePDEResidual_eq_zero
      current.physicalSource ν.coeff
  simpa [completeCarrierWholeResidual, completeCarrierTangent,
    currentPhysicalState,
    generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
    using compiled

/--
Actual residual update on the unchanged physical state.  The complete-carrier
tangent write is uniquely forced by the old and new native Galerkin laws.
-/
theorem ownedResidual_add_nativeTangentWrite_eq_completeResidual
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    ownedCarrierWholeResidual ν current +
        (completeCarrierTangent ν current -
          ownedCarrierTangent ν current) =
      completeCarrierWholeResidual ν current := by
  ext output coordinate
  simp [ownedCarrierWholeResidual, completeCarrierWholeResidual,
    ownedCarrierTangent, completeCarrierTangent,
    wholeLatticeVorticityFourierPDEResidualAt]

/--
Faithful-zero law on the bare physical current: the old whole residual
vanishes exactly when the source-computed missing responsibility support is
empty.
-/
theorem ownedCarrierWholeResidual_eq_zero_iff_missingModes_eq_empty
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    ownedCarrierWholeResidual ν current = 0 ↔
      generatedMissingNonlinearModes current.physicalSource = ∅ := by
  constructor
  · intro residualZero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro output outputMem
    have residualNonzero :=
      currentFullPDEResidual_missing_ne_zero
        current.physicalSource ν.coeff outputMem
    apply residualNonzero
    simpa [ownedCarrierWholeResidual, ownedCarrierTangent,
      currentPhysicalState] using congrFun residualZero output
  · intro missingClosed
    have modesEq :
        generatedCompleteNonlinearGalerkinModes current.physicalSource =
          generatedSupport current.physicalSource := by
      simp [generatedCompleteNonlinearGalerkinModes, missingClosed]
    simpa [ownedCarrierWholeResidual, completeCarrierWholeResidual,
      ownedCarrierTangent, completeCarrierTangent, modesEq] using
      completeCarrierWholeResidual_eq_zero ν current

/--
The bare current itself generates the faithful-zero/nonzero residual
alternative.  Every active row is installed in the exact source of the next
physical receipt; neither row selection nor nonvanishing is a premise.
-/
theorem ownedCarrierWholeResidual_activity
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    (ownedCarrierWholeResidual ν current = 0 ∧
        generatedMissingNonlinearModes current.physicalSource = ∅) ∨
      (ownedCarrierWholeResidual ν current ≠ 0 ∧
        (generatedMissingNonlinearModes
          current.physicalSource).Nonempty ∧
        ∀ output ∈
            generatedMissingNonlinearModes current.physicalSource,
          ownedCarrierWholeResidual ν current output ≠ 0 ∧
            output ∈
              generatedSupport
                (completeOmittedPhysicalLiftSource
                  current.physicalSource)) := by
  by_cases residualZero :
      ownedCarrierWholeResidual ν current = 0
  · exact
      Or.inl
        ⟨residualZero,
          (ownedCarrierWholeResidual_eq_zero_iff_missingModes_eq_empty
            ν current).mp residualZero⟩
  · have missingNe :
        generatedMissingNonlinearModes current.physicalSource ≠ ∅ := by
      intro missingClosed
      exact residualZero
        ((ownedCarrierWholeResidual_eq_zero_iff_missingModes_eq_empty
          ν current).mpr missingClosed)
    refine
      Or.inr
        ⟨residualZero,
          Finset.nonempty_iff_ne_empty.mpr missingNe, ?_⟩
    intro output outputMem
    constructor
    · simpa [ownedCarrierWholeResidual, ownedCarrierTangent,
        currentPhysicalState] using
        currentFullPDEResidual_missing_ne_zero
          current.physicalSource ν.coeff outputMem
    · rw [
        redirectedMacroPhysicalSupport_eq_support_union_missing
          current]
      exact Finset.mem_union_right _ outputMem

/-! ## Bare-current source producer -/

/--
The native responder is now tied directly to the actual whole residual
computed from its bare physical current.

If the old maximal shell process is infinite, that genuine source lineage is
returned.  Otherwise the exact generated macro response carries:

* the source-internal faithful-zero/nonzero residual alternative;
* residual-selected support feedback;
* zero next residual and the exact residual update;
* the existing whole live/trace carrier write; and
* the full positive-time unforced physical law.

The shell ledger remains provenance memory.  It is not used as the PDE
feedback guard.
-/
theorem generatedBareCurrentWholeResidual_nativeFeedback
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    (generatedRedirectedCompleteRoundRespond ν current = none ∧
        Nonempty
          (GeneratedCompleteInfiniteShellAt
            (legacyCurrentReadout current))) ∨
      ∃ response :
          Response (NativeRedirectedCompleteRoundStep ν) current,
        generatedRedirectedCompleteRoundRespond ν current =
            some response ∧
          ((ownedCarrierWholeResidual ν current = 0 ∧
              generatedMissingNonlinearModes
                  current.physicalSource =
                ∅) ∨
            (ownedCarrierWholeResidual ν current ≠ 0 ∧
              (generatedMissingNonlinearModes
                current.physicalSource).Nonempty ∧
              ∀ output ∈
                  generatedMissingNonlinearModes
                    current.physicalSource,
                ownedCarrierWholeResidual ν current output ≠ 0 ∧
                  output ∈
                    generatedSupport
                      (completeOmittedPhysicalLiftSource
                        current.physicalSource))) ∧
          generatedSupport
              (completeOmittedPhysicalLiftSource
                current.physicalSource) =
            generatedSupport current.physicalSource ∪
              generatedMissingNonlinearModes current.physicalSource ∧
          completeCarrierWholeResidual ν current = 0 ∧
          ownedCarrierWholeResidual ν current +
              (completeCarrierTangent ν current -
                ownedCarrierTangent ν current) =
            completeCarrierWholeResidual ν current ∧
          deferredWholeCarrier response.1 -
              deferredWholeCarrier current =
            (response.2.physicalTrace + response.2.shellTrace,
              response.2.shellTrace) ∧
          (let receipt := redirectedMacroPhysicalReceipt ν current;
            receipt.trajectory 0 =
                recollectedPhysicalState current ∧
              (∀ time ∈ Set.Icc (0 : ℝ) receipt.duration,
                HasDerivAt receipt.trajectory
                  (finiteStateVorticityGenerator
                    (generatedSupport
                      (completeOmittedPhysicalLiftSource
                        current.physicalSource))
                    ν.coeff
                    (receipt.trajectory time))
                  time) ∧
              recollectedPhysicalState response.1 =
                receipt.endpoint) := by
  cases generated :
      generatedRedirectedCompleteRoundRespond ν current with
  | none =>
      refine Or.inl ⟨rfl, ?_⟩
      exact
        ⟨generatedCompleteRoundRespond_infiniteShell
          ν (legacyCurrentReadout current)
          (oldResponder_stopped_of_redirected_stopped
            ν current generated)⟩
  | some response =>
      refine Or.inr ⟨response, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ownedCarrierWholeResidual_activity ν current
      · exact
          redirectedMacroPhysicalSupport_eq_support_union_missing
            current
      · exact completeCarrierWholeResidual_eq_zero ν current
      · exact
          ownedResidual_add_nativeTangentWrite_eq_completeResidual
            ν current
      · exact response.2.wholeCarrier_sub
      · exact response.2.physicalProjection_unforced_commutes

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualFeedback
end NavierStokes
end SaturationMonoid
