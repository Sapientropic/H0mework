import H0mework.NavierStokes.ShellGluing.NativeMacroFirstShellPDEBridge
import H0mework.NavierStokes.Completion.OmittedWholeCarrierCompiler

/-!
# Boundary tangent gluing of adjacent redirected macro receipts

Adjacent redirected physical receipts have the same endpoint state, but the
complete source-owned Galerkin carrier may expand at that boundary.  State
continuity alone therefore does not identify their two one-sided tangents.

This module computes the exact critical-pair defect on the common physical
state:

```text
right complete-carrier tangent - left old-carrier tangent
  = - whole-lattice PDE residual of the left tangent.
```

The right tangent is the whole-lattice unforced tangent by the existing
complete carrier compiler.  Thus a nonzero boundary defect is neither an
impulse nor an external force: it is precisely the old carrier's omitted
unforced responsibility, and the next source-owned macro installs the
carrier on which that residual vanishes.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroBoundaryTangentGluing

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedWholeCarrierCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroFirstShellPDEBridge

noncomputable section

/-! ## The two actual one-sided tangents -/

/-- Left derivative at the endpoint of one actual unforced macro receipt. -/
def boundaryLeftTangent
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ComplexVorticityHilbertState :=
  finiteStateVorticityGenerator
    (generatedSupport
      (completeOmittedPhysicalLiftSource
        (lineage.current index).physicalSource))
    ν.coeff
    (lineage.physicalReceipt index).endpoint

/--
Right derivative at time zero of the next actual unforced macro receipt.
The next source itself computes the complete carrier.
-/
def boundaryRightTangent
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ComplexVorticityHilbertState :=
  finiteStateVorticityGenerator
    (generatedSupport
      (completeOmittedPhysicalLiftSource
        (lineage.current (index + 1)).physicalSource))
    ν.coeff
    ((lineage.physicalReceipt (index + 1)).trajectory 0)

/-- Whole-lattice residual of continuing with the left carrier at the common
boundary state. -/
def boundaryLeftWholeResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    ((lineage.physicalReceipt (index + 1)).trajectory 0)
    (boundaryLeftTangent lineage index)

/--
Whole-lattice residual after the next native macro has installed the complete
source-owned carrier, at the same common boundary state.
-/
def boundaryRightWholeResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    ((lineage.physicalReceipt (index + 1)).trajectory 0)
    (boundaryRightTangent lineage index)

/-! ## Exact common-state and support seam -/

theorem boundary_nextSource_support_eq_leftModes
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    generatedSupport
        (lineage.current (index + 1)).physicalSource =
      generatedSupport
        (completeOmittedPhysicalLiftSource
          (lineage.current index).physicalSource) := by
  rw [(lineage.step index).physicalSource_next]
  exact (lineage.physicalReceipt index).nextSource_generatedSupport

theorem boundary_nextSource_state_eq_leftEndpoint
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    generatedComplexVorticityState
          (lineage.current (index + 1)).physicalSource
          (generatedSupport
            (lineage.current (index + 1)).physicalSource) =
      (lineage.physicalReceipt index).endpoint := by
  rw [(lineage.step index).physicalSource_next]
  exact (lineage.physicalReceipt index).nextSource_generatedState

/-- Both displayed tangents are the actual one-sided derivatives of the two
adjacent receipt charts. -/
theorem boundary_actual_oneSidedDerivatives
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    HasDerivAt
        (lineage.physicalReceipt index).trajectory
        (boundaryLeftTangent lineage index)
        (lineage.physicalReceipt index).duration ∧
      HasDerivAt
        (lineage.physicalReceipt (index + 1)).trajectory
        (boundaryRightTangent lineage index)
        0 := by
  constructor
  · exact (lineage.physicalReceipt index).endpoint_physical.1
  · have zeroMem :
        (0 : ℝ) ∈
          Icc (0 : ℝ)
            (lineage.physicalReceipt (index + 1)).duration :=
      ⟨le_rfl,
        (lineage.physicalReceipt (index + 1)).duration_pos.le⟩
    exact
      ((lineage.physicalReceipt (index + 1)).physical
        0 zeroMem).1

/-! ## Critical-pair residual identity -/

/--
The next complete carrier's initial tangent is the whole-lattice unforced
tangent on the common boundary state.
-/
theorem boundaryRightTangent_eq_wholeLatticeTangent
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    boundaryRightTangent lineage index =
      wholeLatticeVorticityFourierTangentAt
        ν.coeff
        ((lineage.physicalReceipt (index + 1)).trajectory 0) := by
  have compiler :=
    completeGalerkinGenerator_eq_wholeLatticeTangent
      (lineage.current (index + 1)).physicalSource
      ν.coeff
  have initial :
      (lineage.physicalReceipt (index + 1)).trajectory 0 =
        generatedCompleteNonlinearInitialState
          (lineage.current (index + 1)).physicalSource :=
    completeOmittedPhysicalTimeReceipt_initial
      (lineage.current (index + 1)).physicalSource ν
  rw [boundaryRightTangent,
    completeOmittedPhysicalLiftSource_generatedSupport,
    initial]
  exact compiler

/--
The next macro's complete carrier closes the whole-lattice residual at the
common boundary state.  This is a whole-carrier equality, not a selected-row
readout.
-/
theorem boundaryRightWholeResidual_eq_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    boundaryRightWholeResidual lineage index = 0 := by
  apply funext
  intro output
  change
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        ((lineage.physicalReceipt (index + 1)).trajectory 0)
        (boundaryRightTangent lineage index) output =
      0
  rw [wholeLatticeVorticityFourierPDEResidualAt]
  rw [congrFun
    (boundaryRightTangent_eq_wholeLatticeTangent lineage index) output]
  simp

/--
Exact tangent gluing defect.  The right macro does not add a forcing term:
it replaces the old projected tangent by the whole-lattice tangent, and the
difference is exactly the negative old residual.
-/
theorem boundaryTangentJump_eq_neg_leftWholeResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    boundaryRightTangent lineage index output -
        boundaryLeftTangent lineage index output =
      -boundaryLeftWholeResidual lineage index output := by
  have rightEq :=
    congrFun
      (boundaryRightTangent_eq_wholeLatticeTangent
        lineage index)
      output
  rw [rightEq]
  simp [boundaryLeftWholeResidual,
    wholeLatticeVorticityFourierPDEResidualAt]

/--
Native whole-carrier residual update at one actual macro boundary:

```text
old residual + generated tangent write = next residual = 0.
```

The tangent write is fixed by the two actual one-sided derivatives.  It is
not supplied as a forcing term or a settlement certificate.
-/
theorem boundaryWholeResidual_add_nativeTangentWrite_eq_nextResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    boundaryLeftWholeResidual lineage index +
        (boundaryRightTangent lineage index -
          boundaryLeftTangent lineage index) =
      boundaryRightWholeResidual lineage index := by
  ext output
  rw [Pi.add_apply, Pi.sub_apply,
    boundaryTangentJump_eq_neg_leftWholeResidual,
    congrFun (boundaryRightWholeResidual_eq_zero lineage index) output]
  simp

/-! ## Exact current-carrier identification -/

/-- The left endpoint tangent is exactly the current-support Galerkin
generator of the recompiled boundary source. -/
theorem boundaryLeftTangent_eq_boundarySourceGenerator
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    boundaryLeftTangent lineage index =
      finiteStateVorticityGenerator
        (generatedSupport
          (lineage.current (index + 1)).physicalSource)
        ν.coeff
        (generatedComplexVorticityState
          (lineage.current (index + 1)).physicalSource
          (generatedSupport
            (lineage.current (index + 1)).physicalSource)) := by
  rw [boundaryLeftTangent]
  have supportEq :=
    boundary_nextSource_support_eq_leftModes lineage index
  have stateEq :=
    boundary_nextSource_state_eq_leftEndpoint lineage index
  calc
    finiteStateVorticityGenerator
          (generatedSupport
            (completeOmittedPhysicalLiftSource
              (lineage.current index).physicalSource))
          ν.coeff
          (lineage.physicalReceipt index).endpoint =
        finiteStateVorticityGenerator
          (generatedSupport
            (lineage.current (index + 1)).physicalSource)
          ν.coeff
          (lineage.physicalReceipt index).endpoint := by
            rw [supportEq]
    _ =
        finiteStateVorticityGenerator
          (generatedSupport
            (lineage.current (index + 1)).physicalSource)
          ν.coeff
          (generatedComplexVorticityState
            (lineage.current (index + 1)).physicalSource
            (generatedSupport
              (lineage.current (index + 1)).physicalSource)) := by
            rw [stateEq]

/-- Residual form of the same exact common-boundary identification. -/
theorem boundaryLeftWholeResidual_eq_boundarySourceResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    boundaryLeftWholeResidual lineage index output =
      wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedComplexVorticityState
          (lineage.current (index + 1)).physicalSource
          (generatedSupport
            (lineage.current (index + 1)).physicalSource))
        (finiteStateVorticityGenerator
          (generatedSupport
            (lineage.current (index + 1)).physicalSource)
          ν.coeff
          (generatedComplexVorticityState
            (lineage.current (index + 1)).physicalSource
            (generatedSupport
              (lineage.current (index + 1)).physicalSource)))
        output := by
  have initial :
      (lineage.physicalReceipt (index + 1)).trajectory 0 =
        generatedCompleteNonlinearInitialState
          (lineage.current (index + 1)).physicalSource :=
    completeOmittedPhysicalTimeReceipt_initial
      (lineage.current (index + 1)).physicalSource ν
  have physicalState :
      generatedCompleteNonlinearInitialState
          (lineage.current (index + 1)).physicalSource =
        generatedComplexVorticityState
          (lineage.current (index + 1)).physicalSource
          (generatedSupport
            (lineage.current (index + 1)).physicalSource) :=
    generatedCompleteNonlinearInitialState_eq_currentPhysicalState
      (lineage.current (index + 1)).physicalSource
  rw [boundaryLeftWholeResidual, initial, physicalState,
    boundaryLeftTangent_eq_boundarySourceGenerator]

/-! ## Faithful residual-selected support feedback -/

/--
On the old physical carrier, whole-lattice residual silence is equivalent to
closure of the source-computed missing-mode inventory.  Thus the next support
write does not rely on an externally supplied faithfulness or coverage
certificate.
-/
theorem boundaryLeftWholeResidual_eq_zero_iff_missingModes_eq_empty
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    boundaryLeftWholeResidual lineage index = 0 ↔
      generatedMissingNonlinearModes
          (lineage.current (index + 1)).physicalSource =
        ∅ := by
  let source :=
    (lineage.current (index + 1)).physicalSource
  constructor
  · intro residualZero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro output outputMem
    have residualNonzero :=
      currentFullPDEResidual_missing_ne_zero
        source ν.coeff outputMem
    apply residualNonzero
    calc
      wholeLatticeVorticityFourierPDEResidualAt
            ν.coeff
            (generatedComplexVorticityState source
              (generatedSupport source))
            (finiteStateVorticityGenerator
              (generatedSupport source)
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source)))
            output =
          boundaryLeftWholeResidual lineage index output :=
        (boundaryLeftWholeResidual_eq_boundarySourceResidual
          lineage index output).symm
      _ = 0 := by
        simpa using congrFun residualZero output
  · intro missingClosed
    change
      generatedMissingNonlinearModes source = ∅
      at missingClosed
    have modesEq :
        generatedCompleteNonlinearGalerkinModes source =
          generatedSupport source := by
      simp [generatedCompleteNonlinearGalerkinModes, missingClosed]
    have compiled :=
      completeGalerkinWholeLatticePDEResidual_eq_zero
        source ν.coeff
    rw [modesEq,
      generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
      at compiled
    apply funext
    intro output
    calc
      boundaryLeftWholeResidual lineage index output =
          wholeLatticeVorticityFourierPDEResidualAt
            ν.coeff
            (generatedComplexVorticityState source
              (generatedSupport source))
            (finiteStateVorticityGenerator
              (generatedSupport source)
              ν.coeff
              (generatedComplexVorticityState source
                (generatedSupport source)))
            output :=
        boundaryLeftWholeResidual_eq_boundarySourceResidual
          lineage index output
      _ = 0 := by
        simpa using congrFun compiled output

/--
Every genuinely missing residual row is installed in the exact source of the
next actual unforced receipt.  This is the law-surface feedback by which the
obstruction changes the next native macro; the coefficient itself is not
inserted into the physical state.
-/
theorem boundaryMissingMode_mem_nextNativeReceiptSupport
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈
        generatedMissingNonlinearModes
          (lineage.current (index + 1)).physicalSource) :
    output ∈
      generatedSupport
        (completeOmittedPhysicalLiftSource
          (lineage.current (index + 1)).physicalSource) := by
  rw [completeOmittedPhysicalLiftSource_generatedSupport]
  exact
    generatedMissingNonlinearModes_subset_completeGalerkinModes
      (lineage.current (index + 1)).physicalSource outputMem

/--
Source-owned recursive residual redirect on one actual macro boundary.

The source itself exhausts the only two legal outcomes:

* faithful whole-carrier silence, equivalently no missing nonlinear row; or
* a nonzero whole residual with a concrete missing row.  That row is written
  into the next macro's Galerkin law surface, the next boundary residual is
  zero, the whole live/trace carrier performs its existing native update, and
  the physical projection is the full positive-time unforced receipt.

No residual, missing row, branch, response, target, support, nonzero witness,
trajectory, or physical law is supplied by the caller.
-/
theorem generatedBoundaryWholeResidual_nativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (boundaryLeftWholeResidual lineage index = 0 ∧
        generatedMissingNonlinearModes
            (lineage.current (index + 1)).physicalSource =
          ∅) ∨
      (boundaryLeftWholeResidual lineage index ≠ 0 ∧
        (generatedMissingNonlinearModes
          (lineage.current (index + 1)).physicalSource).Nonempty ∧
        (∀ output ∈
            generatedMissingNonlinearModes
              (lineage.current (index + 1)).physicalSource,
          boundaryLeftWholeResidual lineage index output ≠ 0 ∧
            output ∈
              generatedSupport
                (completeOmittedPhysicalLiftSource
                  (lineage.current (index + 1)).physicalSource)) ∧
        boundaryRightWholeResidual lineage index = 0 ∧
        boundaryLeftWholeResidual lineage index +
            (boundaryRightTangent lineage index -
              boundaryLeftTangent lineage index) =
          boundaryRightWholeResidual lineage index ∧
        generatedRedirectedCompleteRoundRespond
            ν (lineage.current (index + 1)) =
          some
            ⟨lineage.current (index + 2),
              lineage.step (index + 1)⟩ ∧
        deferredWholeCarrier (lineage.current (index + 2)) -
            deferredWholeCarrier (lineage.current (index + 1)) =
          ((lineage.step (index + 1)).physicalTrace +
              (lineage.step (index + 1)).shellTrace,
            (lineage.step (index + 1)).shellTrace) ∧
        (let receipt := lineage.physicalReceipt (index + 1);
          receipt.trajectory 0 =
              recollectedPhysicalState
                (lineage.current (index + 1)) ∧
            (∀ time ∈ Set.Icc (0 : ℝ) receipt.duration,
              HasDerivAt receipt.trajectory
                (finiteStateVorticityGenerator
                  (generatedSupport
                    (completeOmittedPhysicalLiftSource
                      (lineage.current
                        (index + 1)).physicalSource))
                  ν.coeff
                  (receipt.trajectory time))
                time) ∧
            recollectedPhysicalState
                (lineage.current (index + 2)) =
              receipt.endpoint)) := by
  by_cases residualZero :
      boundaryLeftWholeResidual lineage index = 0
  · exact
      Or.inl
        ⟨residualZero,
          (boundaryLeftWholeResidual_eq_zero_iff_missingModes_eq_empty
            lineage index).mp residualZero⟩
  · have missingNe :
        generatedMissingNonlinearModes
            (lineage.current (index + 1)).physicalSource ≠
          ∅ := by
      intro missingClosed
      exact residualZero
        ((boundaryLeftWholeResidual_eq_zero_iff_missingModes_eq_empty
          lineage index).mpr missingClosed)
    have eachMissing :
        ∀ output ∈
            generatedMissingNonlinearModes
              (lineage.current (index + 1)).physicalSource,
          boundaryLeftWholeResidual lineage index output ≠ 0 ∧
            output ∈
              generatedSupport
                (completeOmittedPhysicalLiftSource
                  (lineage.current (index + 1)).physicalSource) := by
      intro output outputMem
      constructor
      · rw [
          boundaryLeftWholeResidual_eq_boundarySourceResidual
            lineage index output]
        exact
          currentFullPDEResidual_missing_ne_zero
            (lineage.current (index + 1)).physicalSource
            ν.coeff outputMem
      · exact
          boundaryMissingMode_mem_nextNativeReceiptSupport
            lineage index outputMem
    have physical :=
      (lineage.step
        (index + 1)).physicalProjection_unforced_commutes
    refine
      Or.inr
        ⟨residualZero,
          Finset.nonempty_iff_ne_empty.mpr missingNe,
          eachMissing,
          boundaryRightWholeResidual_eq_zero lineage index,
          boundaryWholeResidual_add_nativeTangentWrite_eq_nextResidual
            lineage index,
          lineage.generated (index + 1),
          lineage.wholeCarrier_succ_sub (index + 1),
          ?_⟩
    simpa [
      GeneratedRedirectedCompleteRoundInfiniteLineage.physicalReceipt]
      using physical

/-! ## First-shell ownership versus genuine carrier expansion -/

/--
At every adjacent macro boundary, the next first-shell source event decides
the full tangent-gluing alternative without caller input.

For each active first-shell row the right derivative is always the old
source-generated `q`.  If the coordinate is already dormant-owned, the left
derivative is also `q` and no tangent jump occurs.  If it is genuinely
missing, the left derivative is zero, its whole-lattice residual is `-q`,
and the next complete macro produces the exact nonzero jump `q`.
-/
theorem generatedAdjacentBoundaryFirstShellTangentGluing
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (lineage.step (index + 1)).shellTrace = 0 ∨
      ((lineage.step (index + 1)).shellTrace ≠ 0 ∧
        ∃ receipt : GeneratedIntegerShellReceipt,
          receipt.current =
              (lineage.current (index + 1)).physicalSource ∧
            receipt.wholeShellModes.Nonempty ∧
            ∀ output ∈ receipt.wholeShellModes,
              boundaryRightTangent lineage index output =
                  generatedVorticityNonlinearCoefficientAt
                    (lineage.current (index + 1)).physicalSource
                    output ∧
                ((output ∈
                      generatedSupport
                        (lineage.current
                          (index + 1)).physicalSource ∧
                    boundaryLeftTangent lineage index output =
                      generatedVorticityNonlinearCoefficientAt
                        (lineage.current
                          (index + 1)).physicalSource output ∧
                    boundaryLeftWholeResidual lineage index output =
                      0 ∧
                    boundaryRightTangent lineage index output -
                        boundaryLeftTangent lineage index output =
                      0) ∨
                  (output ∉
                      generatedSupport
                        (lineage.current
                          (index + 1)).physicalSource ∧
                    boundaryLeftTangent lineage index output =
                      0 ∧
                    boundaryLeftWholeResidual lineage index output =
                      -generatedVorticityNonlinearCoefficientAt
                        (lineage.current
                          (index + 1)).physicalSource output ∧
                    boundaryRightTangent lineage index output -
                        boundaryLeftTangent lineage index output =
                      generatedVorticityNonlinearCoefficientAt
                        (lineage.current
                          (index + 1)).physicalSource output ∧
                    boundaryRightTangent lineage index output -
                          boundaryLeftTangent lineage index output ≠
                      0))) := by
  rcases
      generatedFirstShellTrace_actualUnforcedPDE
        lineage (index + 1) with
    traceZero | active
  · exact Or.inl traceZero
  · rcases active with
      ⟨traceNonzero, receipt, currentEq,
        shellNonempty, eachOutput⟩
    refine
      Or.inr
        ⟨traceNonzero, receipt, currentEq,
          shellNonempty, ?_⟩
    intro output outputMem
    rcases eachOutput output outputMem with
      ⟨activeNonlive, _initialZero, _rowDerivative,
        rowNonzero, _traceCoordinateEq, _completeResidualZero⟩
    have rightTangentEq :
        boundaryRightTangent lineage index output =
          generatedVorticityNonlinearCoefficientAt
            (lineage.current (index + 1)).physicalSource
            output := by
      have initial :
          (lineage.physicalReceipt (index + 1)).trajectory 0 =
            generatedCompleteNonlinearInitialState
              (lineage.current (index + 1)).physicalSource :=
        completeOmittedPhysicalTimeReceipt_initial
          (lineage.current (index + 1)).physicalSource ν
      rw [boundaryRightTangent,
        completeOmittedPhysicalLiftSource_generatedSupport,
        initial]
      exact
        completeGalerkinGenerator_activeNonlive
          (lineage.current (index + 1)).physicalSource
          ν.coeff activeNonlive
    refine ⟨rightTangentEq, ?_⟩
    rcases
        (generatedCompleteNonlinearReceipt_consumes_before_quotient
          (lineage.current (index + 1)).physicalSource
          ν ⟨output, activeNonlive⟩).2.2.2 with
      owned | missing
    · rcases owned with
        ⟨supportMem, currentGeneratorEq,
          currentResidualZero⟩
      have leftTangentEq :
          boundaryLeftTangent lineage index output =
            generatedVorticityNonlinearCoefficientAt
              (lineage.current (index + 1)).physicalSource
              output := by
        have boundaryGenerator :=
          congrArg
            (fun tangent : ComplexVorticityHilbertState =>
              tangent output)
            (boundaryLeftTangent_eq_boundarySourceGenerator
              lineage index)
        exact boundaryGenerator.trans currentGeneratorEq
      have boundaryResidualZero :
          boundaryLeftWholeResidual lineage index output = 0 := by
        rw [
          boundaryLeftWholeResidual_eq_boundarySourceResidual
            lineage index output]
        exact currentResidualZero
      have jumpZero :
          boundaryRightTangent lineage index output -
              boundaryLeftTangent lineage index output =
            0 := by
        rw [rightTangentEq, leftTangentEq]
        simp
      exact
        Or.inl
          ⟨supportMem, leftTangentEq,
            boundaryResidualZero, jumpZero⟩
    · rcases missing with
        ⟨supportNotMem, currentResidualEq,
          currentResidualNonzero⟩
      have leftTangentZero :
          boundaryLeftTangent lineage index output = 0 := by
        have boundaryGenerator :=
          congrArg
            (fun tangent : ComplexVorticityHilbertState =>
              tangent output)
            (boundaryLeftTangent_eq_boundarySourceGenerator
              lineage index)
        rw [boundaryGenerator,
          finiteStateVorticityGenerator_apply,
          if_neg supportNotMem]
      have boundaryResidualEq :
          boundaryLeftWholeResidual lineage index output =
            -generatedVorticityNonlinearCoefficientAt
              (lineage.current (index + 1)).physicalSource
              output := by
        rw [
          boundaryLeftWholeResidual_eq_boundarySourceResidual
            lineage index output]
        exact currentResidualEq
      have jumpEq :
          boundaryRightTangent lineage index output -
              boundaryLeftTangent lineage index output =
            generatedVorticityNonlinearCoefficientAt
              (lineage.current (index + 1)).physicalSource
              output := by
        rw [rightTangentEq, leftTangentZero]
        simp
      have jumpNonzero :
          boundaryRightTangent lineage index output -
                boundaryLeftTangent lineage index output ≠
            0 := by
        rw [jumpEq]
        exact rowNonzero
      exact
        Or.inr
          ⟨supportNotMem, leftTangentZero,
            boundaryResidualEq, jumpEq, jumpNonzero⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroBoundaryTangentGluing
end NavierStokes
end SaturationMonoid
