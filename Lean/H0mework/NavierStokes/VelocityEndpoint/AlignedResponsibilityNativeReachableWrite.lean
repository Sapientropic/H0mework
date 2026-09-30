import H0mework.NavierStokes.VelocityEndpoint.AlignedResponsibilityMacroWrite
import H0mework.NavierStokes.VelocityEndpoint.NativeReachableContinuation

/-!
# The aligned endpoint write is the first native reachable response

The common endpoint macro writes physical continuation and the complete
component/kinetic trace.  The endpoint runtime independently presents its
first source response as the dependent edge from `accumulation` to `after 0`.
Here the two presentations are identified before any terminal or maximality
consumer: the macro phase update compiles to the literal target of that exact
response, and its physical frame is the runtime's actual `afterCurrent 0`.

No target node, reachability proof, continuation, ledger equality or branch
is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityNativeReachableWrite

open Filter Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation.GeneratedWholeRestartVelocityEndpointRuntimeState
open AffineRelaxation

noncomputable section

/-- The endpoint macro phases viewed in the concrete source-owned endpoint
runtime.  No later runtime node is introduced by this compiler. -/
def wholeRestartEndpointAlignedMacroRuntimeState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      GeneratedWholeRestartVelocityEndpointRuntimeState
        initial elapsedBounded
  | accumulationRead => .accumulation
  | endpointWritten => .after 0

@[simp] theorem wholeRestartEndpointAlignedMacroRuntimeState_read
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroRuntimeState
        initial elapsedBounded accumulationRead =
      .accumulation :=
  rfl

@[simp] theorem wholeRestartEndpointAlignedMacroRuntimeState_written
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroRuntimeState
        initial elapsedBounded endpointWritten =
      .after 0 :=
  rfl

/-- The macro write and the actual endpoint responder have exactly the same
source and target. -/
theorem wholeRestartEndpointAlignedMacroUpdate_commutes_nativeResponse
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (generatedWholeRestartVelocityEndpointNativeResponse
        initial elapsedBounded .accumulation).1 := by
  rfl

/-- The dependent payload itself is the existing absolute whole-mild
continuation carried by the aligned macro target.  This prevents the ledger
write and the physical continuation from being read as parallel edges. -/
theorem wholeRestartEndpointNativeResponse_eq_alignedMacroWrite
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    generatedWholeRestartVelocityEndpointNativeResponse
        initial elapsedBounded .accumulation =
      ⟨wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead),
        .endpointWrite
          (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
            initial elapsedBounded)⟩ := by
  rfl

/-- The write component returned by the reflexive macro query is the target
of the literal source responder, not a separately chosen continuation. -/
theorem wholeRestartEndpointAlignedMacroQuery_write_eq_nativeResponse
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
        ((generatedWholeRestartEndpointAlignedMacroQuery
          initial elapsedBounded).run accumulationRead).2 =
      (generatedWholeRestartVelocityEndpointNativeResponse
        initial elapsedBounded .accumulation).1 := by
  rfl

/-- The macro write target is least reachable by executing that same source
response. -/
def wholeRestartEndpointAlignedMacroUpdate_nativeReachable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    NativeReachable
      (.accumulation :
        GeneratedWholeRestartVelocityEndpointRuntimeState
          initial elapsedBounded)
      (generatedWholeRestartVelocityEndpointNativeRespond
        initial elapsedBounded)
      (wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)) := by
  exact
    generatedWholeRestartVelocityEndpointAfterZeroReachable
      initial elapsedBounded

/-- Exact same-edge frame equation.  Executing the first reachable endpoint
response writes its actual post-accumulation current and the complete aligned
trace ledger in one step. -/
theorem wholeRestartEndpointAlignedMacroFrame_nativeReachableWrite
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (afterCurrent initial elapsedBounded 0,
        0,
        wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0) := by
  rw [wholeRestartEndpointAlignedMacroFrame_update,
    afterCurrent_zero]

/-- Consequently the physical state written by the aligned macro is the
physical current at the first strictly post-accumulation reachable node. -/
theorem wholeRestartEndpointAlignedMacroFrame_physical_eq_afterCurrent
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (wholeRestartEndpointAlignedMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
      afterCurrent initial elapsedBounded 0 := by
  rw [wholeRestartEndpointAlignedMacroFrame_physical_update,
    afterCurrent_zero]

/-- The target clock of this exact responsibility-bearing macro write is
strictly beyond the source-generated accumulation time. -/
theorem wholeRestartEndpointAlignedMacroWrite_absoluteTime_gt_accumulation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    absoluteTime initial elapsedBounded
        (wholeRestartEndpointAlignedMacroRuntimeState
          initial elapsedBounded accumulationRead) <
      absoluteTime initial elapsedBounded
        (wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)) := by
  exact accumulation_lt_absoluteTime_after_zero initial elapsedBounded

/-- The source-selected H¹ reentry is uniformly late on the endpoint write:
the exact first response target lies more than one half-unit beyond the old
accumulation clock. -/
theorem
    wholeRestartEndpointAlignedMacroWrite_accumulation_add_half_lt_absoluteTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    absoluteTime initial elapsedBounded
          (wholeRestartEndpointAlignedMacroRuntimeState
            initial elapsedBounded accumulationRead) +
        (1 : ℝ) / 2 <
      absoluteTime initial elapsedBounded
        (wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)) := by
  simp only [wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointAlignedMacroRuntimeState,
    absoluteTime_accumulation, absoluteTime_after_zero]
  change
    wholeRestartVelocityAccumulationTime initial + (1 : ℝ) / 2 <
      wholeRestartVelocityAccumulationTime initial +
        (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
          initial elapsedBounded).time.1
  simpa only [add_comm] using
    add_lt_add_left
      (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
        initial elapsedBounded).time_half_lt
      (wholeRestartVelocityAccumulationTime initial)

/-- Measured from the current's own zero clock, the same actual endpoint
response advances physical time by more than one half-unit. -/
theorem wholeRestartEndpointAlignedMacroWrite_half_lt_absoluteTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (1 : ℝ) / 2 <
      absoluteTime initial elapsedBounded
        (wholeRestartEndpointAlignedMacroRuntimeState initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)) := by
  have accumulationNonneg :
      0 ≤ wholeRestartVelocityAccumulationTime initial := by
    unfold wholeRestartVelocityAccumulationTime
    simpa using (le_ciSup elapsedBounded 0)
  simp only [wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointAlignedMacroRuntimeState,
    absoluteTime_after_zero]
  change
    (1 : ℝ) / 2 <
      wholeRestartVelocityAccumulationTime initial +
        (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
          initial elapsedBounded).time.1
  linarith [
    (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded).time_half_lt]

/-! ## Positive kinetic defect is a nonzero native endpoint write -/

/-- Conditional consumer of the internally generated positive-defect branch.
The actual first endpoint response then writes a nonzero whole aligned trace
ledger.  Positivity is not part of the macro producer mouth, and no finite
observer or selected occurrence is supplied. -/
theorem wholeRestartEndpointAlignedMacroTraceLedger_ne_zero_of_defect_pos
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectPos :
      0 < wholeRestartKineticWeakEndpointDefect initial
        ((generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint)) :
    wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) ≠ 0 := by
  have eventuallyPositive :
      ∀ᶠ index : ℕ in atTop,
        wholeRestartKineticWeakEndpointDefect initial
              ((generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
                initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint) /
            2 <
          ‖(linearResidualTrace wholeRestartEndpointAlignedMacroKeep
              (wholeRestartEndpointAlignedMacroPending
                initial elapsedBounded accumulationRead) index).2‖ ^ 2 :=
    (wholeRestartEndpointAlignedMacro_kineticTrace_norm_sq_tendsto_defect
      elapsedBounded) (eventually_gt_nhds (by linarith))
  obtain ⟨index, indexPositive⟩ := eventuallyPositive.exists
  intro ledgerZero
  have writtenKineticZero :
      wholeRestartEndpointAlignedKineticResidual
        initial elapsedBounded index = 0 := by
    rw [← wholeRestartEndpointAlignedMacro_writtenKinetic
      elapsedBounded index]
    have rowZero := congrFun ledgerZero index
    exact congrArg Prod.snd rowZero
  rw [wholeRestartEndpointAlignedMacro_kineticTrace_apply
    elapsedBounded index, writtenKineticZero] at indexPositive
  norm_num at indexPositive
  linarith

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityNativeReachableWrite
end NavierStokes
end SaturationMonoid
