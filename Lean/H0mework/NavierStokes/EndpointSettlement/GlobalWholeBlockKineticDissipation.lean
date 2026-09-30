import H0mework.NavierStokes.EndpointSettlement.GlobalWholeBlockAction
import H0mework.NavierStokes.KineticRestart.CumulativeKineticDissipation

/-!
# Whole-PDE kinetic settlement of the reduced-core global block action

The reduced-core block action already lives on the authoritative global
unforced path.  This module consumes that action with the existing native
kinetic-dissipation ledger.

For every source-generated block, the complete physical dissipation of all
actual restart receipts in the block is charged exactly once.  The resulting
whole-carrier inequality strengthens the quadratic block boundary:

```text
native write-square + actual viscous payment
  ≤ -2 · incoming physical work.
```

Along the same internally generated scale lineage, the global contact
energies converge to the old-run kinetic mass limit, and their energy gap to
the literal accumulation-interface value converges to the stage kinetic
defect.  No scale, block, time, cutoff, target path, continuity certificate,
or energy bound is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-! ## Actual native dissipation on an arbitrary consecutive block -/

/-- Complete physical vorticity dissipation of a consecutive block of
source-owned native restart receipts. -/
def wholeRestartIntervalKineticDissipationPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range steps,
    wholeRestartNextKineticDissipationPayment initial (start + offset)

theorem wholeRestartIntervalKineticDissipationPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    0 ≤ wholeRestartIntervalKineticDissipationPayment
      initial start steps := by
  unfold wholeRestartIntervalKineticDissipationPayment
  exact Finset.sum_nonneg fun offset _offsetMem =>
    wholeRestartNextKineticDissipationPayment_nonneg
      initial (start + offset)

/-- The native kinetic ledger telescopes on every consecutive block, not
only on prefixes beginning at zero. -/
theorem run_contact_kineticMass_add_intervalDissipation_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : ℕ) :
    ∀ steps : ℕ,
      puncturedWholeVorticityKineticMass
            (run initial (start + steps)).contact.physicalState +
          wholeRestartIntervalKineticDissipationPayment
            initial start steps ≤
        puncturedWholeVorticityKineticMass
          (run initial start).contact.physicalState
  | 0 => by
      simp [wholeRestartIntervalKineticDissipationPayment]
  | Nat.succ steps => by
      have finalStep :=
        run_contact_kineticDissipation_succ_le
          initial (start + steps)
      have prefixBound :=
        run_contact_kineticMass_add_intervalDissipation_le
          initial start steps
      unfold wholeRestartIntervalKineticDissipationPayment at prefixBound ⊢
      rw [Finset.sum_range_succ]
      calc
        puncturedWholeVorticityKineticMass
              (run initial (start + (steps + 1))).contact.physicalState +
            ((∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset)) +
              wholeRestartNextKineticDissipationPayment
                initial (start + steps)) =
            (puncturedWholeVorticityKineticMass
                (run initial ((start + steps) + 1)).contact.physicalState +
              wholeRestartNextKineticDissipationPayment
                initial (start + steps)) +
              ∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset) := by
          rw [← Nat.add_assoc start steps 1]
          ring
        _ ≤
            puncturedWholeVorticityKineticMass
                (run initial (start + steps)).contact.physicalState +
              ∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset) :=
          add_le_add finalStep le_rfl
        _ ≤
            puncturedWholeVorticityKineticMass
              (run initial start).contact.physicalState :=
          prefixBound

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-! ## The source-generated action reaches the exact endpoint defect -/

/-- All scale contacts generated inside one global whole-block action retain
the complete old-run kinetic mass limit. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.globalPathContactNormSq_tendsto_massLimit
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    Tendsto
      (fun node =>
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence node))‖ ^ 2)
      atTop
      (nhds (wholeRestartKineticMassLimit (lineage.current stage))) := by
  have massTendsto :
      Tendsto
        (fun node =>
          wholeRestartContactKineticMass
            (lineage.current stage)
            (action.scale.absoluteOccurrence node))
        atTop
        (nhds (wholeRestartKineticMassLimit (lineage.current stage))) :=
    (wholeRestartContactKineticMass_tendsto_limit
      (lineage.current stage)).comp
        action.scale.absoluteOccurrence_strict.tendsto_atTop
  convert massTendsto using 1
  funext node
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    wholeRestartContactKineticMass,
    wholeRestartContactVelocityState_norm_sq,
    wholeRestartContactKineticState,
    puncturedWholeVorticityKineticEuclideanState_norm_sq]

/-- The whole-stage energy gap seen along the action's own scale contacts
converges exactly to the source-generated kinetic completion defect. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.globalPathContactEnergyGap_tendsto_stageDefect
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    Tendsto
      (fun node =>
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence node))‖ ^ 2 -
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.globalStageAccumulationTime stage)‖ ^ 2)
      atTop
      (nhds (infiniteEndpointMacroStageKineticDefect lineage stage)) := by
  have interfaceEq :
      lineage.globalAbsoluteVelocityTrajectory
          (lineage.globalStageAccumulationTime stage) =
        (lineage.step stage).physicalStage
          (lineage.step stage).physicalStageAccumulation := by
    rw [globalStageAccumulationTime]
    change
      lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage +
            (((lineage.step stage).physicalStageAccumulation :
              Icc (0 : ℝ) (lineage.step stage).clockAdvance) : ℝ)) =
        (lineage.step stage).physicalStage
          (lineage.step stage).physicalStageAccumulation
    exact lineage.globalAbsoluteVelocityTrajectory_eq_stage
      stage (lineage.step stage).physicalStageAccumulation
  rw [interfaceEq]
  have shifted :=
    action.globalPathContactNormSq_tendsto_massLimit.sub_const
      (‖(lineage.step stage).physicalStage
        (lineage.step stage).physicalStageAccumulation‖ ^ 2)
  rw [infiniteEndpointMacroStageKineticDefect,
    ← (lineage.step stage).physicalStageKineticEnergyAtom_eq_defect]
  simpa only [
    GeneratedWholeRestartEndpointMacroStep.physicalStageKineticEnergyAtom]
    using shifted

/-! ## Whole-block PDE settlement -/

/-- The actual physical dissipation paid by every native receipt between two
adjacent source-generated scale contacts. -/
def
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPayment
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) : ℝ :=
  wholeRestartIntervalKineticDissipationPayment
    (lineage.current stage)
    (action.scale.absoluteOccurrence node)
    (action.scale.nextScaleGap node)

theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPayment_nonneg
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    0 ≤ action.blockKineticDissipationPayment node :=
  wholeRestartIntervalKineticDissipationPayment_nonneg
    (lineage.current stage)
    (action.scale.absoluteOccurrence node)
    (action.scale.nextScaleGap node)

/-- The complete actual PDE payment of one source-generated block is charged
between the same two sections of the authoritative global path. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.globalPathKineticDissipation_le
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence (node + 1)))‖ ^ 2 +
        action.blockKineticDissipationPayment node ≤
      ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence node))‖ ^ 2 := by
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    lineage.globalAbsoluteVelocityTrajectory_actualContact,
    wholeRestartContactVelocityState_norm_sq,
    wholeRestartContactVelocityState_norm_sq]
  have paid :=
    run_contact_kineticMass_add_intervalDissipation_le
      (lineage.current stage)
      (action.scale.absoluteOccurrence node)
      (action.scale.nextScaleGap node)
  rw [action.scale.absoluteOccurrence_add_nextScaleGap node] at paid
  simpa only [
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPayment]
    using paid

/-- Whole-PDE settlement of the exact quadratic block boundary.  The native
write-square and all physical vorticity dissipation in the block are paid by
the same block's negative incoming work. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.nativeSquare_add_dissipation_le_neg_two_work
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    action.scale.wholeBlockNativeVelocitySquare node +
        action.blockKineticDissipationPayment node ≤
      -2 * action.scale.wholeBlockIncomingVelocityWork node := by
  have paid := action.globalPathKineticDissipation_le node
  have boundary := action.kinetic_boundary node
  linarith

/-- The complete tangent/output-by-pair boundary of the same source block,
before any pair or Fourier quotient, is settled together with the actual
physical dissipation of that block. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundary_add_dissipation_le_zero
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    action.scale.wholeBlockComponentKineticBoundary node +
        action.blockKineticDissipationPayment node ≤ 0 := by
  have paid := action.globalPathKineticDissipation_le node
  have boundary := action.component_boundary node
  linarith

/-! ## The entire source-generated stage action -/

/-- Actual physical dissipation accumulated over a finite prefix of the
source-generated whole-block action. -/
def
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) : ℝ :=
  ∑ node ∈ Finset.range length,
    action.blockKineticDissipationPayment node

theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix_nonneg
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) :
    0 ≤ action.blockKineticDissipationPrefix length := by
  unfold
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix
  exact Finset.sum_nonneg fun node _nodeMem =>
    action.blockKineticDissipationPayment_nonneg node

/-- The complete pre-quotient component boundary of every finite action
prefix telescopes exactly to the two endpoint energies on the global path. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundaryPrefix_eq_globalPathEnergyGap
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    ∀ length : ℕ,
      (∑ node ∈ Finset.range length,
          action.scale.wholeBlockComponentKineticBoundary node) =
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence length))‖ ^ 2 -
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence 0))‖ ^ 2
  | 0 => by simp
  | Nat.succ length => by
      rw [Finset.sum_range_succ,
        action.componentBoundaryPrefix_eq_globalPathEnergyGap length,
        action.component_boundary length]
      ring

/-- Every finite prefix of the entire pre-quotient component action is
settled together with the actual physical dissipation of the same global
stage. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundaryPrefix_add_dissipation_le_zero
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) :
    (∑ node ∈ Finset.range length,
        action.scale.wholeBlockComponentKineticBoundary node) +
        action.blockKineticDissipationPrefix length ≤ 0 := by
  have settled :=
    Finset.sum_le_sum fun node (_nodeMem : node ∈ Finset.range length) =>
      action.componentBoundary_add_dissipation_le_zero node
  rw [Finset.sum_add_distrib] at settled
  simpa only [
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix,
    Finset.sum_const_zero] using settled

/-- The complete viscous payment of every finite action prefix is uniformly
paid by the energy between the first scale contact and the old-run kinetic
mass limit. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix_le_initial_sub_massLimit
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) :
    action.blockKineticDissipationPrefix length ≤
      ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (action.scale.absoluteOccurrence 0))‖ ^ 2 -
        wholeRestartKineticMassLimit (lineage.current stage) := by
  have settled :=
    action.componentBoundaryPrefix_add_dissipation_le_zero length
  rw [action.componentBoundaryPrefix_eq_globalPathEnergyGap length]
    at settled
  have massRangeLower :
      BddBelow
        (Set.range
          (wholeRestartContactKineticMass (lineage.current stage))) :=
    ⟨0, Set.forall_mem_range.mpr fun index =>
      sq_nonneg ‖wholeRestartContactKineticState
        (lineage.current stage) index‖⟩
  have limitLeMass :
      wholeRestartKineticMassLimit (lineage.current stage) ≤
        wholeRestartContactKineticMass
          (lineage.current stage)
          (action.scale.absoluteOccurrence length) := by
    unfold wholeRestartKineticMassLimit
    exact ciInf_le massRangeLower
      (action.scale.absoluteOccurrence length)
  have limitLeEnergy :
      wholeRestartKineticMassLimit (lineage.current stage) ≤
        ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (action.scale.absoluteOccurrence length))‖ ^ 2 := by
    calc
      wholeRestartKineticMassLimit (lineage.current stage) ≤
          wholeRestartContactKineticMass
            (lineage.current stage)
            (action.scale.absoluteOccurrence length) :=
        limitLeMass
      _ =
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence length))‖ ^ 2 := by
        symm
        rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
          wholeRestartContactKineticMass,
          wholeRestartContactVelocityState_norm_sq,
          wholeRestartContactKineticState,
          puncturedWholeVorticityKineticEuclideanState_norm_sq]
  linarith

/-- The entire actual physical dissipation family of one source-generated
stage action is summable.  Hence positive blocks cannot be turned into a
contradiction merely by counting them; the remaining endpoint responsibility
lies in the complete component/strong-join channel. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.summable_blockKineticDissipationPayment
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    Summable action.blockKineticDissipationPayment := by
  apply summable_of_sum_range_le
  · exact action.blockKineticDissipationPayment_nonneg
  · intro length
    simpa only [
      WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix]
      using
        action.blockKineticDissipationPrefix_le_initial_sub_massLimit
          length

/-- After all source-generated blocks are consumed, the old-run kinetic
mass limit and the complete actual viscous payment remain below the first
scale-contact energy. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.massLimit_add_totalBlockDissipation_le_initial
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    wholeRestartKineticMassLimit (lineage.current stage) +
        ∑' node : ℕ, action.blockKineticDissipationPayment node ≤
      ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (action.scale.absoluteOccurrence 0))‖ ^ 2 := by
  have totalPaymentLe :
      (∑' node : ℕ, action.blockKineticDissipationPayment node) ≤
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence 0))‖ ^ 2 -
          wholeRestartKineticMassLimit (lineage.current stage) := by
    exact
      action.summable_blockKineticDissipationPayment.tsum_le_of_sum_range_le
        action.blockKineticDissipationPrefix_le_initial_sub_massLimit
  linarith

/-- Whole-stage residual transport: the initial contact-to-interface energy
gap plus every generated complete component boundary converges exactly to
the source kinetic completion defect.  Thus the endpoint defect is the
remaining stage residual after all finite whole-block actions have been
written, not an independent completion receipt. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundaryTransport_tendsto_stageDefect
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    Tendsto
      (fun length =>
        (‖lineage.globalAbsoluteVelocityTrajectory
              (lineage.actualContactGlobalTime
                stage (action.scale.absoluteOccurrence 0))‖ ^ 2 -
            ‖lineage.globalAbsoluteVelocityTrajectory
              (lineage.globalStageAccumulationTime stage)‖ ^ 2) +
          ∑ node ∈ Finset.range length,
            action.scale.wholeBlockComponentKineticBoundary node)
      atTop
      (nhds (infiniteEndpointMacroStageKineticDefect lineage stage)) := by
  convert action.globalPathContactEnergyGap_tendsto_stageDefect using 1
  funext length
  rw [action.componentBoundaryPrefix_eq_globalPathEnergyGap length]
  ring

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
