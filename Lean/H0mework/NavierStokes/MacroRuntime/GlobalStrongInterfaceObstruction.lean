import H0mework.NavierStokes.MacroRuntime.GlobalAbsoluteVelocity
import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStageKineticClosure

/-!
# Positive endpoint defect as a global strong-interface obstruction

The infinite endpoint-macro lineage now owns one stabilized absolute velocity
path whose chart on every generated macro interval is literal.  The local
kinetic closure law identifies positive defect with failure of strong
continuity at the internal accumulation point of that exact chart.  This
module transports the obstruction to its generated absolute time

`macroClock index + accumulationTime(current index)`.

Thus a positive source disposition is directly visible to an independent
PDE regularity consumer: the generated global path is strongly discontinuous
there, while the identical native response writes a nonzero aligned trace.
No global path, discontinuity witness, time, branch, observer or faithfulness
law is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The actual absolute physical time of the old-run accumulation interface
inside one generated macro stage. -/
def globalStageAccumulationTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (index : ℕ) : ℝ :=
  lineage.macroClock index +
    wholeRestartVelocityAccumulationTime (lineage.current index)

/-- Positive defect at one generated stage forces strong discontinuity of
the single stabilized global absolute velocity path at that stage's exact
physical accumulation time. -/
theorem globalAbsoluteVelocityTrajectory_not_continuousAt_of_stageDefect_pos
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (index : ℕ)
    (defectPositive :
      0 < infiniteEndpointMacroStageKineticDefect lineage index) :
    ¬ ContinuousAt lineage.globalAbsoluteVelocityTrajectory
        (lineage.globalStageAccumulationTime index) := by
  intro globalContinuous
  let step := lineage.step index
  let shift : Icc (0 : ℝ) step.clockAdvance → ℝ :=
    fun localTime => lineage.macroClock index + localTime.1
  have shiftContinuous : Continuous shift := by
    exact continuous_const.add continuous_subtype_val
  have outer :
      Tendsto lineage.globalAbsoluteVelocityTrajectory
        (nhds
          (lineage.macroClock index +
            wholeRestartVelocityAccumulationTime (lineage.current index)))
        (nhds
          (lineage.globalAbsoluteVelocityTrajectory
            (lineage.macroClock index +
              wholeRestartVelocityAccumulationTime
                (lineage.current index)))) := by
    change Tendsto lineage.globalAbsoluteVelocityTrajectory
      (nhds
        (lineage.macroClock index +
          wholeRestartVelocityAccumulationTime (lineage.current index)))
      (nhds
        (lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock index +
            wholeRestartVelocityAccumulationTime (lineage.current index))))
      at globalContinuous
    exact globalContinuous
  have inner :
      Tendsto shift (nhds step.physicalStageAccumulation)
        (nhds
          (lineage.macroClock index +
            wholeRestartVelocityAccumulationTime
              (lineage.current index))) := by
    change ContinuousAt shift step.physicalStageAccumulation
    exact shiftContinuous.continuousAt
  have composedRaw := outer.comp inner
  have composed :
      ContinuousAt
        (fun localTime : Icc (0 : ℝ) step.clockAdvance =>
          lineage.globalAbsoluteVelocityTrajectory
            (lineage.macroClock index + localTime.1))
        step.physicalStageAccumulation := by
    change Tendsto
      (fun localTime : Icc (0 : ℝ) step.clockAdvance =>
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock index + localTime.1))
      (nhds step.physicalStageAccumulation)
      (nhds
        (lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock index +
            step.physicalStageAccumulation.1)))
    convert composedRaw using 1
    · rfl
    · congr 2
  have stageEq :
      (fun localTime : Icc (0 : ℝ) step.clockAdvance =>
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock index + localTime.1)) =
        step.physicalStage := by
    funext localTime
    exact lineage.globalAbsoluteVelocityTrajectory_eq_stage
      index localTime
  have stageContinuous :
      ContinuousAt step.physicalStage
        step.physicalStageAccumulation := by
    rw [← stageEq]
    exact composed
  have localDefectPositive :
      0 < wholeRestartKineticWeakEndpointDefect (lineage.current index)
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          (lineage.current index)
          step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint := by
    simpa only [infiniteEndpointMacroStageKineticDefect, step] using
      defectPositive
  exact
    (step.physicalStage_not_continuousAt_accumulation_of_kineticDefect_pos
      localDefectPositive) stageContinuous

/-- The same positive stage simultaneously exposes the global physical
discontinuity and writes its nonzero aligned whole-carrier responsibility. -/
theorem globalStrongDiscontinuity_and_alignedTrace_ne_zero_of_stageDefect_pos
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (index : ℕ)
    (defectPositive :
      0 < infiniteEndpointMacroStageKineticDefect lineage index) :
    (¬ ContinuousAt lineage.globalAbsoluteVelocityTrajectory
        (lineage.globalStageAccumulationTime index)) ∧
      (lineage.step index).alignedTrace ≠ 0 := by
  have localDefectPositive :
      0 < wholeRestartKineticWeakEndpointDefect (lineage.current index)
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          (lineage.current index)
          (lineage.step index).elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint := by
    simpa only [infiniteEndpointMacroStageKineticDefect] using
      defectPositive
  exact
    ⟨lineage.globalAbsoluteVelocityTrajectory_not_continuousAt_of_stageDefect_pos
        index defectPositive,
      (lineage.step index).alignedTrace_ne_zero_of_kineticDefect_pos
        localDefectPositive⟩

/-- Any independent strong-continuity theorem for the actual generated
global path eliminates positive defect at every source-generated stage. -/
theorem stageDefect_eq_zero_of_globalAbsoluteVelocityTrajectory_continuous
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (globalContinuous :
      Continuous lineage.globalAbsoluteVelocityTrajectory)
    (index : ℕ) :
    infiniteEndpointMacroStageKineticDefect lineage index = 0 := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current index)
      (lineage.step index).elapsedBounded).family.endpointReceipt.kineticReceipt
  rcases receipt.defect_disposition with defectPositive | zeroDisposition
  · exact False.elim <|
      (lineage.globalAbsoluteVelocityTrajectory_not_continuousAt_of_stageDefect_pos
        index (by
          simpa only [infiniteEndpointMacroStageKineticDefect, receipt] using
            defectPositive)) globalContinuous.continuousAt
  · simpa only [infiniteEndpointMacroStageKineticDefect, receipt] using
      zeroDisposition.1

end GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- A strong-continuity theorem for the actual source-generated global path
therefore forces the public infinite-lineage producer into its all-zero
global branch.  The target path is not supplied: it is the stabilized path
already generated by the lineage. -/
noncomputable def
    generatedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity_of_continuous
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (globalContinuous :
      Continuous lineage.globalAbsoluteVelocityTrajectory) :
    GeneratedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity
      lineage := by
  exact
    match generatedInfiniteWholeRestartEndpointMacroKineticDisposition
        lineage with
    | .positive index defectPositive =>
        False.elim <|
          (lineage.globalAbsoluteVelocityTrajectory_not_continuousAt_of_stageDefect_pos
            index defectPositive) globalContinuous.continuousAt
    | .allZero global => global

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
