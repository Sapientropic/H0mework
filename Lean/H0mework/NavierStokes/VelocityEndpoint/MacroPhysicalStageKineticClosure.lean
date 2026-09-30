import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStage

/-!
# Exact kinetic closure law at an endpoint macro physical interface

The physical stage already proves that zero kinetic defect is sufficient for
strong gluing at the old accumulation endpoint.  Here the converse is forced
from the same actual selected contacts.  Strong continuity of the stage
makes their velocity states converge strongly; the exact contact-wise
velocity/kinetic distance isometry transports that Cauchy property to the
kinetic carrier; its generated weak endpoint then identifies the unique
strong limit, forcing the kinetic defect to vanish.

Consequently positive defect is not merely a nonzero scalar readout.  On the
same native macro response it is exactly a failure of strong physical
interface closure and a nonzero aligned whole-carrier trace.  No convergence,
path equality, endpoint, defect branch or faithfulness law is supplied by a
caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice

noncomputable section

/-! ## Reverse transport of strong convergence on the shared lineage -/

/-- Strong convergence of the generated physical-velocity contacts forces
strong convergence of the kinetic contacts selected at the identical source
indices.  This is the reverse direction of the existing zero-defect physical
completion and uses the exact contact distance isometry. -/
theorem wholeRestartEndpointKinetic_strong_tendsto_of_velocityStrong
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (velocityStrong :
      Tendsto
        (fun index =>
          wholeRestartContactVelocityState initial
            (receipt.subsequence index))
        atTop (nhds receipt.velocityEndpoint)) :
    Tendsto
      (fun index =>
        wholeRestartContactKineticState initial
          (receipt.subsequence index))
      atTop (nhds receipt.kineticReceipt.endpoint) := by
  let velocitySequence : ℕ → WholeRestartVelocityEndpointState :=
    fun index =>
      wholeRestartContactVelocityState initial
        (receipt.subsequence index)
  let kineticSequence : ℕ → WholeRestartKineticEndpointState :=
    fun index =>
      wholeRestartContactKineticState initial
        (receipt.subsequence index)
  have velocityCauchy : CauchySeq velocitySequence := by
    simpa only [velocitySequence] using velocityStrong.cauchySeq
  have kineticCauchy : CauchySeq kineticSequence := by
    rw [Metric.cauchySeq_iff] at velocityCauchy ⊢
    intro epsilon epsilonPos
    obtain ⟨cutoff, close⟩ := velocityCauchy epsilon epsilonPos
    refine ⟨cutoff, ?_⟩
    intro left leftGe right rightGe
    rw [show
      dist (kineticSequence left) (kineticSequence right) =
        dist (velocitySequence left) (velocitySequence right) by
          exact
            (wholeRestartContactVelocityState_dist_eq_kinetic initial
              (receipt.subsequence left)
              (receipt.subsequence right)).symm]
    exact close left leftGe right rightGe
  obtain ⟨kineticLimit, kineticStrong⟩ :=
    cauchySeq_tendsto_of_complete kineticCauchy
  have strongInnerTendsto
      (test : WholeRestartKineticEndpointState) :
      Tendsto
        (fun index => inner ℂ (kineticSequence index) test)
        atTop (nhds (inner ℂ kineticLimit test)) :=
    kineticStrong.inner tendsto_const_nhds
  have weakInnerTendsto
      (test : WholeRestartKineticEndpointState) :
      Tendsto
        (fun index => inner ℂ (kineticSequence index) test)
        atTop (nhds (inner ℂ receipt.kineticReceipt.endpoint test)) := by
    simpa only [kineticSequence] using receipt.kinetic_weak_tendsto test
  have innerEq (test : WholeRestartKineticEndpointState) :
      inner ℂ kineticLimit test =
        inner ℂ receipt.kineticReceipt.endpoint test :=
    tendsto_nhds_unique
      (strongInnerTendsto test) (weakInnerTendsto test)
  have limitEq : kineticLimit = receipt.kineticReceipt.endpoint := by
    let difference := kineticLimit - receipt.kineticReceipt.endpoint
    have selfZero : inner ℂ difference difference = 0 := by
      calc
        inner ℂ difference difference =
            inner ℂ kineticLimit difference -
              inner ℂ receipt.kineticReceipt.endpoint difference := by
          dsimp only [difference]
          rw [inner_sub_left]
        _ = inner ℂ receipt.kineticReceipt.endpoint difference -
              inner ℂ receipt.kineticReceipt.endpoint difference := by
          rw [innerEq difference]
        _ = 0 := sub_self _
    have normSqZero : ‖difference‖ ^ 2 = 0 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact congrArg Complex.re selfZero
    have differenceZero : difference = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg difference]
    exact sub_eq_zero.mp differenceZero
  simpa only [kineticSequence, limitEq] using kineticStrong

/-- Strong physical convergence on the shared generated contacts forces the
source kinetic defect itself to be zero. -/
theorem wholeRestartKineticDefect_eq_zero_of_velocityStrong
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (velocityStrong :
      Tendsto
        (fun index =>
          wholeRestartContactVelocityState initial
            (receipt.subsequence index))
        atTop (nhds receipt.velocityEndpoint)) :
    wholeRestartKineticWeakEndpointDefect
        initial receipt.kineticReceipt.endpoint = 0 := by
  have kineticStrong :=
    wholeRestartEndpointKinetic_strong_tendsto_of_velocityStrong
      receipt velocityStrong
  have normSqToEndpoint :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState initial
            (receipt.subsequence index)‖ ^ 2)
        atTop
        (nhds (‖receipt.kineticReceipt.endpoint‖ ^ 2)) :=
    kineticStrong.norm.pow 2
  have massToLimit :
      Tendsto
        (fun index =>
          wholeRestartContactKineticMass initial
            (receipt.subsequence index))
        atTop (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
      Function.comp_def] using
      receipt.kineticReceipt.mass_tendsto.comp
        receipt.velocitySubsubsequence_strictMono.tendsto_atTop
  have normSqToLimit :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState initial
            (receipt.subsequence index)‖ ^ 2)
        atTop (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [wholeRestartContactKineticMass] using massToLimit
  have endpointNormSqEq :
      ‖receipt.kineticReceipt.endpoint‖ ^ 2 =
        wholeRestartKineticMassLimit initial :=
    tendsto_nhds_unique normSqToEndpoint normSqToLimit
  unfold wholeRestartKineticWeakEndpointDefect
  linarith

/-! ## The actual stage contact sequence -/

namespace GeneratedWholeRestartEndpointMacroStep

/-- The source-selected contact endpoint times, embedded in this macro
stage.  These are the exact occurrences used by the endpoint compiler. -/
def physicalStageSelectedContactTime
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (index : ℕ) : Icc (0 : ℝ) step.clockAdvance :=
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  ⟨elapsedTime current (receipt.subsequence index + 1), by
    constructor
    · exact
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
          current _
    · exact (calc
          elapsedTime current (receipt.subsequence index + 1) <
              wholeRestartVelocityAccumulationTime current :=
            elapsedTime_lt_wholeRestartVelocityAccumulationTime
              current step.elapsedBounded _
          _ ≤ step.clockAdvance := by
            rw [step.clockAdvance_eq_selectedAbsoluteTime]
            exact
              (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
                current step.elapsedBounded).selectedAbsoluteTime_gt_accumulation.le).le⟩

/-- Those exact contact endpoint times converge to the internal accumulation
interface in the macro-stage topology. -/
theorem physicalStageSelectedContactTime_tendsto_accumulation
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Tendsto step.physicalStageSelectedContactTime atTop
      (nhds step.physicalStageAccumulation) := by
  rw [tendsto_subtype_rng]
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  change
    Tendsto
      (fun index => elapsedTime current (receipt.subsequence index + 1))
      atTop (nhds (wholeRestartVelocityAccumulationTime current))
  exact
    (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      current step.elapsedBounded).prefixEndpointTime_tendsto

/-- Reading the physical stage at a selected contact time returns the exact
actual contact velocity on that same occurrence. -/
theorem physicalStage_selectedContactTime
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (index : ℕ) :
    let receipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    step.physicalStage (step.physicalStageSelectedContactTime index) =
      wholeRestartContactVelocityState current
        (receipt.subsequence index) := by
  dsimp only
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  have timeBefore :
      ((step.physicalStageTime
        (step.physicalStageSelectedContactTime index))).1 <
        wholeRestartVelocityAccumulationTime current := by
    exact elapsedTime_lt_wholeRestartVelocityAccumulationTime
      current step.elapsedBounded _
  rw [physicalStage,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
      current step.elapsedBounded _ timeBefore]
  have contact :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint
      current step.elapsedBounded (receipt.subsequence index)
  convert contact using 1
  apply Subtype.ext
  rfl

/-- The stage value at its internal accumulation interface is the literal
physical velocity endpoint selected by the same source receipt. -/
theorem physicalStage_accumulation
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    let receipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    step.physicalStage step.physicalStageAccumulation =
      receipt.velocityEndpoint := by
  dsimp only
  have timeEq :
      step.physicalStageTime step.physicalStageAccumulation =
        wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
          current step.elapsedBounded := by
    apply Subtype.ext
    rfl
  rw [physicalStage, timeEq]
  exact
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start
      current step.elapsedBounded

/-- Strong continuity of the actual stage forces strong convergence of the
exact selected physical contacts; no convergence is accepted as a premise by
the endpoint producer. -/
theorem selectedVelocity_strong_tendsto_of_physicalStage_continuousAt
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (stageContinuous :
      ContinuousAt step.physicalStage step.physicalStageAccumulation) :
    let receipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    Tendsto
      (fun index =>
        wholeRestartContactVelocityState current
          (receipt.subsequence index))
      atTop (nhds receipt.velocityEndpoint) := by
  dsimp only
  have outer :
      Tendsto step.physicalStage
        (nhds step.physicalStageAccumulation)
        (nhds (step.physicalStage step.physicalStageAccumulation)) :=
    stageContinuous
  have composedRaw := outer.comp
    step.physicalStageSelectedContactTime_tendsto_accumulation
  have composed :
      Tendsto
        (fun index =>
          step.physicalStage (step.physicalStageSelectedContactTime index))
        atTop
        (nhds (step.physicalStage step.physicalStageAccumulation)) := by
    simpa only [Function.comp_def] using composedRaw
  simpa only [step.physicalStage_selectedContactTime,
    step.physicalStage_accumulation] using composed

/-- Strong closure of the actual physical interface is possible only when
the internally generated kinetic defect is zero. -/
theorem kineticDefect_eq_zero_of_physicalStage_continuousAt
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (stageContinuous :
      ContinuousAt step.physicalStage step.physicalStageAccumulation) :
    wholeRestartKineticWeakEndpointDefect current
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
      0 := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  exact
    wholeRestartKineticDefect_eq_zero_of_velocityStrong receipt
      (step.selectedVelocity_strong_tendsto_of_physicalStage_continuousAt
        stageContinuous)

/-- Exact physical meaning of the source-generated kinetic defect on one
native macro stage. -/
theorem physicalStage_continuousAt_accumulation_iff_kineticDefect_eq_zero
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    ContinuousAt step.physicalStage step.physicalStageAccumulation ↔
      wholeRestartKineticWeakEndpointDefect current
          (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
            current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0 := by
  constructor
  · exact step.kineticDefect_eq_zero_of_physicalStage_continuousAt
  · exact
      step.physicalStage_continuousAt_accumulation_of_kineticDefect_eq_zero

/-- Positive defect is a concrete strong-interface obstruction on the same
actual stage. -/
theorem physicalStage_not_continuousAt_accumulation_of_kineticDefect_pos
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (defectPos :
      0 < wholeRestartKineticWeakEndpointDefect current
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint) :
    ¬ ContinuousAt step.physicalStage step.physicalStageAccumulation := by
  intro stageContinuous
  have defectZero :=
    step.kineticDefect_eq_zero_of_physicalStage_continuousAt
      stageContinuous
  linarith

/-- Premise-free exact stage disposition generated by the source receipt:
either the physical interface closes strongly, or it fails strongly and the
identical native response writes a nonzero aligned whole-carrier trace. -/
theorem physicalStage_continuousAt_or_discontinuous_with_alignedTrace
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    ContinuousAt step.physicalStage step.physicalStageAccumulation ∨
      (¬ ContinuousAt step.physicalStage step.physicalStageAccumulation ∧
        step.alignedTrace ≠ 0) := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt.kineticReceipt
  rcases receipt.defect_disposition with defectPos | ⟨defectZero, _strong⟩
  · exact Or.inr
      ⟨step.physicalStage_not_continuousAt_accumulation_of_kineticDefect_pos
          defectPos,
        step.alignedTrace_ne_zero_of_kineticDefect_pos defectPos⟩
  · exact Or.inl
      (step.physicalStage_continuousAt_accumulation_of_kineticDefect_eq_zero
        defectZero)

end GeneratedWholeRestartEndpointMacroStep

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
