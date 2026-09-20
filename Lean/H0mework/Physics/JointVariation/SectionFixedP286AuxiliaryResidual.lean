import H0mework.Physics.JointVariation.SectionFixedRecenteredResidualNormalForm
import H0mework.Physics.FinalJoint.FixedTimeAxisP286LiveHodgeNormalForm

/-!
# Fixed complete-joint spacetime P286 auxiliary residual

This module reads one coordinate of the already generated whole-carrier
normal form in order to obtain a decisive fixed-lineage regression.  It does
not make the P286 equation a separate producer gate: the result remains a
projection of the simultaneous nine-coordinate residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506P286AuxiliaryResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506RecenteredResidualNormalForm
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286LiveHodgeNormalForm
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev GlobalActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

/-- The P286 auxiliary projection of the global residual is exactly the
matching-contact projection.  The only assembly coordinate visible to this
algebraic action equation is gauge curvature, and the source/current-only
global writer already preserves it identically. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_eq_matching
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        GlobalActual point).p286GaugeAuxiliary =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (fixedP506L0CompleteJointActionMatchingContact point)
        (completeJointActionMatchingContactPoint point)).p286GaugeAuxiliary := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeSection_pointwiseJointResidual_normalForm]
  unfold fixedP506L0CompleteJointActionPointwiseJointResidualNormalForm
    diracDualFormNativeJointResidualOfActionJet
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (StageNineGlobalIntegratedAction.sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource)
        (pointwiseActionJetWithCompleteJointAssemblySeam
          (generatedDiracDualFormNativePointwiseActionJet
            positiveSmoothUnifiedSource
            (fixedP506L0CompleteJointActionMatchingContact point)
            (completeJointActionMatchingContactPoint point))
          (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point)
        ).pointField =
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (StageNineGlobalIntegratedAction.sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource)
        (generatedDiracDualFormNativePointwiseActionJet
          positiveSmoothUnifiedSource
          (fixedP506L0CompleteJointActionMatchingContact point)
          (completeJointActionMatchingContactPoint point)).pointField
  simp only [pointwiseActionJetWithCompleteJointAssemblySeam]
  rw [
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_gaugeCurvature_zero]
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
  simp only [zero_add]

/-- On the canonical time axis through spatial origin, the matching-contact
read is the literal final-common P506/L0 action actual at spatial contact
zero. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_timeAxis_eq_finalCommon
    (time : ℝ) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        GlobalActual (canonicalCauchySlicePoint time 0)
      ).p286GaugeAuxiliary =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual 0)
        (canonicalCauchySlicePoint time 0)).p286GaugeAuxiliary := by
  have matching :=
    fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_eq_matching
      (canonicalCauchySlicePoint time 0)
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon] at matching
  simpa only [canonicalSpatialProjection_slice,
    completeJointActionMatchingContactPoint, canonicalTimeProjection_slice]
    using matching

/-- The global simultaneous residual has the same exact live-Hodge verdict
on its time-axis P286 auxiliary projection as the matching final-common
action contact.  In particular, all-point closure cannot be inferred from
the origin receipt: it is equivalent here to an explicit coefficient
identity of the already generated coframe. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_timeAxis_pairZero_eq_zero_iff
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    p286CoordinateEquiv
        ((diracDualFormNativePointwiseJointResidual
          positiveSmoothUnifiedSource GlobalActual
          (canonicalCauchySlicePoint time 0)).p286GaugeAuxiliary 0) =
        0 ↔
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time =
        1 / 3 := by
  have actualEq :=
    fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_timeAxis_eq_finalCommon
      time
  have coordinateEq := congrArg p286CoordinateEquiv (congrFun actualEq 0)
  rw [coordinateEq]
  change
    p286CoordinateEquiv
        (formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (StageNineGlobalIntegratedAction.sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource)
          (toContinuumPointField (fixedP506L0FinalCommonActionActual 0)
            (canonicalCauchySlicePoint time 0)) 0) =
        0 ↔
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time =
        1 / 3
  simpa only [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate,
    formNativeP286GaugeActualToCoordinateLinear_apply] using
    finalCommon_p286AuxiliaryResidual_timeAxis_pairZero_eq_zero_iff
      time inDomain

/-- Positive origin regression for the explicit live-Hodge mouth.  The
coefficient reduces to `1/3` before any source-specific Hessian coordinate is
needed. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_liveHodgePairZeroCoefficient_origin :
    fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient 0 =
      1 / 3 := by
  unfold fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient
    fixedP506L0FinalCommonTimeAxisSpatialCoframeNormalForm
  simp

/-- Any claimed global zero fiber for the generated `U*` must satisfy the
live-Hodge coefficient identity throughout the canonical nondegenerate time
domain.  This is a necessary readout of the whole-carrier claim, not a
separate equation receipt. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_zeroFiber_implies_liveHodge_identity
    (zeroFiber :
      DiracDualFormNativeJointZeroFiber positiveSmoothUnifiedSource
        GlobalActual)
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time =
      1 / 3 := by
  have pointwiseZero :=
    (diracDualFormNativeJointZeroFiber_iff_pointwise
      positiveSmoothUnifiedSource GlobalActual).1 zeroFiber
      (canonicalCauchySlicePoint time 0)
  have coordinateZero :
      p286CoordinateEquiv
          ((diracDualFormNativePointwiseJointResidual
            positiveSmoothUnifiedSource GlobalActual
            (canonicalCauchySlicePoint time 0)).p286GaugeAuxiliary 0) =
        0 := by
    rw [pointwiseZero]
    simp
  exact
    (fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_timeAxis_pairZero_eq_zero_iff
      time inDomain).1 coordinateZero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506P286AuxiliaryResidual
