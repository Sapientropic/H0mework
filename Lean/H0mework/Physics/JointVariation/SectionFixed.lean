import H0mework.Physics.JointVariation.SectionOperator
import H0mework.Physics.JointVariation.ResponseOperatorFixedSpecialization
import H0mework.Physics.FinalJoint.FixedZeroFiber
import H0mework.Physics.FixedJoint.FixedSectionResponse

/-!
# Fixed P506/L0 complete-joint spacetime section

This module specializes the source/current-only spacetime-section write to
the authoritative fixed P506/L0 solved current.  At each canonical spatial
contact, the internally generated Cartan restart followed by the complete
joint action is exactly the existing final-common contact actual.  Hence all
matching contacts have the already proved nine-channel zero fiber at their
origins.

The one global diagonal actual is defined before any contact restriction or
assembly seam is read.  Its whole action jet is then compared with the
matching contact through the exhaustive seam carrier from the generic
producer module.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionResponseOperatorFixedP506Specialization
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- One global complete-joint actual generated from the fixed P506/L0 source
and solved current.  No contact family, residual, seam, or zero receipt is an
input. -/
def fixedP506L0CompleteJointActionSpacetimeSectionActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
    positiveSmoothUnifiedSource FixedInput

/-- The matching contact read from the fixed global producer at one spacetime
occurrence. -/
def fixedP506L0CompleteJointActionMatchingContact
    (point : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointActionMatchingContact positiveSmoothUnifiedSource FixedInput
    point

/-- The matching contact is definitionally the existing fixed final-common
action actual selected by the occurrence's spatial coordinate. -/
theorem fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon
    (point : BasePoint) :
    fixedP506L0CompleteJointActionMatchingContact point =
      fixedP506L0FinalCommonActionActual
        (canonicalSpatialProjection point) := by
  unfold fixedP506L0CompleteJointActionMatchingContact
    completeJointActionMatchingContact completeJointActionSpatialContact
    FixedInput
  simpa [fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput] using
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed
      (canonicalSpatialProjection point)

/-- Every matching contact has the complete nine-channel zero fiber at its
own action origin. -/
theorem fixedP506L0CompleteJointActionMatchingContact_residual_origin_zero
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (fixedP506L0CompleteJointActionMatchingContact point) 0 =
      0 := by
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  exact
    fixedP506L0FinalCommonActionResidual_zero
      (canonicalSpatialProjection point)

/-- The whole-carrier assembly seam generated after evaluating the one global
actual and its matching source/action contact. -/
def fixedP506L0CompleteJointActionSpacetimeAssemblySeam
    (point : BasePoint) : CompleteJointActionJetAssemblySeam :=
  completeJointActionJetAssemblySeam
    (generatedDiracDualFormNativePointwiseActionJet
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionActual point)
    (generatedDiracDualFormNativePointwiseActionJet
      positiveSmoothUnifiedSource
      (fixedP506L0CompleteJointActionMatchingContact point)
      (completeJointActionMatchingContactPoint point))

/-- The fixed P506/L0 whole-section seam has no P286 curvature component.
This is inherited from the source/current-only connection-preserving write,
not obtained by solving a residual coordinate. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_gaugeCurvature_zero
    (point : BasePoint) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
      ).gaugeCurvature = 0 := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_assemblySeam_gaugeCurvature_zero
      positiveSmoothUnifiedSource FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth point

/-- The fixed P506/L0 whole-section seam also has no gravity-auxiliary
exterior-covariant-derivative component.  This is the fixed-lineage
specialization of the generic computed-`II+` transport theorem. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
    (point : BasePoint) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_assemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
      positiveSmoothUnifiedSource FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth point

/-- Fixed-lineage whole-section action-jet naturality.  The statement ranges
over every spacetime occurrence at once and lists all diagonal assembly
responsibility through one typed seam. -/
theorem fixedP506L0CompleteJointActionSpacetimeSection_actionJet_naturality
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionActual point =
      pointwiseActionJetWithCompleteJointAssemblySeam
        (generatedDiracDualFormNativePointwiseActionJet
          positiveSmoothUnifiedSource
          (fixedP506L0CompleteJointActionMatchingContact point)
          (completeJointActionMatchingContactPoint point))
        (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point) := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_actionJet_naturality
      positiveSmoothUnifiedSource FixedInput point

/-- On the canonical time-zero slice, every matching contact is read exactly
at the action origin and therefore has the already generated nine-channel
zero fiber. -/
theorem fixedP506L0CompleteJointActionMatchingContact_timeZero_zeroFiber
    (space : StageNineSpatialPoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      (fixedP506L0CompleteJointActionMatchingContact
        (canonicalCauchySlicePoint 0 space))
      (completeJointActionMatchingContactPoint
        (canonicalCauchySlicePoint 0 space)) := by
  change
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (fixedP506L0CompleteJointActionMatchingContact
          (canonicalCauchySlicePoint 0 space))
        (completeJointActionMatchingContactPoint
          (canonicalCauchySlicePoint 0 space)) = 0
  rw [completeJointActionMatchingContactPoint,
    canonicalTimeProjection_slice, canonicalCauchySlicePoint_zero_zero_local]
  exact
    fixedP506L0CompleteJointActionMatchingContact_residual_origin_zero
      (canonicalCauchySlicePoint 0 space)

/-- Closing the internally generated seam on the time-zero slice transports
the entire nine-channel zero fiber in one step.  This theorem is a downstream
readout; the seam-zero proof remains the next action-naturality obligation. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_timeZero_zeroFiber_of_seam_zero
    (space : StageNineSpatialPoint)
    (seamZero :
      fixedP506L0CompleteJointActionSpacetimeAssemblySeam
          (canonicalCauchySlicePoint 0 space) = 0) :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionActual
      (canonicalCauchySlicePoint 0 space) := by
  apply
    (onDiracDualFormNativePointwiseJointZeroFiber_iff_of_generatedActionJet_eq
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionActual
      (fixedP506L0CompleteJointActionMatchingContact
        (canonicalCauchySlicePoint 0 space))
      (canonicalCauchySlicePoint 0 space)
      (completeJointActionMatchingContactPoint
        (canonicalCauchySlicePoint 0 space))
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_actionJet_eq_contact_of_seam_zero
        positiveSmoothUnifiedSource FixedInput
        (canonicalCauchySlicePoint 0 space) seamZero)).2
  exact fixedP506L0CompleteJointActionMatchingContact_timeZero_zeroFiber space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
