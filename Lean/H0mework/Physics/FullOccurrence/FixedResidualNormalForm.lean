import H0mework.Physics.ElectricJoint.ElectricECOccurrenceNaturality
import H0mework.Physics.ElectricEC.FixedFullOccurrenceOriginSettlement

/-!
# Fixed P506/L0 residual of the full-occurrence joint global write

The source/current-only full-occurrence global operator has already produced
one four-dimensional actual.  Its whole action jet differs from the matching
five-leg contact by one exhaustive assembly seam.  This module connects that
global producer directly to the contact-origin settlement on the complete
nine-channel carrier.

No residual coordinate or seam enters the constructor.  A seam-zero
hypothesis below is only the exact downstream condition under which the
already generated contact read transports to the already generated global
actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalResidualNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceOriginSettlement
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Global : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

/-- Fixed-lineage specialization of the internally generated whole-action
assembly seam. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
    (point : BasePoint) :
    StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator.CompleteJointActionJetAssemblySeam :=
  completeJointLiveElectricECFullOccurrenceAssemblySeam
    Source Current point

/-- Simplicity is already closed on the global actual independently of any
derived-jet assembly seam. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityMultiplier_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Global point
      ).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField Global point) =
      0
  exact
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_simplicity
        Source Current point)

/-- One simultaneous normal form for the residual of the global actual.
When the exhaustive action-jet seam closes, the entire nine-channel read is
the already computed matching-contact support. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_pointwiseJointResidual_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (assemblySeamZero :
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
          (canonicalCauchySlicePoint time space) =
        0) :
    diracDualFormNativePointwiseJointResidual Source Global
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
        (canonicalCauchySlicePoint time space)).asJointResidual := by
  calc
    diracDualFormNativePointwiseJointResidual Source Global
          (canonicalCauchySlicePoint time space) =
        diracDualFormNativePointwiseJointResidual Source
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            (canonicalCauchySlicePoint time space)) 0 := by
      exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_residual_eq_contact_of_assemblySeam_zero
          Source Current (canonicalCauchySlicePoint time space)
          assemblySeamZero
    _ =
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
          (canonicalCauchySlicePoint time space)).asJointResidual :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_originResidual_normalForm
        time space inDomain

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalResidualNormalForm
