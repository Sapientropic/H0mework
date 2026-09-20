import H0mework.Physics.JointVariation.SectionOperator
import H0mework.Physics.ElectricJoint.ElectricECOccurrenceOperator

/-!
# Whole-action-jet naturality of the live-electric EC global write

The full-occurrence global operator is one source/current-only write.  At
each spacetime point its nine primitive values are the local-origin values of
the same five-leg action contact.  This module compares the two complete
mother-action jets once, on the whole carrier.

The comparison reuses the exhaustive eight-coordinate assembly-seam carrier:
only derived jet data can differ.  The seam is computed after both jets exist
and never enters the global constructor.  Hence this module neither produces
a sector-local world nor reconstructs a correction from residual support.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-! ## Exhaustive whole-carrier seam -/

/-- The complete derived-jet difference between the one global write and
the matching action-generated contact.  It is a diagnostic read of two
already generated jets. -/
def completeJointLiveElectricECFullOccurrenceAssemblySeam
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    CompleteJointActionJetAssemblySeam :=
  completeJointActionJetAssemblySeam
    (generatedDiracDualFormNativePointwiseActionJet source
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
        source current) point)
    (completeJointLiveElectricECFullOccurrenceActionJet
      source current point)

/-- The action jet of the one global write is exactly the matching contact
jet plus the exhaustive assembly seam.  All primitive values and both
connection values agree literally; no field-specific transporter is needed.
-/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_actionJet_naturality
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
          source current) point =
      pointwiseActionJetWithCompleteJointAssemblySeam
        (completeJointLiveElectricECFullOccurrenceActionJet
          source current point)
        (completeJointLiveElectricECFullOccurrenceAssemblySeam
          source current point) := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointLiveElectricECFullOccurrenceAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary_at
          source current point
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_multiplier_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointLiveElectricECFullOccurrenceAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeAuxiliary_at
          source current point
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointLiveElectricECFullOccurrenceAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointLiveElectricECFullOccurrenceAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_at
          source current point
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at
        source current point
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection_at
        source current point
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointLiveElectricECFullOccurrenceAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointLiveElectricECFullOccurrenceAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointLiveElectricECFullOccurrenceAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointLiveElectricECFullOccurrenceAssemblySeam,
      completeJointActionJetAssemblySeam]

/-- A zero internally generated assembly seam turns whole-carrier
naturality into literal equality with the matching action contact.  The zero
proof is a downstream acceptance premise, not input to the global write. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_actionJet_eq_contact_of_assemblySeam_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (seamZero :
      completeJointLiveElectricECFullOccurrenceAssemblySeam
        source current point = 0) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
          source current) point =
      completeJointLiveElectricECFullOccurrenceActionJet
        source current point := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_actionJet_naturality,
    seamZero,
    pointwiseActionJetWithCompleteJointAssemblySeam_zero]

/-- Under the same exhaustive seam closure, the complete nine-channel
residual of the global write is the local-origin residual of the matching
five-leg contact.  This transports an already generated contact settlement
in one step and does not produce either side. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_residual_eq_contact_of_assemblySeam_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (seamZero :
      completeJointLiveElectricECFullOccurrenceAssemblySeam
        source current point = 0) :
    diracDualFormNativePointwiseJointResidual source
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
          source current) point =
      diracDualFormNativePointwiseJointResidual source
        (completeJointLiveElectricECFullOccurrenceContact
          source current point) 0 := by
  exact
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      source
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
        source current)
      (completeJointLiveElectricECFullOccurrenceContact source current point)
      point 0
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobal_actionJet_eq_contact_of_assemblySeam_zero
        source current point seamZero)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
