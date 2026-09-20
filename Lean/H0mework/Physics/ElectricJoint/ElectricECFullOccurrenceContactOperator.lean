import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Live-electric Einstein--Cartan full-occurrence contact

This module upgrades the existing full-occurrence contact to the authoritative
live-electric five-leg action followed by its Einstein--Cartan leg.  One
spacetime occurrence canonically recenters the supplied current, and the same
source/current-only action operator then generates one local contact actual.

The accompanying action jet is a readout at that generated contact's local
origin.  Neither constructor accepts a residual, support, seam, target field,
branch, equation receipt, or realization witness.  This module deliberately
does not construct the later jet-faithful global actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality

noncomputable section

set_option autoImplicit false

/-! ## Generic source/current-only occurrence action -/

/-- Recenter one current at a physical occurrence and run the authoritative
live-electric complete-joint action together with its Einstein--Cartan leg.
The occurrence selects only where the same current is read; it does not select
a residual branch or a target field. -/
def completeJointLiveElectricECFullOccurrenceContact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
    source (fullyRecenterHolonomicConfiguration current contact)

/-- The occurrence contact is definitionally the authoritative action write
applied to the canonical recentering of the same supplied current. -/
theorem completeJointLiveElectricECFullOccurrenceContact_eq_actionWrite
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    completeJointLiveElectricECFullOccurrenceContact source current contact =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        source (fullyRecenterHolonomicConfiguration current contact) :=
  rfl

/-- At the base occurrence the contact is exactly a restart of the same
source-owned five-leg action on the supplied current. -/
@[simp] theorem completeJointLiveElectricECFullOccurrenceContact_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLiveElectricECFullOccurrenceContact source current 0 =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        source current := by
  rw [completeJointLiveElectricECFullOccurrenceContact,
    fullyRecenterHolonomicConfiguration_zero]

/-- The point value consumed at the recentered origin is the value of the
same current at the selected physical occurrence. -/
theorem completeJointLiveElectricECFullOccurrenceInput_pointField_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    toContinuumPointField
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      toContinuumPointField current contact :=
  fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
    current contact

/-- Before the five-leg write, the complete mother-action jet at the local
origin is the action jet of the same source/current at the selected occurrence.
This is provenance transport, not an equation or zero-fiber premise. -/
theorem completeJointLiveElectricECFullOccurrenceInput_actionJet_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      generatedDiracDualFormNativePointwiseActionJet source current contact :=
  generatedActionJet_fullyRecenter_origin_unconditional source current contact

/-- Read the complete mother-action jet at the local origin of the generated
live-electric Einstein--Cartan occurrence contact. -/
def completeJointLiveElectricECFullOccurrenceActionJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet source
    (completeJointLiveElectricECFullOccurrenceContact source current contact) 0

/-- The occurrence action jet is a downstream read of the actual produced by
the same source/current-only action write. -/
theorem completeJointLiveElectricECFullOccurrenceActionJet_eq_generated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    completeJointLiveElectricECFullOccurrenceActionJet source current contact =
      generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
          source (fullyRecenterHolonomicConfiguration current contact)) 0 :=
  rfl

@[simp] theorem completeJointLiveElectricECFullOccurrenceActionJet_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLiveElectricECFullOccurrenceActionJet source current 0 =
      generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
          source current) 0 := by
  rw [completeJointLiveElectricECFullOccurrenceActionJet,
    completeJointLiveElectricECFullOccurrenceContact_zero]

/-! ## Fixed P506/L0 specialization on the current final actual -/

/-- The fixed P506/L0 occurrence contact is generated from the positive source
and the current authoritative live-electric Einstein--Cartan actual `U5`.
The occurrence remains a read index, not a branch choice. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointLiveElectricECFullOccurrenceContact positiveSmoothUnifiedSource
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact

theorem fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact_provenance
    (contact : BasePoint) :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact contact =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration
          fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact) :=
  rfl

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact_zero :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact 0 =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual := by
  exact completeJointLiveElectricECFullOccurrenceContact_zero _ _

/-- Fixed-lineage readout of the action jet generated at the occurrence
contact. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceActionJet
    (contact : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  completeJointLiveElectricECFullOccurrenceActionJet
    positiveSmoothUnifiedSource
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact

theorem fixedP506L0CompleteJointLiveElectricECFullOccurrenceActionJet_provenance
    (contact : BasePoint) :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceActionJet contact =
      generatedDiracDualFormNativePointwiseActionJet positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
          positiveSmoothUnifiedSource
          (fullyRecenterHolonomicConfiguration
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact))
        0 :=
  rfl

/-- The input action jet used by the fixed occurrence write keeps the exact
positive-source/U5 occurrence provenance. -/
theorem fixedP506L0CompleteJointLiveElectricECFullOccurrenceInput_actionJet_origin
    (contact : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration
          fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact)
        0 =
      generatedDiracDualFormNativePointwiseActionJet positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual contact :=
  completeJointLiveElectricECFullOccurrenceInput_actionJet_origin _ _ _

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
