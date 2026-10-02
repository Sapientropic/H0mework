import H0mework.Versions.R2.Physics.SourceFormation.Equations
import H0mework.Versions.R2.Physics.SourceFamily.OccurrenceReadout

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation

open StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGravityBianchi
open StageNineDiracDualFormNativeJointResidualCarrier StageNineCClassicalWorldAcceptance
open StageNineDynamicBreakingVacuum StageNineGlobalBundle

noncomputable section

theorem source_clock_eq (source : SmoothUnifiedSource) :
    MotherFamilyOccurrence.sourceClock source = SourceFamily.clock (index source) := by
  unfold MotherFamilyOccurrence.sourceClock SourceFamily.clock
  rw [source_coupling]

theorem source_phase_eq (source : SmoothUnifiedSource) :
    MotherFamilyOccurrence.sourcePhaseRate source = SourceFamily.phaseRate (index source) := by
  unfold MotherFamilyOccurrence.sourcePhaseRate SourceFamily.phaseRate
  rw [source_clock_eq]

theorem material_field_eq (source : SmoothUnifiedSource) :
    formedField source = MotherFamilyOccurrence.materialField source := by
  unfold formedField seed SourceFamily.seedAt MotherFamilyOccurrence.materialField
  rw [source_clock_eq, source_phase_eq]

theorem material_joint_zero (source : SmoothUnifiedSource) :
    DiracDualFormNativeJointZeroFiber source (MotherFamilyOccurrence.materialField source) := by
  rw [← material_field_eq]
  exact joint_zero source

/-- The history's existing material-field producer realizes every raw
source in its own full equations. Sector presence is a separate readout. -/
theorem material_realization (source : SmoothUnifiedSource) :
    (MotherFamilyOccurrence.materialField source).Smooth ∧
      (MotherFamilyOccurrence.materialField source).Nondegenerate ∧
      GravityConnectionLorentzAdmissible (MotherFamilyOccurrence.materialField source) ∧
      DiracDualFormNativeJointZeroFiber source (MotherFamilyOccurrence.materialField source) ∧
      DynamicScalarSourceContactAtOrigin source (MotherFamilyOccurrence.materialField source) := by
  rw [← material_field_eq]
  refine ⟨field_smooth source, field_nondegenerate source, lorentz_admissible source, joint_zero source, ?_⟩
  unfold DynamicScalarSourceContactAtOrigin
  rw [scalar_eq, generatedLocalVacuumCoordinates, generatedScalarFrame,
    generatedTransition_normalized, scalarCoordinateAction_one]

theorem material_original : MotherFamilyOccurrence.materialField Runtime.source = Runtime.configuration := by
  exact (material_field_eq Runtime.source).symm.trans field_original

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation
