import H0mework.Physics.ConstitutiveAction.SpatialSectionGaugeClosure
import H0mework.Physics.FixedJoint.FixedJointResidual

/-!
# Algebraic residual closure of the constitutive spatial section

The section actual is generated before this module.  Here its algebraic
gravity-simplicity channel is read directly from the same contactwise EC
operator, and the already proved global constitutive P286 channel is inserted
into the complete joint residual carrier.

The remaining channels are left literal.  No residual field or support
coordinate is consumed by an action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionAlgebraicClosure

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- Contactwise simplicity assembles to one pointwise simplicity law for the
single global section actual. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current) := by
  intro point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe_slice]
  exact
    diracDualFormNativeConstitutiveJointActionResponseOperator_simplicity
      source
      (spatiallyRecenterHolonomicConfiguration current
        (canonicalSpatialProjection point))
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_simplicity :
    FormNativeGravitySimplicityEquation
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor :=
  diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_simplicity
    positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

/-- Complete joint residual section of the new action-generated global
section.  The definition occurs only after the producer exists. -/
def fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      point).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
          point) =
      0
  apply
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
        point)).2
  exact
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_simplicity
      point

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary =
      0 := by
  exact
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryResidual_zero
      space

/-- Two independently action-generated algebraic channels are closed on the
same new section actual.  This is a downstream readout, not a constructor. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSection_algebraic_regression
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).gravityMultiplier =
        0 ∧
      (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary =
        0 := by
  exact
    ⟨fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
        _,
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
        space⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionAlgebraicClosure
