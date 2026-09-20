import H0mework.Physics.FixedJoint.FixedConstitutiveSectionResidual

/-!
# Fixed P506/L0 constitutive differential residual section

The preceding module settles the three algebraic channels and substitutes the
actual P286 auxiliary first jet on the complete generated time-zero slice.
This module continues the same readback through the differential channels.

The fixed-lineage fields are compared directly with the already generated
KIN-16 primitive diagonal on that slice.  This is a diagnostic calculation
only.  No residual coordinate, sign, support, or branch is accepted by an
action write in this module.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineIIPlusRestriction
open StageNineMatterPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineTopologicalFourFormPairing
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev ConstitutiveActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private abbrev PrimitiveActual : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-! ## Exact fixed-lineage slice seams -/

/-- The constitutive successor retains the explicit KIN-16 identity/zero
coframe jet at every point of the generated time-zero slice. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt ConstitutiveActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

/-- The temporal primal action write is faithful on the whole canonical
time-zero slice, so the constitutive successor and KIN-16 primitive have the
same matter value there. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    ConstitutiveActual.matter (canonicalCauchySlicePoint 0 space) =
      PrimitiveActual.matter (canonicalCauchySlicePoint 0 space) := by
  have primalSlice :=
    congrArg
      (fun state : StageNineCauchyState => state.matter space)
      (canonicalCauchyRestriction_zero_actionGeneratedCurrentCoframeMatterTimeResponseActual
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
  change
    (actionGeneratedCurrentCoframeMatterTimeResponseActual
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
      ).matter (canonicalCauchySlicePoint 0 space) =
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.matter
      (canonicalCauchySlicePoint 0 space) at primalSlice
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_matter,
    fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual.matter
        (canonicalCauchySlicePoint 0 space) =
      PrimitiveActual.matter (canonicalCauchySlicePoint 0 space)
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
  rw [currentP286CompleteActionResponseOperator_matter,
    fixedGlobalMatterDualFullCauchy_matter]
  unfold fixedGlobalPrimalMatterWrittenActual
  rw [primalSlice]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]

/-- The independent adjoint action write is likewise faithful on the same
time-zero slice. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    ConstitutiveActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      PrimitiveActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  have dualSlice :=
    congrArg
      (fun state : StageNineCauchyState => state.conjugateMatter space)
      (canonicalCauchyRestriction_zero_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
        fixedGlobalPrimalMatterWrittenActual)
  change
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      fixedGlobalPrimalMatterWrittenActual).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      fixedGlobalPrimalMatterWrittenActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) at dualSlice
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter,
    fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      PrimitiveActual.conjugateMatter (canonicalCauchySlicePoint 0 space)
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
  rw [currentP286CompleteActionResponseOperator_conjugateMatter,
    fixedGlobalMatterDualFullCauchy_conjugateMatter]
  unfold fixedGlobalMatterDualWrittenActual
  rw [dualSlice]
  unfold fixedGlobalPrimalMatterWrittenActual
  rw [actionGeneratedCurrentCoframeMatterTimeResponseActual_conjugateMatter]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]

/-- Consequently the physical spin three-form is read from identical
coframe/matter/adjoint data on the generated slice. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_spin_zeroSlice_eq_primitive
    (space : StageNineSpatialPoint) :
    formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField ConstitutiveActual
          (canonicalCauchySlicePoint 0 space)) =
      formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField PrimitiveActual
          (canonicalCauchySlicePoint 0 space)) := by
  have responseEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource ConstitutiveActual PrimitiveActual
      (canonicalCauchySlicePoint 0 space)
      (by
        rw [
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
        have primitiveJet :=
          fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
        exact congrArg PointwiseLorentzianCoframeJet.coframe primitiveJet
          |>.symm)
      (fixedP506FormNativeConstitutiveJointActionSuccessor_matter_zeroSlice
        space)
      (fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_zeroSlice
        space)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at responseEquality
  exact neg_injective responseEquality

/-! ## Lorentz differential support -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_eq_primitive :
    ConstitutiveActual.coframe = PrimitiveActual.coframe := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gravityAuxiliary_eq_primitive :
    ConstitutiveActual.gravityAuxiliary =
      PrimitiveActual.gravityAuxiliary := by
  funext point
  have successorSimplicity :=
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField ConstitutiveActual point)).1
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        point)
  calc
    ConstitutiveActual.gravityAuxiliary point =
        physicalIIPlusBivector (ConstitutiveActual.coframe point) :=
      successorSimplicity
    _ = physicalIIPlusBivector (PrimitiveActual.coframe point) := by
      rw [
        fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_eq_primitive]
    _ = PrimitiveActual.gravityAuxiliary point :=
      (fixedPrimitiveDiagonal_simplicity point).symm

private theorem fixedPrimitiveDiagonal_restrictToIIPlus :
    restrictHolonomicConfigurationToIIPlus PrimitiveActual =
      PrimitiveActual := by
  exact
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      PrimitiveActual).2 fixedPrimitiveDiagonal_simplicity

/-- KIN-16 already closes the Lorentz equation on the complete generated
time-zero slice.  This is the comparison zero used below; it is not a
certificate supplied to the constitutive successor. -/
theorem fixedPrimitiveDiagonal_lorentzEuler_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        PrimitiveActual (canonicalCauchySlicePoint 0 space) =
      0 := by
  apply
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current
      positiveSmoothUnifiedSource 0 PrimitiveActual
      (canonicalCauchySlicePoint 0 space)).2
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative PrimitiveActual
          (canonicalCauchySlicePoint 0 space) =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (restrictHolonomicConfigurationToIIPlus PrimitiveActual)
          (canonicalCauchySlicePoint 0 space) := by
      rw [fixedPrimitiveDiagonal_restrictToIIPlus]
    _ =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (PrimitiveActual.coframe (canonicalCauchySlicePoint 0 space))
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt PrimitiveActual.coframe
                (canonicalCauchySlicePoint 0 space))
              (PrimitiveActual.gravityConnection
                (canonicalCauchySlicePoint 0 space)))) :=
      holonomicGravityAuxiliaryExteriorCovariantDerivative_restrictToIIPlus_eq_torsionCoframe
        PrimitiveActual
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
        fixedPrimitiveDiagonal_lorentzAdmissible
        (canonicalCauchySlicePoint 0 space)
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus PrimitiveActual)
            (canonicalCauchySlicePoint 0 space)) :=
      fixedPrimitiveDiagonal_torsionSpin_zeroSlice space
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField PrimitiveActual
            (canonicalCauchySlicePoint 0 space)) := by
      rw [fixedPrimitiveDiagonal_restrictToIIPlus]

/-- Exact Lorentz support normal form on the generated slice.  Both terms
act on the same source-generated `II+` bivector; the only remaining
difference is the two forward-generated gravity connections. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorLorentzZeroSliceNormalForm
    (space : StageNineSpatialPoint) : PhysicalBivectorThreeForm :=
  let point := canonicalCauchySlicePoint 0 space
  pointwisePhysicalBivectorConnectionExteriorAction
      (ConstitutiveActual.gravityConnection point)
      (physicalIIPlusBivector 1) -
    pointwisePhysicalBivectorConnectionExteriorAction
      (PrimitiveActual.gravityConnection point)
      (physicalIIPlusBivector 1)

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).lorentzConnection =
      fixedP506FormNativeConstitutiveJointActionSuccessorLorentzZeroSliceNormalForm
        space := by
  let point := canonicalCauchySlicePoint 0 space
  have auxiliaryEquality :
      ConstitutiveActual.gravityAuxiliary =
        PrimitiveActual.gravityAuxiliary :=
    fixedP506FormNativeConstitutiveJointActionSuccessor_gravityAuxiliary_eq_primitive
  have exteriorEquality :
      holonomicGravityAuxiliaryExteriorDerivative ConstitutiveActual point =
        holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point := by
    unfold holonomicGravityAuxiliaryExteriorDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [auxiliaryEquality]
  have successorAuxiliaryAt :
      ConstitutiveActual.gravityAuxiliary point =
        physicalIIPlusBivector 1 := by
    rw [auxiliaryEquality]
    exact
      (fixedPrimitiveDiagonal_simplicity point).trans
        (by
          congr 1
          have primitiveJet :=
            fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
          exact congrArg PointwiseLorentzianCoframeJet.coframe primitiveJet)
  have primitiveAuxiliaryAt :
      PrimitiveActual.gravityAuxiliary point =
        physicalIIPlusBivector 1 := by
    exact
      (fixedPrimitiveDiagonal_simplicity point).trans
        (by
          congr 1
          have primitiveJet :=
            fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
          exact congrArg PointwiseLorentzianCoframeJet.coframe primitiveJet)
  have primitiveZero :=
    fixedPrimitiveDiagonal_lorentzEuler_zeroSlice space
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        ConstitutiveActual point =
      fixedP506FormNativeConstitutiveJointActionSuccessorLorentzZeroSliceNormalForm
        space
  unfold holonomicFormNativeLorentzEulerThreeForm at primitiveZero ⊢
  rw [holonomicGravityAuxiliaryExteriorCovariantDerivative_eq_parts]
    at primitiveZero
  change
    holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
          pointwisePhysicalBivectorConnectionExteriorAction
            (PrimitiveActual.gravityConnection point)
            (PrimitiveActual.gravityAuxiliary point) +
        formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
          (toContinuumPointField PrimitiveActual point) =
      0 at primitiveZero
  rw [primitiveAuxiliaryAt] at primitiveZero
  rw [holonomicGravityAuxiliaryExteriorCovariantDerivative_eq_parts,
    exteriorEquality, successorAuxiliaryAt,
    fixedP506FormNativeConstitutiveJointActionSuccessor_spin_zeroSlice_eq_primitive]
  unfold
    fixedP506FormNativeConstitutiveJointActionSuccessorLorentzZeroSliceNormalForm
  change
    holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
          pointwisePhysicalBivectorConnectionExteriorAction
            (ConstitutiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) +
        formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
          (toContinuumPointField PrimitiveActual point) =
      pointwisePhysicalBivectorConnectionExteriorAction
          (ConstitutiveActual.gravityConnection point)
          (physicalIIPlusBivector 1) -
        pointwisePhysicalBivectorConnectionExteriorAction
          (PrimitiveActual.gravityConnection point)
          (physicalIIPlusBivector 1)
  have primitiveBalance :
      holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
          formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
            (toContinuumPointField PrimitiveActual point) =
        -pointwisePhysicalBivectorConnectionExteriorAction
          (PrimitiveActual.gravityConnection point)
          (physicalIIPlusBivector 1) := by
    apply (add_eq_zero_iff_eq_neg).1
    calc
      (holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
            formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
              (toContinuumPointField PrimitiveActual point)) +
          pointwisePhysicalBivectorConnectionExteriorAction
            (PrimitiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) =
        holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
            pointwisePhysicalBivectorConnectionExteriorAction
              (PrimitiveActual.gravityConnection point)
              (physicalIIPlusBivector 1) +
          formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
            (toContinuumPointField PrimitiveActual point) := by
          abel
      _ = 0 := primitiveZero
  calc
    holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
          pointwisePhysicalBivectorConnectionExteriorAction
            (ConstitutiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) +
        formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
          (toContinuumPointField PrimitiveActual point) =
        pointwisePhysicalBivectorConnectionExteriorAction
            (ConstitutiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) +
          (holonomicGravityAuxiliaryExteriorDerivative PrimitiveActual point +
            formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
              (toContinuumPointField PrimitiveActual point)) := by
      abel
    _ =
        pointwisePhysicalBivectorConnectionExteriorAction
            (ConstitutiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) +
          -pointwisePhysicalBivectorConnectionExteriorAction
            (PrimitiveActual.gravityConnection point)
            (physicalIIPlusBivector 1) := by
      rw [primitiveBalance]
    _ = _ := by
      simp [sub_eq_add_neg]

/-- Carrier-level section normal form after resolving the Lorentz channel as
the difference of the two forward-generated connection actions.  The P286
connection channel still uses its already proved actual first-jet form; the
remaining four differential channels remain literal same-actual readouts. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorDifferentialResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSuccessorResidualZeroSliceNormalForm
      space with
    lorentzConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorLorentzZeroSliceNormalForm
        space }

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_differentialNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorDifferentialResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## P286 connection differential support -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate ConstitutiveActual
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) := by
  change
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (canonicalCauchySlicePoint 0 space) =
      _
  have connectionEquality :
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection =
        FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
    simpa only using
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection
  calc
    holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) := by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [connectionEquality]
    _ =
        fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 space) :=
      fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm
        (canonicalCauchySlicePoint 0 space)

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryCoordinate_zeroSlice_explicit
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveAuxiliaryCoordinate
        (canonicalCauchySlicePoint 0 space) =
      c3h181FullAuxiliaryCoordinateNormalForm
        (-(canonicalCauchySlicePoint 0 space)) := by
  rw [fixedP506FormNativeConstitutiveAuxiliaryCoordinate_zeroSlice]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm
      (canonicalCauchySlicePoint 0 space)

/-- Fully explicit primitive/first-jet presentation of the P286 connection
residual on the generated slice.  The last summand is the charged-current
readout of the same actual and action occurrence. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
    (space : StageNineSpatialPoint) : P286GaugeThreeForm :=
  let point := canonicalCauchySlicePoint 0 space
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (fixedP506FormNativeJointActionSolvedConnectionNormalForm point)
      (c3h181FullAuxiliaryCoordinateNormalForm (-point))
      (fun direction =>
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection direction)) +
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField ConstitutiveActual point)

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeConnection =
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space := by
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_normalForm]
  unfold
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
  dsimp only [ConstitutiveActual]
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_zeroSlice,
    fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryCoordinate_zeroSlice_explicit]

/-- Joint connection-support carrier: three algebraic zeros plus the exact
Lorentz and P286 connection normal forms, all on the same actual. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorConnectionResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSuccessorDifferentialResidualZeroSliceNormalForm
      space with
    p286GaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space }

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_connectionNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorConnectionResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
        space
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Scalar differential support -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_scalar_vacuum :
    ConstitutiveActual.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
    fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_volume_zeroSlice
    (space : StageNineSpatialPoint) :
    generatedVolumeDensity
        (toContinuumPointField ConstitutiveActual
          (canonicalCauchySlicePoint 0 space)) =
      1 := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  norm_num

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_scalarPotential_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField ConstitutiveActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField ConstitutiveActual
      (canonicalCauchySlicePoint 0 space)).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun
      fixedP506FormNativeConstitutiveJointActionSuccessor_scalar_vacuum
      (canonicalCauchySlicePoint 0 space)]
  simp

/-- Exact scalar support after removing the already settled volume and
vacuum-potential factors.  No term here is used as a write coefficient. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  scalarGaugeConnectionKineticFirstVariationDensity
      positiveSmoothUnifiedSource 0 point
      (toContinuumPointField ConstitutiveActual point)
      (holonomicScalarVariationAlgebraicDirection ConstitutiveActual direction
        point) +
    diracDualScalarYukawaFirstVariationDensity
      (toContinuumPointField ConstitutiveActual point) direction -
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
      ConstitutiveActual direction point

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).scalar =
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource ConstitutiveActual direction
          (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space direction
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    diracDualScalarAlgebraicDirectionalCoefficient
    fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_volume_zeroSlice,
    fixedP506FormNativeConstitutiveJointActionSuccessor_scalarPotential_zeroSlice]
  ring

/-- Carrier normal form with both connection channels and the scalar channel
resolved on the same generated slice. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorConnectionScalarResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSuccessorConnectionResidualZeroSliceNormalForm
      space with
    scalar :=
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space }

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_connectionScalarNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorConnectionScalarResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl

/-! ## Primal and adjoint matter differential support -/

/-- Matter support after removing the already settled unit volume on the
generated slice. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorMatterZeroSliceNormalForm
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) : ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  (ConstitutiveActual.conjugateMatter point
      (diracDualMatterAlgebraicVariationVector positiveSmoothUnifiedSource
        ConstitutiveActual direction point)).re -
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
      ConstitutiveActual direction point

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_matter_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).matter =
      fixedP506FormNativeConstitutiveJointActionSuccessorMatterZeroSliceNormalForm
        space := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource ConstitutiveActual direction
          (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorMatterZeroSliceNormalForm
        space direction
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
    diracDualMatterAlgebraicDirectionalCoefficient
    fixedP506FormNativeConstitutiveJointActionSuccessorMatterZeroSliceNormalForm
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_volume_zeroSlice]
  ring

/-- Adjoint support on the same unit-volume slice. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorConjugateMatterZeroSliceNormalForm
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) : ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  (matterDualOfCoordinates direction
    (generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0
      point (toContinuumPointField ConstitutiveActual point))).re

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_conjugateMatter_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).conjugateMatter =
      fixedP506FormNativeConstitutiveJointActionSuccessorConjugateMatterZeroSliceNormalForm
        space := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        ConstitutiveActual direction (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorConjugateMatterZeroSliceNormalForm
        space direction
  unfold diracDualConjugateMatterDirectionalCoefficient
    fixedP506FormNativeConstitutiveJointActionSuccessorConjugateMatterZeroSliceNormalForm
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_volume_zeroSlice]
  ring

/-! ## Coframe differential support -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_physicalIIPlusCoframeTangent_smul
    (coframe variation : LorentzianCoframe) (parameter : ℝ) :
    physicalIIPlusCoframeTangent coframe (parameter • variation) =
      parameter • physicalIIPlusCoframeTangent coframe variation := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

/-- The direct `II+` constraint reaction packaged in the same continuous
coframe-dual carrier as the other two action-generated coframe legs. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorCoframeConstraintReactionCovector
    (space : StageNineSpatialPoint) :
    LorentzianCoframe →L[ℝ] ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField ConstitutiveActual point
  ({ toFun := fun variation =>
      formNativeCoframeConstraintReaction field variation
     map_add' := by
       intro first second
       unfold formNativeCoframeConstraintReaction
       rw [physicalIIPlusCoframeTangent_add,
         gravityTopologicalWedgeCoefficient_add_right]
     map_smul' := by
       intro parameter variation
       unfold formNativeCoframeConstraintReaction
       rw [
         fixedP506FormNativeConstitutiveJointActionSuccessor_physicalIIPlusCoframeTangent_smul,
         gravityTopologicalWedgeCoefficient_smul_right]
       rfl } : LorentzianCoframe →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- Exact coframe support generated by the authoritative form-native action:
gauge constitutive response plus matter response minus the direct constraint
reaction, all read from the same constitutive actual. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorCoframeZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    LorentzianCoframe →L[ℝ] ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField ConstitutiveActual point
  diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      field +
    diracDualFormNativeCoframeMatterEulerCovector positiveSmoothUnifiedSource
      point field -
    fixedP506FormNativeConstitutiveJointActionSuccessorCoframeConstraintReactionCovector
      space

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_coframe_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).coframe =
      fixedP506FormNativeConstitutiveJointActionSuccessorCoframeZeroSliceNormalForm
        space := by
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField ConstitutiveActual point
  have nondegenerate : Matrix.det field.coframe ≠ 0 := by
    change Matrix.det
      (ConstitutiveActual.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0
    rw [
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
    norm_num
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource
        point field =
      fixedP506FormNativeConstitutiveJointActionSuccessorCoframeZeroSliceNormalForm
        space
  apply ContinuousLinearMap.ext
  intro variation
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      positiveSmoothUnifiedSource point field nondegenerate variation]
  simp [
    fixedP506FormNativeConstitutiveJointActionSuccessorCoframeZeroSliceNormalForm,
    fixedP506FormNativeConstitutiveJointActionSuccessorCoframeConstraintReactionCovector,
    point, field]

/-! ## Complete generated-slice residual support -/

/-- Complete nine-channel residual normal form on the fixed P506/L0
generated slice.  This carrier is diagnostic: none of its coordinates or
support branches is an input to an action write. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorFullResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSuccessorConnectionScalarResidualZeroSliceNormalForm
      space with
    matter :=
      fixedP506FormNativeConstitutiveJointActionSuccessorMatterZeroSliceNormalForm
        space
    conjugateMatter :=
      fixedP506FormNativeConstitutiveJointActionSuccessorConjugateMatterZeroSliceNormalForm
        space
    coframe :=
      fixedP506FormNativeConstitutiveJointActionSuccessorCoframeZeroSliceNormalForm
        space }

/-- One carrier equality accounts for all nine residual channels of the
same source/action-generated actual on every point of the canonical
time-zero slice. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_fullNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorFullResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_matter_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_conjugateMatter_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_coframe_zeroSlice_normalForm
        space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
