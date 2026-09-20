import H0mework.Physics.ConstitutiveAction.SpatialSectionAlgebraicClosure

/-!
# Joint residual of the constitutive spatial section

The spatial section is generated before this module.  We now substitute that
single global actual into the authoritative nine-coordinate residual.  The
first non-algebraic computation keeps the exact mixed-jet responsibility:
the gravity-auxiliary coordinate is the difference between the literal
curvature of the assembled section and the curvature of the matching
action-generated contact actual.

This residual is diagnostic only.  No coordinate, sign, support branch, or
curvature seam is consumed by an action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionAlgebraicClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Generated time-zero Cauchy values -/

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem canonicalSpatialContactTranslation_zero
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  simpa only [canonicalCauchySlicePoint_zero_zero] using
    canonicalSpatialContactTranslation_timeAxis space 0

theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityConnection_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).gravityConnection (canonicalCauchySlicePoint 0 space) =
      current.gravityConnection (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeConstitutiveJointActionResponseOperator_gravityConnection_zero]
  exact congrArg current.gravityConnection
    (canonicalSpatialContactTranslation_zero space)

theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) := by
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeConstitutiveJointActionResponseOperator_gravityAuxiliary]
  simp [spatiallyRecenterHolonomicConfiguration]

/-- Whenever the input current is already simple, the assembled section's
gravity auxiliary is literally the same whole spacetime field.  This is a
field identity, so its first jet may be recomputed by rewriting rather than
transported from a contact receipt. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation current) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).gravityAuxiliary =
      current.gravityAuxiliary := by
  funext point
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary
      source current point]
  exact (simplicity point).symm

theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).matter (canonicalCauchySlicePoint 0 space) =
      current.matter (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeConstitutiveJointActionResponseOperator_matter_zero]
  exact congrArg current.matter
    (canonicalSpatialContactTranslation_zero space)

theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      current.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeConstitutiveJointActionResponseOperator_conjugateMatter_zero]
  exact congrArg current.conjugateMatter
    (canonicalSpatialContactTranslation_zero space)

/-! ## Lorentz channel on the generated slice -/

/-- The Lorentz residual of the assembled section on its generated
time-zero slice is the literal Lorentz residual of the input current at that
same point.  The proof uses the whole-field auxiliary equality and the
same-slice primitive values; it does not transport a zero receipt. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_lorentzResidual_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation current)
    (space : StageNineSpatialPoint) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicFormNativeLorentzEulerThreeForm source 0 current
        (canonicalCauchySlicePoint 0 space) := by
  let output :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current
  let point := canonicalCauchySlicePoint 0 space
  have auxiliaryEquality :
      output.gravityAuxiliary = current.gravityAuxiliary :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_eq_current
      source current simplicity
  have connectionEquality :
      output.gravityConnection point = current.gravityConnection point :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityConnection_zeroSlice
      source current space
  have covariantDerivativeEquality :
      holonomicGravityAuxiliaryExteriorCovariantDerivative output point =
        holonomicGravityAuxiliaryExteriorCovariantDerivative current point := by
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [auxiliaryEquality, connectionEquality]
  have coframeEquality :
      output.coframe point = current.coframe point :=
    congrFun
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
        source current)
      point
  have matterEquality :
      output.matter point = current.matter point :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
      source current space
  have conjugateMatterEquality :
      output.conjugateMatter point = current.conjugateMatter point :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
      source current space
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at source
      output current point coframeEquality matterEquality
      conjugateMatterEquality
  have spinEquality :
      formNativeMatterSpinThreeForm source 0 point
          (toContinuumPointField output point) =
        formNativeMatterSpinThreeForm source 0 point
          (toContinuumPointField current point) := by
    unfold diracDualFormNativeActionSpinResponseAt
      formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
    exact neg_injective physicalSpinEquality
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [covariantDerivativeEquality, spinEquality]

private theorem
    fixedP506FormNativeJointActionSolvedSuccessor_simplicity :
    FormNativeGravitySimplicityEquation
      FixedP506FormNativeJointActionSolvedSuccessor := by
  unfold FixedP506FormNativeJointActionSolvedSuccessor
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      positiveSmoothUnifiedSource _

/-- Fixed-lineage fourth-channel normal form.  Any nonzero Lorentz support
belongs to the already generated input current and is merely read here; this
equality does not select a connection write. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_lorentzConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).lorentzConnection =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) := by
  exact
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_lorentzResidual_zeroSlice
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_simplicity space

/-- Exact gravity-auxiliary coordinate of the already generated global
section.  Contact reaction cancellation removes the algebraic terms, leaving
only the honest global/contact curvature seam. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliaryResidual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField
          (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
            source current)
          (canonicalCauchySlicePoint time space)) =
      holonomicContravariantGravityCurvature
          (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
            source current)
          (canonicalCauchySlicePoint time space) -
        holonomicContravariantGravityCurvature
          (diracDualFormNativeConstitutiveJointActionResponseOperator source
            (spatiallyRecenterHolonomicConfiguration current space))
          (canonicalCauchySlicePoint time 0) := by
  let contact :=
    diracDualFormNativeConstitutiveJointActionResponseOperator source
      (spatiallyRecenterHolonomicConfiguration current space)
  have contactZero :
      formNativeGravityAuxiliaryEulerResidual
          (toContinuumPointField contact
            (canonicalCauchySlicePoint time 0)) =
        0 :=
    congrFun
      (diracDualFormNativeConstitutiveJointActionResponseOperator_auxiliaryEquation
        source
        (spatiallyRecenterHolonomicConfiguration current space))
      (canonicalCauchySlicePoint time 0)
  change
    holonomicContravariantGravityCurvature
          (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
            source current)
          (canonicalCauchySlicePoint time space) -
        gravityInternalDualEquiv
          ((diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
            source current).gravityAuxiliary
              (canonicalCauchySlicePoint time space)) +
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
          source current).gravitySimplicityMultiplier
            (canonicalCauchySlicePoint time space) =
      _
  change
    holonomicContravariantGravityCurvature contact
          (canonicalCauchySlicePoint time 0) -
        gravityInternalDualEquiv
          (contact.gravityAuxiliary (canonicalCauchySlicePoint time 0)) +
        contact.gravitySimplicityMultiplier
          (canonicalCauchySlicePoint time 0) =
      0 at contactZero
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_multiplier_slice]
  dsimp only [contact] at contactZero
  linear_combination contactZero

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint time space)).gravityAuxiliary =
      holonomicContravariantGravityCurvature
          FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
          (canonicalCauchySlicePoint time space) -
        holonomicContravariantGravityCurvature
          (diracDualFormNativeConstitutiveJointActionResponseOperator
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration
              FixedP506FormNativeJointActionSolvedSuccessor space))
          (canonicalCauchySlicePoint time 0) := by
  exact
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliaryResidual
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor time space

/-! ## Three-channel carrier checkpoint -/

/-- The current section-level normal form on the generated time-zero slice.
The multiplier and P286 auxiliary channels are settled; the gravity
auxiliary channel retains the exact global/contact curvature seam.  The
other six coordinates remain literal readouts of this same section actual.

This carrier is diagnostic only.  In particular, the curvature difference
is not negated or fed to any action write. -/
def
    fixedP506FormNativeConstitutiveJointActionSpatialSectionThreeChannelResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  { fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      point with
    gravityMultiplier := 0
    gravityAuxiliary :=
      holonomicContravariantGravityCurvature
          FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
          point -
        holonomicContravariantGravityCurvature
          (diracDualFormNativeConstitutiveJointActionResponseOperator
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration
              FixedP506FormNativeJointActionSolvedSuccessor space))
          (canonicalCauchySlicePoint 0 0)
    p286GaugeAuxiliary := 0 }

/-- One equality records all three currently computed channels without
altering any of the six still-open differential coordinates. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_zeroSlice_threeChannelNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSpatialSectionThreeChannelResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
        0 space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
        space
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Four-channel extension of the same diagnostic carrier.  The Lorentz
coordinate is not forced to zero: it is exposed as the literal current
readout that the section preserves on the generated slice. -/
def
    fixedP506FormNativeConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSpatialSectionThreeChannelResidualZeroSliceNormalForm
      space with
    lorentzConnection :=
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) }

/-- The fourth computed coordinate is assembled with the original three in
one same-actual carrier equality. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_zeroSlice_fourChannelNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
        0 space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_lorentzConnection_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionResidual
