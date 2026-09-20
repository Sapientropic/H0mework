import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286ZeroSliceCompatibility

/-!
# Fixed P506/L0 P286 zero-slice exterior continuity

The fixed zero-slice anchor is the canonical constitutive auxiliary pulled
back along the generated zero-slice projection.  This module transports the
canonical live-input regularity through that pullback and proves continuity
of all four exterior-derivative components at the common occurrence.

No required profile, residual coordinate, support branch, target field, or
zero-fiber receipt enters the proof.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceContinuity

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageNineCanonicalRestrictionP286CoherentRegularity
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286HolonomicSecondJetCarrier
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedZeroSliceContinuityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fixedZeroSliceContinuityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fixedZeroSliceContinuityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev FixedCanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev FixedCanonicalConnection : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private abbrev FixedCanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedZeroSliceAnchor : StageNineHolonomicConfiguration :=
  completeJointP286ZeroSliceAnchoredCurrent positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private theorem fixedCanonicalConnection_smooth :
    FixedCanonicalConnection.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth FixedCanonicalInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite) 1

private theorem fixedCanonicalCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeCurvatureCoordinate FixedCanonicalConnection) := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff
      FixedCanonicalConnection fixedCanonicalConnection_smooth pair)

private theorem fixedCanonicalAuxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedCanonicalActual) 0 := by
  have nondegenerate :
      Matrix.det (FixedCanonicalInput.coframe 0) ≠ 0 := by
    change
      Matrix.det
        (fixedP506L0P286CanonicalGeneratedActual.coframe 0) ≠ 0
    rw [fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
    norm_num
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedCanonicalInput.coframe 0) nondegenerate
      (holonomicP286GaugeCurvatureCoordinate FixedCanonicalConnection 0)
  have inner : ContDiffAt ℝ ∞
      (fun point =>
        (FixedCanonicalInput.coframe point,
          holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalConnection point)) 0 :=
    (holonomicCoframe_contDiff FixedCanonicalInput
      (fixedP506L0FinalCommonActionActual_smooth 0)).contDiffAt.prodMk
        fixedCanonicalCurvatureCoordinate_contDiff.contDiffAt
  have composed := outer.comp 0 inner
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate FixedCanonicalActual =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (FixedCanonicalInput.coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalConnection point) by
      funext point
      unfold holonomicP286GaugeAuxiliaryCoordinate
      rw [fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliary]
      change
        formNativeP286GaugeActualToCoordinateLinear
            (StageNineFormNativeP286GaugeConstitutiveElimination.formNativeP286GaugeEliminatedAuxiliaryAtBoundary
              (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
              (FixedCanonicalInput.coframe point)
              (holonomicGaugeCurvature FixedCanonicalConnection point)) =
          formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
            (FixedCanonicalInput.coframe point)
            (holonomicP286GaugeCurvatureCoordinate
              FixedCanonicalConnection point)
      unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
      rw [show
        holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalConnection point =
          formNativeP286GaugeActualToCoordinateLinear
            (holonomicGaugeCurvature FixedCanonicalConnection point) by
          rfl]
      rw [formNativeP286GaugeActual_coordinate_actual]]
  exact composed

private theorem fixedAlgebraicAuxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]
  exact fixedCanonicalAuxiliaryCoordinate_contDiffAt_origin

private theorem fixedZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor) 0 := by
  have coordinateEq :
    holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor =
      holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent ∘
        (canonicalRestrictionZeroSliceProjection : BasePoint → BasePoint) := by
      funext point pair
      simp [FixedZeroSliceAnchor, completeJointP286ZeroSliceAnchoredCurrent,
        holonomicP286GaugeAuxiliaryCoordinate,
        completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor,
        canonicalRestrictionZeroSliceProjection_apply]
  rw [coordinateEq]
  have algebraicAtProjection : ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
      (canonicalRestrictionZeroSliceProjection 0) := by
    rw [canonicalRestrictionZeroSliceProjection.map_zero]
    exact fixedAlgebraicAuxiliaryCoordinate_contDiffAt_origin
  exact ContDiffAt.comp
    (g := holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
    (f := fun point : BasePoint =>
      canonicalRestrictionZeroSliceProjection point)
    0 algebraicAtProjection
    canonicalRestrictionZeroSliceProjection.contDiff.contDiffAt

private theorem fixedZeroSliceAnchor_auxiliaryFirstJet_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor)) 0 :=
  fixedZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin.fderiv_right
    (by simp)

private theorem fixedZeroSliceAnchor_directionalDerivative_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        p286GaugeAuxiliaryDirectionalDerivative
          FixedZeroSliceAnchor point direction) 0 := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  exact
    fixedZeroSliceAnchor_auxiliaryFirstJet_contDiffAt_origin.clm_apply
      contDiffAt_const

private theorem
    fixedZeroSliceAnchor_orderedDirectionalDerivative_contDiffAt_origin
    (direction first second : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        orderedP286GaugeTwoFormComponent
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedZeroSliceAnchor point direction)
          first second) 0 := by
  unfold orderedP286GaugeTwoFormComponent
  apply ContDiffAt.sum
  intro pair _
  have coefficientSmooth : ContDiffAt ℝ ∞
      (fun _ : BasePoint =>
        orientedLorentzBivectorBasisCoefficient pair first second) 0 :=
    contDiffAt_const
  exact coefficientSmooth.smul
    (contDiffAt_pi.mp
      (fixedZeroSliceAnchor_directionalDerivative_contDiffAt_origin
        direction) pair)

/-- The complete pure-exterior P286 read of the fixed zero-slice anchor is
smooth at the common P506/L0 occurrence. -/
theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286ZeroSliceAnchoredCurrent
          positiveSmoothUnifiedSource
          (completeJointGlobalP286AlgebraicCurrent
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor))) 0 := by
  apply contDiffAt_pi.mpr
  intro triple
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
  exact
    ((fixedZeroSliceAnchor_orderedDirectionalDerivative_contDiffAt_origin
        (threeFormFirst triple) (threeFormSecond triple)
        (threeFormThird triple)).add
      (fixedZeroSliceAnchor_orderedDirectionalDerivative_contDiffAt_origin
        (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (fixedZeroSliceAnchor_orderedDirectionalDerivative_contDiffAt_origin
        (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

/-- Every one of the canonical `(012, 013, 023, 123)` exterior components is
continuous at the same fixed occurrence. -/
theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_component_continuousAt_origin
    (triple : Fin 4) :
    ContinuousAt
      (fun point =>
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286ZeroSliceAnchoredCurrent
            positiveSmoothUnifiedSource
            (completeJointGlobalP286AlgebraicCurrent
              positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor))
          point triple) 0 :=
  (contDiffAt_pi.mp
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_contDiffAt_origin
    triple).continuousAt

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceContinuity
