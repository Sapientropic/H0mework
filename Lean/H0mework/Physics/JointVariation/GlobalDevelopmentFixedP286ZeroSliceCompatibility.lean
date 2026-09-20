import H0mework.Physics.GaugeAction.CanonicalRestrictionP286CoherentRegularity
import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility

/-!
# Fixed P506/L0 P286 zero-slice compatibility

The global P286 temporal producer anchors its field by pulling the
action-generated algebraic auxiliary back along the canonical zero-slice
retraction.  This module proves that the pullback retains the three spatial
first-jet directions at the fixed occurrence, hence retains the complete
`123` exterior coordinate.

No residual, support coordinate, derivative witness, or target field enters
the producer.  The differentiability facts are read from the explicit fixed
canonical constitutive normal form.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceCompatibility

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalRestrictionP286CoherentRegularity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedZeroSliceP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fixedZeroSliceP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fixedZeroSliceP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev FixedAlgebraicCurrent :
    StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedZeroSliceAnchor :
    StageNineHolonomicConfiguration :=
  completeJointP286ZeroSliceAnchoredCurrent positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

/-- The fixed algebraic auxiliary is genuinely differentiable at the common
occurrence because its whole field is the established live canonical
constitutive response. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]
  apply
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
  change
    Matrix.det
      (fixedP506L0P286CanonicalGeneratedActual.coframe 0) ≠
        0
  rw [fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
  norm_num

/-- The anchor is literally the algebraic field pulled back to canonical
time zero. -/
theorem fixedP506L0CompleteJointP286ZeroSliceAnchor_coordinate_eq_pullback :
    holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor =
      holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent ∘
        canonicalRestrictionZeroSliceProjection := by
  funext point pair
  simp [FixedZeroSliceAnchor, completeJointP286ZeroSliceAnchoredCurrent,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor,
    canonicalRestrictionZeroSliceProjection_apply]

theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_auxiliaryCoordinate_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor) 0 := by
  rw [
    fixedP506L0CompleteJointP286ZeroSliceAnchor_coordinate_eq_pullback]
  have algebraicDerivative :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
        0 :=
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_differentiableAt_origin.hasFDerivAt
  have algebraicDerivativeAtProjection :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
        (canonicalRestrictionZeroSliceProjection 0) := by
    rw [canonicalRestrictionZeroSliceProjection.map_zero]
    exact algebraicDerivative
  have composed :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent ∘
          canonicalRestrictionZeroSliceProjection)
        ((fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0
          ).comp canonicalRestrictionZeroSliceProjection)
        0 :=
    HasFDerivAt.comp
      (f := fun point : BasePoint =>
        canonicalRestrictionZeroSliceProjection point)
      (f' := canonicalRestrictionZeroSliceProjection)
      (g := holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
      (g' := fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
      0 algebraicDerivativeAtProjection
      canonicalRestrictionZeroSliceProjection.hasFDerivAt
  exact composed.differentiableAt

/-- Each spatial derivative survives the zero-slice retraction exactly. -/
theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_spatialDirectionalDerivative_origin
    (axis : Fin 3) :
    p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 axis.succ =
      p286GaugeAuxiliaryDirectionalDerivative FixedAlgebraicCurrent 0
        axis.succ := by
  have algebraicDerivative :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
        0 :=
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_differentiableAt_origin.hasFDerivAt
  have algebraicDerivativeAtProjection :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
        (canonicalRestrictionZeroSliceProjection 0) := by
    rw [canonicalRestrictionZeroSliceProjection.map_zero]
    exact algebraicDerivative
  have composed :
      HasFDerivAt
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent ∘
          canonicalRestrictionZeroSliceProjection)
        ((fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0
          ).comp canonicalRestrictionZeroSliceProjection)
        0 :=
    HasFDerivAt.comp
      (f := fun point : BasePoint =>
        canonicalRestrictionZeroSliceProjection point)
      (f' := canonicalRestrictionZeroSliceProjection)
      (g := holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
      (g' := fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0)
      0 algebraicDerivativeAtProjection
      canonicalRestrictionZeroSliceProjection.hasFDerivAt
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [
    fixedP506L0CompleteJointP286ZeroSliceAnchor_coordinate_eq_pullback,
    composed.fderiv,
    ContinuousLinearMap.comp_apply,
    canonicalRestrictionZeroSliceProjection_coordinateSpatial]

/-- The zero-slice anchor therefore retains the full spatial `123` exterior
coordinate of the same algebraic current. -/
theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_origin_three :
    holonomicP286GaugeAuxiliaryExteriorDerivative FixedZeroSliceAnchor 0 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedAlgebraicCurrent 0 3 := by
  simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    threeFormFirst, threeFormSecond, threeFormThird,
    orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
    orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
  have first :
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedZeroSliceAnchor 0 1) 3 =
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedAlgebraicCurrent 0 1) 3 := by
    simpa using congrFun
      (fixedP506L0CompleteJointP286ZeroSliceAnchor_spatialDirectionalDerivative_origin
        0) 3
  have second :
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedZeroSliceAnchor 0 2) 4 =
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedAlgebraicCurrent 0 2) 4 := by
    simpa using congrFun
      (fixedP506L0CompleteJointP286ZeroSliceAnchor_spatialDirectionalDerivative_origin
        1) 4
  have third :
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedZeroSliceAnchor 0 3) 5 =
      (p286GaugeAuxiliaryDirectionalDerivative
        FixedAlgebraicCurrent 0 3) 5 := by
    simpa using congrFun
      (fixedP506L0CompleteJointP286ZeroSliceAnchor_spatialDirectionalDerivative_origin
        2) 5
  rw [first, second, third]

/-- The spatial anchor read now meets the action-required occurrence profile.
This closes the `123` target before the temporal primitive is transported to
the final actual. -/
theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_origin_three_eq_requiredProfile :
    holonomicP286GaugeAuxiliaryExteriorDerivative FixedZeroSliceAnchor 0 3 =
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 3 := by
  rw [
    fixedP506L0CompleteJointP286ZeroSliceAnchor_exteriorDerivative_origin_three,
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct,
    ←
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_origin_eq_required]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceCompatibility
