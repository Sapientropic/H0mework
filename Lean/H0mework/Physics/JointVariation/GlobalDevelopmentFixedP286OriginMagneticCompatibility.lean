import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286ZeroSliceCompatibility

/-!
# Fixed P506/L0 origin magnetic temporal compatibility

At the common occurrence the source/current action profile is already the
literal exterior derivative of the algebraic current.  This module identifies
the three magnetic coordinates of the temporal correction with the temporal
first jet of that same algebraic field.  No residual coordinate or target
field is accepted as a premise.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286OriginMagneticCompatibility

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalRestrictionP286CoherentRegularity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceCompatibility
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedOriginMagneticP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fixedOriginMagneticP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fixedOriginMagneticP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedZeroSliceAnchor : StageNineHolonomicConfiguration :=
  completeJointP286ZeroSliceAnchoredCurrent positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private theorem fixedProfile_origin_eq_algebraicExterior :
    completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedAlgebraicCurrent 0 := by
  rw [
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct,
    ←
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_origin_eq_required]

private theorem fixedAnchor_temporalDirectionalDerivative_origin
    (pair : Fin 6) :
    (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0
      canonicalLorentzianTimeDirection) pair = 0 := by
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
    canonicalRestrictionZeroSliceProjection_coordinateTime]
  simp

theorem fixedP506L0P286TemporalCorrectionProfile_origin_magnetic
    (pair : Fin 6)
    (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :
    completeJointP286TemporalCorrectionProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 pair =
      (p286GaugeAuxiliaryDirectionalDerivative FixedAlgebraicCurrent 0
        canonicalLorentzianTimeDirection) pair := by
  have spatialDerivative (axis : Fin 3) :
      p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0
          axis.succ =
        p286GaugeAuxiliaryDirectionalDerivative FixedAlgebraicCurrent 0
          axis.succ := by
    simpa [FixedZeroSliceAnchor, FixedAlgebraicCurrent] using
      fixedP506L0CompleteJointP286ZeroSliceAnchor_spatialDirectionalDerivative_origin
        axis
  have temporalDerivativeZero (candidate : Fin 6) :
      (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 0)
          candidate = 0 := by
    simpa [canonicalLorentzianTimeDirection] using
      fixedAnchor_temporalDirectionalDerivative_origin candidate
  simp only [FixedZeroSliceAnchor] at spatialDerivative temporalDerivativeZero
  rcases magnetic with rfl | rfl | rfl
  · rw [completeJointP286TemporalCorrectionProfile_twoThree,
      fixedProfile_origin_eq_algebraicExterior]
    have spatialTwoTwo :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 2) 2 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 2) 2 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 1) 2
    have spatialThreeOne :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 3) 1 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 3) 1 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 2) 1
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 3,
      spatialTwoTwo, spatialThreeOne]
    simp [canonicalLorentzianTimeDirection]
  · rw [completeJointP286TemporalCorrectionProfile_threeOne,
      fixedProfile_origin_eq_algebraicExterior]
    have spatialOneTwo :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 1) 2 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 1) 2 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 0) 2
    have spatialThreeZero :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 3) 0 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 3) 0 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 2) 0
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 4,
      spatialOneTwo, spatialThreeZero]
    simp [canonicalLorentzianTimeDirection]
  · rw [completeJointP286TemporalCorrectionProfile_oneTwo,
      fixedProfile_origin_eq_algebraicExterior]
    have spatialOneOne :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 1) 1 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 1) 1 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 0) 1
    have spatialTwoZero :
        (p286GaugeAuxiliaryDirectionalDerivative FixedZeroSliceAnchor 0 2) 0 =
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedAlgebraicCurrent 0 2) 0 := by
      simpa [FixedZeroSliceAnchor] using
        congrFun (spatialDerivative 1) 0
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 5,
      spatialOneOne, spatialTwoZero]
    simp [canonicalLorentzianTimeDirection]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286OriginMagneticCompatibility
