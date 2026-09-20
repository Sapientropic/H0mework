import H0mework.Physics.FixedJoint.FixedJointP286AlgebraicConnectionChangedRead
import H0mework.Physics.FixedJoint.FixedConstitutiveDifferentialSectionResidual
import H0mework.Physics.FixedJoint.FixedConstitutivePhysicalClosure
import H0mework.Physics.ScalarJets.GeneratedTransitionScalarJet
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport

/-!
# Fixed P506/L0 U6 P286 zero-slice obstruction

This module gives a direct same-source obstruction to extending the fixed
origin P286 Euler zero across the complete zero slice.  At the spatial
`e₀` point, the faithful `123/hypercharge` coordinate is exactly `7/36`:
the canonical exterior contribution is `1`, while the Temporal scalar and
matter currents contribute `7/36` and `-1`.

The public conclusions are an origin-zero regression, the exact nonzero
coordinate, whole-P286 nonvanishing, and failure of the complete pointwise
joint zero fiber at that occurrence.  No residual coordinate is used as a
producer premise, and no successor is defined.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286ZeroSliceObstruction

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutivePhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineSourceGeneratedHolonomicChartAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaussRadialSecondJetLift
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private theorem p286TemporalGaugeOneForm_wedge_reads_spatial123
    (coordinate : P286CoordinateCarrier)
    (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286TemporalGaugeOneForm coordinate) threeForm =
      p286CoordinateLiePairing coordinate (threeForm 3) := by
  classical
  unfold p286GaugeOneFormThreeFormWedgeCoefficient
    p286TemporalGaugeOneForm canonicalLorentzianTimeDirection
    oneWedgeThreeSign missingTripleOfOneForm
  simp [Fin.sum_univ_four]

/-- The distinguished occurrence is already a genuine algebraic P286 fixed
point.  This is the baseline for the zero-slice computation below, not an
all-point extrapolation. -/
theorem fixedP506L0_Algebraic_p286Euler_origin_zero :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic 0 = 0 := by
  exact
    StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility.fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_origin_zero

/-- Exact complete zero-slice support before coordinate adjudication.  Both
summands are positive reads of already generated fields. -/
theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_support
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
          (canonicalCauchySlicePoint 0 space) +
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Temporal
            (canonicalCauchySlicePoint 0 space)) := by
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged
      (canonicalCauchySlicePoint 0 space)

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

private abbrev Charge : P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge

private theorem positiveVacuumCoordinates_normalForm :
    sourceGeneratedVacuumCoordinates Source =
      ∑ output : Fin 2, ∑ input : Fin 2,
        EuclideanSpace.single (finiteGenerationScalarIndex output input) 1 := by
  unfold sourceGeneratedVacuumCoordinates
  rw [positive_sourceGeneratedVacuumBase]
  simp [finiteGenerationJointBreakingScalar, finiteGenerationBreakingTensor,
    scalarCoordinateEquiv]

private theorem hyperchargeAction_positiveVacuum_normalForm :
    scalarP286ActionBilinear hyperchargeCoordinate
        (sourceGeneratedVacuumCoordinates Source) =
      ∑ output : Fin 2, ∑ input : Fin 2,
        (Complex.I *
            (exteriorHyperchargeWeight
              (finiteGenerationScalarIndex output input) : ℂ)) •
          EuclideanSpace.single
            (finiteGenerationScalarIndex output input) 1 := by
  ext index
  change
    scalarMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm hyperchargeCoordinate))
        (sourceGeneratedVacuumCoordinates Source) index = _
  rw [show
    p286LieBlockEmbed (p286CoordinateEquiv.symm hyperchargeCoordinate) =
        motherHyperchargeDirection by
      simp [hyperchargeCoordinate, motherHyperchargeDirection]]
  rw [scalarMotherLieAction_motherHyperchargeDirection_apply,
    positiveVacuumCoordinates_normalForm]
  simp [Pi.single_apply]
  by_cases h00 : index = finiteGenerationScalarIndex 0 0 <;>
    by_cases h01 : index = finiteGenerationScalarIndex 0 1 <;>
    by_cases h10 : index = finiteGenerationScalarIndex 1 0 <;>
    by_cases h11 : index = finiteGenerationScalarIndex 1 1 <;>
    simp_all [finiteGenerationScalarIndex, finiteGenerationScalarSubset] <;>
    ring

private def finiteGenerationChargeActionCoefficient
    (output input : Fin 2) : ℂ :=
  match output, input with
  | 0, 0 => Complex.I
  | 0, 1 => 0
  | 1, 0 => -(1 / 3 : ℂ) * Complex.I
  | 1, 1 => -(4 / 3 : ℂ) * Complex.I

private def chargeFundamentalCoefficient (index : SU7MotherIndex) : ℂ :=
  (p286LieBlockEmbed p506MatterCurrentGaussData :
    Matrix SU7MotherIndex SU7MotherIndex ℂ) index index

private theorem fundamentalChargeAction_basis
    (index : SU7MotherIndex) :
    fundamentalMotherLieAction
        (p286LieBlockEmbed p506MatterCurrentGaussData)
        (su7FundamentalBasis index) =
      chargeFundamentalCoefficient index • su7FundamentalBasis index := by
  funext row
  fin_cases index <;> fin_cases row <;>
    simp +decide [chargeFundamentalCoefficient, fundamentalMotherLieAction,
      p506MatterCurrentGaussData,
      p506MatterCurrentGaussColor, p506MatterCurrentGaussColorRaw,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator,
      su7FundamentalBasis, Matrix.mulVecLin, Matrix.mulVec,
      Matrix.diagonal_apply, Pi.single_apply, Fin.sum_univ_seven] <;>
    norm_num

private theorem exteriorChargeAction_basis
    (index : ExteriorBasisIndex 4) :
    exteriorBasisLieAction 4
        (p286LieBlockEmbed p506MatterCurrentGaussData) index =
      (∑ position : Fin 4,
          chargeFundamentalCoefficient
            (exteriorPositionEquiv index position).1) •
        su7ExteriorBasis 4 index := by
  unfold exteriorBasisLieAction
  calc
    _ = ∑ position : Fin 4,
          chargeFundamentalCoefficient
              (exteriorPositionEquiv index position).1 •
            su7ExteriorBasis 4 index := by
      apply Finset.sum_congr rfl
      intro position _
      change
        (exteriorPower.ιMulti ℂ 4)
            (exteriorBasisLieActionInput 4
              (p286LieBlockEmbed p506MatterCurrentGaussData) index
              position) = _
      rw [exteriorBasisLieActionTerm_eq_update,
        show exteriorBasisInput 4 index position =
            su7FundamentalBasis
              (exteriorPositionEquiv index position).1 by rfl,
        fundamentalChargeAction_basis,
        (exteriorPower.ιMulti ℂ 4).map_update_smul,
        show su7FundamentalBasis
              (exteriorPositionEquiv index position).1 =
            exteriorBasisInput 4 index position by rfl,
        Function.update_eq_self]
      exact congrArg
        (fun value =>
          chargeFundamentalCoefficient
              (exteriorPositionEquiv index position).1 • value)
        (exteriorBasisInput_wedge_eq_basis_current 4 index)
    _ = _ := by rw [← Finset.sum_smul]

private theorem chargeAction_finiteGenerationBreakingTensor
    (output input : Fin 2) :
    exteriorMotherLieAction 4
        (p286LieBlockEmbed p506MatterCurrentGaussData)
        (finiteGenerationBreakingTensor output input) =
      finiteGenerationChargeActionCoefficient output input •
        finiteGenerationBreakingTensor output input := by
  rw [finiteGenerationBreakingTensor,
    exteriorMotherLieAction_basis_current, exteriorChargeAction_basis]
  congr 1
  calc
    (∑ position : Fin 4,
        chargeFundamentalCoefficient
          (exteriorPositionEquiv
            (finiteGenerationScalarIndex output input) position).1) =
        ∑ basisIndex ∈ (finiteGenerationScalarIndex output input).1,
          chargeFundamentalCoefficient basisIndex :=
      exteriorPosition_sum_eq_subset_sum_complex
        (finiteGenerationScalarIndex output input)
        chargeFundamentalCoefficient
    _ = finiteGenerationChargeActionCoefficient output input := by
      fin_cases output <;> fin_cases input <;>
        simp +decide [finiteGenerationChargeActionCoefficient,
          finiteGenerationScalarIndex, finiteGenerationScalarSubset,
          chargeFundamentalCoefficient,
          p506MatterCurrentGaussData, p506MatterCurrentGaussColor,
          p506MatterCurrentGaussColorRaw, p286LieBlockEmbed, rawP286LieBlock,
          weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
          hyperchargeGenerator, Matrix.diagonal_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          SU7ExteriorBreakingYukawa.colorZeroIndex,
          SU7ExteriorBreakingYukawa.colorOneIndex,
          SU7ExteriorBreakingYukawa.colorTwoIndex,
          SU7ExteriorBreakingYukawa.weakOneIndex,
          hyperPlusIndex, hyperMinusIndex] <;>
        ring

private theorem chargeAction_positiveVacuum_normalForm :
    scalarP286ActionBilinear Charge
        (sourceGeneratedVacuumCoordinates Source) =
      ∑ output : Fin 2, ∑ input : Fin 2,
        finiteGenerationChargeActionCoefficient output input •
          EuclideanSpace.single
            (finiteGenerationScalarIndex output input) 1 := by
  change
    scalarP286ActionBilinear
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  rw [currentGaussCharge_eq_normalForm]
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm p506MatterCurrentGaussCoordinate))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  rw [show p286CoordinateEquiv.symm p506MatterCurrentGaussCoordinate =
      p506MatterCurrentGaussData by
    simp [p506MatterCurrentGaussCoordinate]]
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  rw [scalarCoordinateEquiv.symm_apply_apply,
    positive_sourceGeneratedVacuumBase]
  simp only [finiteGenerationJointBreakingScalar, map_sum,
    chargeAction_finiteGenerationBreakingTensor, map_smul]
  simp [finiteGenerationBreakingTensor, scalarCoordinateEquiv]

private theorem scalarCoordinatePairingRe_eq_inner_re
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second = (inner ℂ first second).re := by
  simp [scalarCoordinatePairingRe, PiLp.inner_apply,
    RCLike.inner_apply', mul_comm]

private theorem hypercharge_charge_scalarAction_pairing_normalForm_local :
    scalarCoordinatePairingRe
        (scalarP286ActionBilinear hyperchargeCoordinate
          (sourceGeneratedVacuumCoordinates Source))
        (scalarP286ActionBilinear Charge
          (sourceGeneratedVacuumCoordinates Source)) =
      -(7 / 3 : ℝ) := by
  rw [hyperchargeAction_positiveVacuum_normalForm,
    chargeAction_positiveVacuum_normalForm,
    scalarCoordinatePairingRe_eq_inner_re]
  simp +decide [Fin.sum_univ_two,
    finiteGenerationChargeActionCoefficient,
    finiteGenerationScalarIndex, finiteGenerationScalarSubset,
    exteriorHyperchargeWeight, fundamentalHyperchargeWeight,
    SU7ExteriorBreakingYukawa.colorZeroIndex,
    SU7ExteriorBreakingYukawa.colorOneIndex,
    SU7ExteriorBreakingYukawa.colorTwoIndex,
    SU7ExteriorBreakingYukawa.weakOneIndex,
    hyperPlusIndex, hyperMinusIndex,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  norm_num

/-- Exact finite-representation pairing of the canonical hypercharge action
with the inherited P506 Gauss-charge action on the source vacuum.  Its public
mouth uses only stable source constants, not the local proof abbreviations. -/
theorem hypercharge_charge_scalarAction_pairing_normalForm :
    scalarCoordinatePairingRe
        (scalarP286ActionBilinear
          (p286CoordinateEquiv (0, 0, hyperchargeGenerator))
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
        (scalarP286ActionBilinear
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)) =
      -(7 / 3 : ℝ) := by
  exact hypercharge_charge_scalarAction_pairing_normalForm_local

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem scalarCoordinatePairingRe_zero_left_local
    (second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 second = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_local
    (first : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem fixedPrimitiveDiagonal_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.matter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.matter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      Source positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      Source positiveP506MatterCurrentFullSynchronizedCauchyState).matter space =
      diracSpinTwoMatterProbe
  rw [reads.2.2.2.2.2.2.2.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact fixedCartanReactionContact_matter_origin space

private theorem fixedPrimitiveDiagonal_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.conjugateMatter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      Source positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      Source positiveP506MatterCurrentFullSynchronizedCauchyState).conjugateMatter
        space = diracSpinZeroMatterCoordinate
  rw [reads.2.2.2.2.2.2.2.2.2]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact fixedCartanReactionContact_conjugateMatter_origin space

private theorem constitutive_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter
        (canonicalCauchySlicePoint 0 space) = diracSpinTwoMatterProbe := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_matter_zeroSlice,
    fixedPrimitiveDiagonal_matter_zeroSlice_constant]

private theorem constitutive_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_zeroSlice,
    fixedPrimitiveDiagonal_conjugateMatter_zeroSlice_constant]

private theorem p286MatterCurrentCoefficient_eq_of_contacts_local
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point firstPoint : BasePoint)
    (coframeEq : first.coframe point = second.coframe firstPoint)
    (matterEq : first.matter point = second.matter firstPoint)
    (conjugateEq :
      first.conjugateMatter point = second.conjugateMatter firstPoint)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient source first direction point =
      p286MatterCurrentCoefficient source second direction firstPoint := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateEq]
  simp only [matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    p286GaugeConnectionMotherVariation]

private theorem p286ScalarCurrentCoefficient_eq_of_contacts_local
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point firstPoint : BasePoint)
    (coframeEq : first.coframe point = second.coframe firstPoint)
    (scalarEq : first.scalar point = second.scalar firstPoint)
    (covariantDerivativeEq :
      holonomicScalarCovariantDerivative first point =
        holonomicScalarCovariantDerivative second firstPoint)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient source first direction point =
      p286ScalarCurrentCoefficient source second direction firstPoint := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [coframeEq, scalarEq, covariantDerivativeEq]

private theorem constitutive_temporalHypercharge_matterCurrent_e0 :
    p286MatterCurrentCoefficient Source
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) = -1 := by
  calc
    _ = p286MatterCurrentCoefficient Source
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 := by
      apply p286MatterCurrentCoefficient_eq_of_contacts_local
      · rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice,
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_origin]
      · rw [constitutive_matter_zeroSlice_constant,
          StageNineDiracDualFormNativeFixedP506JointActionConstitutivePhysicalClosure.fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin]
      · rw [constitutive_conjugateMatter_zeroSlice_constant,
          StageNineDiracDualFormNativeFixedP506JointActionConstitutivePhysicalClosure.fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin]
    _ = -1 :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_temporalHyperchargeMatterCurrent

private theorem constitutive_connectionCoordinate_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) := by
  have connectionEquality :
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection =
        FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
    simpa only using
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection
  calc
    _ = holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) := by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [connectionEquality]
    _ = _ :=
      fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm
        (canonicalCauchySlicePoint 0 space)

private theorem fixedSolvedConnection_zeroSlice_time_e0 :
    fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 SpatialE0) 0 =
      (1 / 12 : ℝ) • Charge := by
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 SpatialE0)) 0
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  have couplingValue : c3h181StrongCouplingSquared = 1 / 2 := by
    change positiveSmoothUnifiedSource.legacy.sigma = (1 / 2 : ℝ)
    exact
      StageNinePositiveSourceGravityMouthResidualTransportIteration.positiveSmoothUnifiedSource_legacy_sigma_eq_half
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  unfold c3h181FullConnectionCoefficient
  rw [couplingValue]
  simp [SpatialE0,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    coordinateDirection, localBaseCoordinate_apply, p286BaseCoordinate_apply,
    Fin.sum_univ_three, Pi.single_apply]
  norm_num

private theorem positive_generatedLocalVacuumCoordinates_zero_local :
    generatedLocalVacuumCoordinates Source 0 =
      fun _ => sourceGeneratedVacuumCoordinates Source := by
  funext point
  rw [generatedLocalVacuumCoordinates, generatedScalarFrame,
    generatedTransition_normalized]
  exact scalarCoordinateAction_one _

private theorem constitutive_scalar_vacuum :
    FixedP506FormNativeConstitutiveJointActionSuccessor.scalar =
      fun _ => sourceGeneratedVacuumCoordinates Source := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalarGeneratedVacuum,
    positive_generatedLocalVacuumCoordinates_zero_local]

private theorem constitutive_temporalHypercharge_scalarVariation_e0 :
    holonomicScalarGaugeConnectionVariation
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (fun _ => p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) =
      fun direction =>
        if direction = 0 then
          scalarP286ActionBilinear hyperchargeCoordinate
            (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [congrFun constitutive_scalar_vacuum
    (canonicalCauchySlicePoint 0 SpatialE0)]
  change
    scalarP286ActionBilinear
        ((p286TemporalGaugeOneForm hyperchargeCoordinate) direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  fin_cases direction <;>
    simp [p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection]

private theorem fixedSolvedConnection_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) axis.succ
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  fin_cases axis <;>
    simp [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]

private theorem constitutive_scalarCovariantDerivative_e0 :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (canonicalCauchySlicePoint 0 SpatialE0) =
      fun direction =>
        if direction = 0 then
          (1 / 12 : ℝ) •
            scalarP286ActionBilinear Charge
              (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [constitutive_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  have coordinateEq := congrFun
    (constitutive_connectionCoordinate_zeroSlice SpatialE0) direction
  unfold holonomicP286GaugeConnectionCoordinate at coordinateEq
  have rawEq := congrArg p286CoordinateEquiv.symm coordinateEq
  simp only [p286CoordinateEquiv.symm_apply_apply] at rawEq
  rw [rawEq]
  change
    scalarP286ActionBilinear
        (fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 SpatialE0) direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  by_cases h : direction = 0
  · subst direction
    rw [fixedSolvedConnection_zeroSlice_time_e0]
    simp
  · have directionEq : (direction.pred h).succ = direction :=
      Fin.succ_pred direction h
    rw [← directionEq,
      fixedSolvedConnection_zeroSlice_spatial SpatialE0 (direction.pred h)]
    simp [h]

private theorem constitutive_temporalHypercharge_scalarCurrent_e0 :
    p286ScalarCurrentCoefficient Source
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) =
      7 / 36 := by
  unfold p286ScalarCurrentCoefficient
  rw [constitutive_temporalHypercharge_scalarVariation_e0]
  simp only [toContinuumPointField]
  rw [constitutive_scalarCovariantDerivative_e0]
  simp only [generatedVolumeDensity]
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  simp only [Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  rw [StageNinePositiveSourceNativeGravityCurvatureBridge.lorentzianMetricOfCoframe_one_inv]
  have reversePairing :
      scalarCoordinatePairingRe
          (scalarP286ActionBilinear Charge
            (sourceGeneratedVacuumCoordinates Source))
          (scalarP286ActionBilinear hyperchargeCoordinate
            (sourceGeneratedVacuumCoordinates Source)) =
        -(7 / 3 : ℝ) := by
    rw [scalarCoordinatePairingRe_comm_local]
    exact hypercharge_charge_scalarAction_pairing_normalForm_local
  simp only [Fin.sum_univ_four]
  simp [minkowskiInternalMetric, Matrix.diagonal_apply,
    scalarCoordinatePairingRe_zero_left_local,
    scalarCoordinatePairingRe_zero_right_local,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right,
    hypercharge_charge_scalarAction_pairing_normalForm_local, reversePairing]
  norm_num

private theorem formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) :
    (fun point =>
      formNativeChargedGaugeFirstCoefficient Source 0 point
        (toContinuumPointField configuration point) direction) =
      p286ScalarCurrentCoefficient Source configuration direction +
        p286MatterCurrentCoefficient Source configuration direction := by
  funext point
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point]
  rw [mul_add]
  rfl

private theorem constitutive_temporalHypercharge_chargedCoefficient_e0 :
    formNativeChargedGaugeFirstCoefficient Source 0
        (canonicalCauchySlicePoint 0 SpatialE0)
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (canonicalCauchySlicePoint 0 SpatialE0))
        (p286TemporalGaugeOneForm hyperchargeCoordinate) =
      -(29 / 36 : ℝ) := by
  rw [congrFun
    (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
      FixedP506FormNativeConstitutiveJointActionSuccessor
      (p286TemporalGaugeOneForm hyperchargeCoordinate))
    (canonicalCauchySlicePoint 0 SpatialE0)]
  change
    p286ScalarCurrentCoefficient Source
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (p286TemporalGaugeOneForm hyperchargeCoordinate)
          (canonicalCauchySlicePoint 0 SpatialE0) +
        p286MatterCurrentCoefficient Source
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (p286TemporalGaugeOneForm hyperchargeCoordinate)
          (canonicalCauchySlicePoint 0 SpatialE0) = _
  rw [constitutive_temporalHypercharge_scalarCurrent_e0,
    constitutive_temporalHypercharge_matterCurrent_e0]
  norm_num

private theorem constitutive_chargedThreeForm_e0_spatial123_hypercharge :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 SpatialE0)
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor
            (canonicalCauchySlicePoint 0 SpatialE0))) 3) =
      -(29 / 36 : ℝ) := by
  rw [← p286TemporalGaugeOneForm_wedge_reads_spatial123]
  rw [formNativeChargedGaugeThreeForm_evaluation]
  exact constitutive_temporalHypercharge_chargedCoefficient_e0

private theorem hypercharge_negCharge_pairing :
    p286CoordinateLiePairing hyperchargeCoordinate (-Charge) = 1 := by
  have chargeHypercharge :
      p286CoordinateLiePairing Charge hyperchargeCoordinate = -1 := by
    change
      p286CoordinateLiePairing
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
          hyperchargeCoordinate = -1
    rw [currentGaussCharge_eq_normalForm]
    change
      p286CoordinateLiePairing p506MatterCurrentGaussCoordinate
          (p286CoordinateEquiv (0, 0, hyperchargeGenerator)) = -1
    rw [p506MatterCurrentGaussCoordinate_pairing]
    simp [hyperchargeGenerator]
  rw [show -Charge = (-1 : ℝ) • Charge by simp,
    p286CoordinateLiePairing_smul_right,
    p286CoordinateLiePairing_symmetric, chargeHypercharge]
  norm_num

private theorem temporal_scalar_firstJet_zeroSlice_e0
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative Temporal.scalar
        (canonicalCauchySlicePoint 0 SpatialE0) direction =
      fieldDirectionalDerivative FixedInput.scalar
        (canonicalCauchySlicePoint 0 SpatialE0) direction := by
  have currentDifferentiable :
      DifferentiableAt ℝ FixedInput.scalar
        (canonicalCauchySlicePoint 0 SpatialE0) :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      ).differentiable (by simp) |>.differentiableAt
  by_cases generatedDifferentiable :
      DifferentiableAt ℝ Temporal.scalar
        (canonicalCauchySlicePoint 0 SpatialE0)
  · have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source FixedInput SpatialE0 currentDifferentiable
        (by simpa [Temporal, completeJointGlobalTemporalCurrent] using
          generatedDifferentiable) direction
    simpa [Temporal, completeJointGlobalTemporalCurrent] using generated
  · have generatedDerivativeZero :
        fieldDirectionalDerivative Temporal.scalar
            (canonicalCauchySlicePoint 0 SpatialE0) direction = 0 := by
      unfold fieldDirectionalDerivative
      rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
      rfl
    have currentDerivativeZero :
        fieldDirectionalDerivative FixedInput.scalar
            (canonicalCauchySlicePoint 0 SpatialE0) direction = 0 := by
      rw [← fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        constitutive_scalar_vacuum]
      simp [fieldDirectionalDerivative]
    rw [generatedDerivativeZero, currentDerivativeZero]

private theorem temporal_scalarCovariantDerivative_e0_eq_constitutive :
    holonomicScalarCovariantDerivative Temporal
        (canonicalCauchySlicePoint 0 SpatialE0) =
      holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  funext direction
  calc
    holonomicScalarCovariantDerivative Temporal
          (canonicalCauchySlicePoint 0 SpatialE0) direction =
        holonomicScalarCovariantDerivative FixedInput
          (canonicalCauchySlicePoint 0 SpatialE0) direction := by
      unfold holonomicScalarCovariantDerivative
      rw [temporal_scalar_firstJet_zeroSlice_e0 direction]
      have scalarPointEq :
          Temporal.scalar (canonicalCauchySlicePoint 0 SpatialE0) =
            FixedInput.scalar (canonicalCauchySlicePoint 0 SpatialE0) := by
        change
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source FixedInput).scalar
              (canonicalCauchySlicePoint 0 SpatialE0) = _
        exact
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
            Source FixedInput SpatialE0
      rw [scalarPointEq]
      rfl
    _ = holonomicScalarCovariantDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (canonicalCauchySlicePoint 0 SpatialE0) direction := by
      unfold holonomicScalarCovariantDerivative
      rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

/-- The scalar part of the old temporal charged read at the distinguished
zero-slice occurrence.  This convention-locked value is exported only so a
later same-source write can be checked by read-after-write subtraction; it is
not a producer parameter. -/
theorem
    fixedP506L0_Temporal_scalarCurrent_zeroSlice_spatialE0_temporalHypercharge_eq :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor)
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) =
      7 / 36 := by
  change
    p286ScalarCurrentCoefficient Source Temporal
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) = 7 / 36
  calc
    _ = p286ScalarCurrentCoefficient Source
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) := by
      apply p286ScalarCurrentCoefficient_eq_of_contacts_local
      · change
          FixedInput.coframe (canonicalCauchySlicePoint 0 SpatialE0) =
            FixedP506FormNativeConstitutiveJointActionSuccessor.coframe
              (canonicalCauchySlicePoint 0 SpatialE0)
        exact (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe _).symm
      · calc
          Temporal.scalar (canonicalCauchySlicePoint 0 SpatialE0) =
              FixedInput.scalar
                (canonicalCauchySlicePoint 0 SpatialE0) := by
            change
              (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
                Source FixedInput).scalar
                  (canonicalCauchySlicePoint 0 SpatialE0) = _
            exact
              sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
                Source FixedInput SpatialE0
          _ = FixedP506FormNativeConstitutiveJointActionSuccessor.scalar
                (canonicalCauchySlicePoint 0 SpatialE0) :=
            (congrFun
              fixedP506FormNativeConstitutiveJointActionSuccessor_scalar _).symm
      · exact temporal_scalarCovariantDerivative_e0_eq_constitutive
    _ = 7 / 36 := constitutive_temporalHypercharge_scalarCurrent_e0

private theorem temporal_chargedThreeForm_e0_eq_constitutive :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 SpatialE0)
        (toContinuumPointField Temporal
          (canonicalCauchySlicePoint 0 SpatialE0)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 SpatialE0)
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (canonicalCauchySlicePoint 0 SpatialE0)) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · change
      FixedInput.coframe (canonicalCauchySlicePoint 0 SpatialE0) =
        FixedP506FormNativeConstitutiveJointActionSuccessor.coframe
          (canonicalCauchySlicePoint 0 SpatialE0)
    exact (congrFun
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe _).symm
  · calc
      Temporal.scalar (canonicalCauchySlicePoint 0 SpatialE0) =
          FixedInput.scalar (canonicalCauchySlicePoint 0 SpatialE0) := by
        change
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source FixedInput).scalar
              (canonicalCauchySlicePoint 0 SpatialE0) = _
        exact
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
            Source FixedInput SpatialE0
      _ = FixedP506FormNativeConstitutiveJointActionSuccessor.scalar
            (canonicalCauchySlicePoint 0 SpatialE0) :=
        (congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_scalar _).symm
  · exact temporal_scalarCovariantDerivative_e0_eq_constitutive
  · calc
      Temporal.matter (canonicalCauchySlicePoint 0 SpatialE0) =
          FixedInput.matter (canonicalCauchySlicePoint 0 SpatialE0) := by
        change
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source FixedInput).matter
              (canonicalCauchySlicePoint 0 SpatialE0) = _
        exact
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
            Source FixedInput SpatialE0
      _ = FixedP506FormNativeConstitutiveJointActionSuccessor.matter
            (canonicalCauchySlicePoint 0 SpatialE0) :=
        (congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_matter _).symm
  · calc
      Temporal.conjugateMatter (canonicalCauchySlicePoint 0 SpatialE0) =
          FixedInput.conjugateMatter
            (canonicalCauchySlicePoint 0 SpatialE0) := by
        change
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source FixedInput).conjugateMatter
              (canonicalCauchySlicePoint 0 SpatialE0) = _
        exact
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
            Source FixedInput SpatialE0
      _ = FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter
            (canonicalCauchySlicePoint 0 SpatialE0) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter
          _).symm

private theorem fixedCanonicalConnectionCandidate_zero_local :
    fixedP506L0P286CanonicalConnectionCandidate 0 =
      fixedP506L0P286CanonicalActionInput := by
  simpa [fixedP506L0P286CanonicalConnectionCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate] using
    (diracDualFormNativeP286CanonicalConnectionCandidate_zero
      fixedP506L0P286CanonicalActionInput)

private theorem fixedCanonicalGeneratedWrite_zero_local :
    fixedP506L0P286CanonicalGeneratedWrite = 0 := by
  simpa only using
    StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta.fixedP506L0P286CanonicalGeneratedWrite_zero

private theorem canonical_gaugeConnection_eq_constitutive :
    Canonical.gaugeConnection =
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection := by
  change
    (fixedP506L0P286CanonicalJointCandidate
      fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection = _
  rw [fixedCanonicalGeneratedWrite_zero_local,
    fixedP506L0P286CanonicalJointCandidate_gaugeConnection,
    fixedCanonicalConnectionCandidate_zero_local,
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_constitutive]

private theorem canonical_gaugeAuxiliary_eq_constitutive :
    Canonical.gaugeAuxiliary =
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary := by
  funext point
  rw [fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliary,
    fixedCanonicalGeneratedWrite_zero_local,
    fixedCanonicalConnectionCandidate_zero_local]
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  unfold fixedP506FormNativeConstitutiveAuxiliaryField
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_solved]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    fixedP506L0P286CanonicalActionInput FixedInput
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved point]

private theorem canonical_exterior_eq_constitutive :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [canonical_gaugeConnection_eq_constitutive,
    canonical_gaugeAuxiliary_eq_constitutive]

private theorem constitutive_explicitZeroSliceNormalForm_e0_spatial123 :
    (fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        SpatialE0) 3 =
      -Charge +
        (formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 SpatialE0)
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor
            (canonicalCauchySlicePoint 0 SpatialE0))) 3 := by
  unfold
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
  simp only [Pi.add_apply]
  congr 1
  unfold pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative p286GaugeTwoFormAdjoint
  change
    orderedP286GaugeTwoFormComponent
          (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection 1) +
            p286GaugeTwoFormAdjoint
              (fixedP506FormNativeJointActionSolvedConnectionNormalForm
                (canonicalCauchySlicePoint 0 SpatialE0) 1)
              (c3h181FullAuxiliaryCoordinateNormalForm
                (-(canonicalCauchySlicePoint 0 SpatialE0)))) 2 3 +
        orderedP286GaugeTwoFormComponent
          (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection 2) +
            p286GaugeTwoFormAdjoint
              (fixedP506FormNativeJointActionSolvedConnectionNormalForm
                (canonicalCauchySlicePoint 0 SpatialE0) 2)
              (c3h181FullAuxiliaryCoordinateNormalForm
                (-(canonicalCauchySlicePoint 0 SpatialE0)))) 3 1 +
      orderedP286GaugeTwoFormComponent
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
            (coordinateDirection 3) +
          p286GaugeTwoFormAdjoint
            (fixedP506FormNativeJointActionSolvedConnectionNormalForm
              (canonicalCauchySlicePoint 0 SpatialE0) 3)
            (c3h181FullAuxiliaryCoordinateNormalForm
              (-(canonicalCauchySlicePoint 0 SpatialE0)))) 1 2 =
      -Charge
  have connectionOne :
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 SpatialE0) 1 = 0 := by
    simpa using fixedSolvedConnection_zeroSlice_spatial SpatialE0 0
  have connectionTwo :
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 SpatialE0) 2 = 0 := by
    simpa using fixedSolvedConnection_zeroSlice_spatial SpatialE0 1
  have connectionThree :
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 SpatialE0) 3 = 0 := by
    simpa using fixedSolvedConnection_zeroSlice_spatial SpatialE0 2
  rw [connectionOne, connectionTwo, connectionThree]
  simp [fixedP506FormNativeJointActionAuxiliaryFirstJetLinear,
    fixedP506FormNativeGaussCharge_eq_neg_U7,
    SpatialE0, canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    coordinateDirection, localBaseCoordinate_apply, p286BaseCoordinate_apply,
    p286GaussRadialAuxiliaryFirstJetLinear,
    p286GaussAuxiliaryAxisEmbedding, p286SpatialAuxiliaryVelocityEmbedding,
    p286GaugeTwoFormAdjoint, orderedP286GaugeTwoFormComponent,
    StageNineLorentzConnectionVariation.orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond,
    StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_left,
    Fin.sum_univ_three, Fin.sum_univ_six]
  module

private theorem constitutiveExterior_e0_spatial123_eq_negCharge :
    (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
      FixedP506FormNativeConstitutiveJointActionSuccessor
      (canonicalCauchySlicePoint 0 SpatialE0)) 3 = -Charge := by
  have residual := congrFun
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
      SpatialE0) 3
  change
    (holonomicFormNativeP286GaugeEulerThreeForm Source 0
      FixedP506FormNativeConstitutiveJointActionSuccessor
      (canonicalCauchySlicePoint 0 SpatialE0)) 3 =
        (fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
          SpatialE0) 3 at residual
  unfold holonomicFormNativeP286GaugeEulerThreeForm at residual
  simp only [Pi.add_apply] at residual
  rw [constitutive_explicitZeroSliceNormalForm_e0_spatial123] at residual
  exact add_right_cancel residual

private theorem canonicalExterior_e0_spatial123_eq_negCharge :
    (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
      (canonicalCauchySlicePoint 0 SpatialE0)) 3 = -Charge := by
  rw [congrFun canonical_exterior_eq_constitutive
    (canonicalCauchySlicePoint 0 SpatialE0)]
  exact constitutiveExterior_e0_spatial123_eq_negCharge

private theorem temporal_chargedThreeForm_e0_spatial123_hypercharge :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 SpatialE0)
          (toContinuumPointField Temporal
            (canonicalCauchySlicePoint 0 SpatialE0))) 3) =
      -(29 / 36 : ℝ) := by
  rw [temporal_chargedThreeForm_e0_eq_constitutive]
  exact constitutive_chargedThreeForm_e0_spatial123_hypercharge

/-- The fixed algebraic P286 Euler read is concretely nonzero on the complete
zero slice: at the spatial `e₀` point, its faithful `123/hypercharge`
coordinate is exactly `7/36`. -/
theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_spatial123_hypercharge_eq :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0)) 3) =
      7 / 36 := by
  rw [congrFun (fixedP506L0_Algebraic_p286Euler_zeroSlice_support SpatialE0) 3]
  rw [Pi.add_apply, p286CoordinateLiePairing_add_right,
    canonicalExterior_e0_spatial123_eq_negCharge,
    hypercharge_negCharge_pairing,
    temporal_chargedThreeForm_e0_spatial123_hypercharge]
  norm_num

theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_spatial123_hypercharge_ne_zero :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0)) 3) ≠ 0 := by
  rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_spatial123_hypercharge_eq]
  norm_num

theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_ne_zero :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 SpatialE0) ≠ 0 := by
  intro formZero
  apply
    fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_spatial123_hypercharge_ne_zero
  rw [formZero]
  change p286CoordinateLiePairing hyperchargeCoordinate 0 = 0
  rw [show (0 : P286CoordinateCarrier) =
      (0 : ℝ) • hyperchargeCoordinate by simp,
    p286CoordinateLiePairing_smul_right]
  norm_num

theorem fixedP506L0_U6_p286_zeroSlice_e0_spatial123_hypercharge_eq :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((diracDualFormNativePointwiseJointResidual Source U6
          (canonicalCauchySlicePoint 0 SpatialE0)).p286GaugeConnection 3) =
      7 / 36 := by
  rw [fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_canonicalExterior_add_temporalCharged]
  rw [Pi.add_apply, p286CoordinateLiePairing_add_right,
    canonicalExterior_e0_spatial123_eq_negCharge,
    hypercharge_negCharge_pairing,
    temporal_chargedThreeForm_e0_spatial123_hypercharge]
  norm_num

theorem fixedP506L0_U6_p286_zeroSlice_e0_ne_zero :
    (diracDualFormNativePointwiseJointResidual Source U6
      (canonicalCauchySlicePoint 0 SpatialE0)).p286GaugeConnection ≠ 0 := by
  intro formZero
  have evaluated := congrArg
    (fun form : P286GaugeThreeForm =>
      p286CoordinateLiePairing hyperchargeCoordinate (form 3)) formZero
  have zeroValue :
      p286CoordinateLiePairing hyperchargeCoordinate
          ((0 : P286GaugeThreeForm) 3) = 0 := by
    change p286CoordinateLiePairing hyperchargeCoordinate 0 = 0
    rw [show (0 : P286CoordinateCarrier) =
        (0 : ℝ) • hyperchargeCoordinate by simp,
      p286CoordinateLiePairing_smul_right]
    norm_num
  have contradiction : (7 / 36 : ℝ) = 0 := by
    rw [← fixedP506L0_U6_p286_zeroSlice_e0_spatial123_hypercharge_eq]
    exact evaluated.trans zeroValue
  norm_num at contradiction


/-- The nonzero P286 coordinate obstructs the complete U6 pointwise joint
zero fiber at the same generated occurrence. -/
theorem fixedP506L0_U6_not_onPointwiseJointZeroFiber_zeroSlice_e0 :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber Source U6
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  intro zeroFiber
  apply fixedP506L0_U6_p286_zeroSlice_e0_ne_zero
  unfold OnDiracDualFormNativePointwiseJointZeroFiber at zeroFiber
  have projected := congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection) zeroFiber
  simpa using projected

/-- Public occurrence form of the fixed U6 zero-slice obstruction. -/
theorem fixedP506L0_U6_not_onPointwiseJointZeroFiber_zeroSlice_spatialE0 :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) := by
  simpa [SpatialE0] using
    fixedP506L0_U6_not_onPointwiseJointZeroFiber_zeroSlice_e0

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286ZeroSliceObstruction
