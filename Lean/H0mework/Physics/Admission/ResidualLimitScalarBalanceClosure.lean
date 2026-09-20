import H0mework.Physics.GaugeAction.ResidualLimitP286ScalarFrozenTransportBoundary

/-!
# S9-C3h35: residual-limit scalar balance closure

This module evaluates the actual scalar source-only balance isolated by
C3h25/C3h26.  It accepts no zero premise, tuned source value, ansatz
coefficient, boundary constant, branch witness, shell, or stationarity receipt.
The finite SU(7) exterior action, actual affine P286 connection germ, and
constant generated vacuum force both the algebraic and differential scalar
terms to zero.  The conclusion closes the scalar coordinate in the declared
residual-limit matter-orbit class; it does not decide the P286 BF balance,
coframe equation, or joint stationarity.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitScalarBalanceClosure

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzCoverAndSpinDescent
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineJointResidualResponseSnapshot
open StageNineRequiredDifferentialResponseTransport
open StageNineResidualLimitMatterOrbitJointClassification
open StageNineResidualLimitP286ScalarFrozenTransportBoundary
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineScalarPointwiseEquation
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- One canonical scalar basis direction already occurring in the actual
source-generated joint breaking scalar. -/
def scalarBasisProbe : ScalarCoordinateCarrier :=
  scalarCoordinateEquiv (finiteGenerationBreakingTensor 0 0)

/-- One actual color-Cartan P286 one-form direction at spacetime direction
zero.  Returning through `p286CoordinateEquiv` keeps the arbitrary finite
coordinate chart out of the physical choice. -/
def colorCartanP286Probe : P286GaugeOneForm
  | 0 => p286CoordinateEquiv (colorCartanGenerator, 0, 0)
  | _ => 0

def colorCartanMotherDirection : SU7MotherLieMatrix :=
  p286LieBlockEmbed (colorCartanGenerator, 0, 0)

def colorMixingMotherDirection : SU7MotherLieMatrix :=
  p286LieBlockEmbed (colorMixingGenerator, 0, 0)

theorem fundamentalColorCartan_basis
    (index : SU7MotherIndex) :
    fundamentalMotherLieAction colorCartanMotherDirection
        (su7FundamentalBasis index) =
      (if index = colorZeroIndex then Complex.I
      else if index = colorOneIndex then -Complex.I else 0) •
        su7FundamentalBasis index := by
  fin_cases index <;> ext row <;> fin_cases row <;>
    norm_num [fundamentalMotherLieAction, colorCartanMotherDirection,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, colorCartanGenerator,
      colorCartanRaw, su7FundamentalBasis, Matrix.mulVecLin,
      Matrix.mulVec, Fin.sum_univ_seven, colorZeroIndex, colorOneIndex] <;>
    simp

theorem fundamentalColorMixing_basis
    (index : SU7MotherIndex) :
    fundamentalMotherLieAction colorMixingMotherDirection
        (su7FundamentalBasis index) =
      if index = colorZeroIndex then -su7FundamentalBasis colorOneIndex
      else if index = colorOneIndex then su7FundamentalBasis colorZeroIndex
      else 0 := by
  fin_cases index <;> ext row <;> fin_cases row <;>
    norm_num [fundamentalMotherLieAction, colorMixingMotherDirection,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, colorMixingGenerator,
      colorMixingRaw, su7FundamentalBasis, Matrix.mulVecLin,
      Matrix.mulVec, Fin.sum_univ_seven, colorZeroIndex, colorOneIndex] <;>
    simp [colorZeroIndex]

theorem exteriorMotherLieAction_basis
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree matrix (su7ExteriorBasis degree index) =
      exteriorBasisLieAction degree matrix index := by
  simp [exteriorMotherLieAction, Finsupp.single_apply]

theorem exteriorBasisInput_wedge_eq_basis
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    (exteriorPower.ιMulti ℂ degree) (exteriorBasisInput degree index) =
      su7ExteriorBasis degree index := by
  rw [su7ExteriorBasis, exteriorPower.basis_apply]
  rfl

theorem finiteGenerationScalarIndex_colorZero_mem
    (output input : Fin 2) :
    colorZeroIndex ∈ (finiteGenerationScalarIndex output input).1 := by
  fin_cases output <;> fin_cases input <;>
    simp [finiteGenerationScalarIndex, finiteGenerationScalarSubset,
      colorZeroIndex]

theorem finiteGenerationScalarIndex_colorOne_mem
    (output input : Fin 2) :
    colorOneIndex ∈ (finiteGenerationScalarIndex output input).1 := by
  fin_cases output <;> fin_cases input <;>
    simp [finiteGenerationScalarIndex, finiteGenerationScalarSubset,
      colorOneIndex]

theorem exteriorBasisLieAction_colorCartan_zero_of_colors_mem
    (degree : ℕ) (index : ExteriorBasisIndex degree)
    (colorZeroMem : colorZeroIndex ∈ index.1)
    (colorOneMem : colorOneIndex ∈ index.1) :
    exteriorBasisLieAction degree colorCartanMotherDirection index = 0 := by
  classical
  let zeroPosition : Fin degree :=
    (exteriorPositionEquiv index).symm ⟨colorZeroIndex, colorZeroMem⟩
  let onePosition : Fin degree :=
    (exteriorPositionEquiv index).symm ⟨colorOneIndex, colorOneMem⟩
  have zeroPositionValue :
      (exteriorPositionEquiv index zeroPosition).1 = colorZeroIndex := by
    exact congrArg Subtype.val
      ((exteriorPositionEquiv index).apply_symm_apply
        ⟨colorZeroIndex, colorZeroMem⟩)
  have onePositionValue :
      (exteriorPositionEquiv index onePosition).1 = colorOneIndex := by
    exact congrArg Subtype.val
      ((exteriorPositionEquiv index).apply_symm_apply
        ⟨colorOneIndex, colorOneMem⟩)
  have positionsDifferent : zeroPosition ≠ onePosition := by
    intro equality
    have valueEquality := congrArg
      (fun position => (exteriorPositionEquiv index position).1) equality
    rw [zeroPositionValue, onePositionValue] at valueEquality
    exact (by decide : colorZeroIndex ≠ colorOneIndex) valueEquality
  let term := fun position : Fin degree =>
    (exteriorPower.ιMulti ℂ degree)
      (exteriorBasisLieActionInput degree colorCartanMotherDirection index
        position)
  have zeroTerm : term zeroPosition =
      Complex.I • su7ExteriorBasis degree index := by
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorCartan_basis]
    simp only [zeroPositionValue, if_pos]
    have basisAtZero :
        su7FundamentalBasis colorZeroIndex =
          exteriorBasisInput degree index zeroPosition := by
      simp [exteriorBasisInput, zeroPositionValue]
    rw [basisAtZero, (exteriorPower.ιMulti ℂ degree).map_update_smul,
      Function.update_eq_self,
      exteriorBasisInput_wedge_eq_basis]
  have oneTerm : term onePosition =
      (-Complex.I) • su7ExteriorBasis degree index := by
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorCartan_basis]
    simp only [onePositionValue,
      show colorOneIndex ≠ colorZeroIndex by decide, if_false, if_pos]
    have basisAtOne :
        su7FundamentalBasis colorOneIndex =
          exteriorBasisInput degree index onePosition := by
      simp [exteriorBasisInput, onePositionValue]
    rw [basisAtOne, (exteriorPower.ιMulti ℂ degree).map_update_smul,
      Function.update_eq_self,
      exteriorBasisInput_wedge_eq_basis]
  have otherTerm (position : Fin degree)
      (notZero : position ≠ zeroPosition)
      (notOne : position ≠ onePosition) : term position = 0 := by
    have valueNotZero :
        (exteriorPositionEquiv index position).1 ≠ colorZeroIndex := by
      intro valueEquality
      apply notZero
      apply (exteriorPositionEquiv index).injective
      apply Subtype.ext
      exact valueEquality.trans zeroPositionValue.symm
    have valueNotOne :
        (exteriorPositionEquiv index position).1 ≠ colorOneIndex := by
      intro valueEquality
      apply notOne
      apply (exteriorPositionEquiv index).injective
      apply Subtype.ext
      exact valueEquality.trans onePositionValue.symm
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorCartan_basis]
    simp only [valueNotZero, valueNotOne, if_false,
      zero_smul]
    apply (exteriorPower.ιMulti ℂ degree).map_coord_zero position
    simp
  have termNormalForm (position : Fin degree) :
      term position =
        (if position = zeroPosition then
          Complex.I • su7ExteriorBasis degree index else 0) +
        (if position = onePosition then
          (-Complex.I) • su7ExteriorBasis degree index else 0) := by
    by_cases atZero : position = zeroPosition
    · subst position
      simp [zeroTerm, positionsDifferent]
    · by_cases atOne : position = onePosition
      · subst position
        simp [oneTerm, atZero]
      · simp [atZero, atOne, otherTerm position atZero atOne]
  unfold exteriorBasisLieAction
  change (∑ position : Fin degree, term position) = 0
  simp_rw [termNormalForm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  module

theorem exteriorBasisLieAction_colorMixing_zero_of_colors_mem
    (degree : ℕ) (index : ExteriorBasisIndex degree)
    (colorZeroMem : colorZeroIndex ∈ index.1)
    (colorOneMem : colorOneIndex ∈ index.1) :
    exteriorBasisLieAction degree colorMixingMotherDirection index = 0 := by
  classical
  let zeroPosition : Fin degree :=
    (exteriorPositionEquiv index).symm ⟨colorZeroIndex, colorZeroMem⟩
  let onePosition : Fin degree :=
    (exteriorPositionEquiv index).symm ⟨colorOneIndex, colorOneMem⟩
  have zeroPositionValue :
      (exteriorPositionEquiv index zeroPosition).1 = colorZeroIndex := by
    exact congrArg Subtype.val
      ((exteriorPositionEquiv index).apply_symm_apply
        ⟨colorZeroIndex, colorZeroMem⟩)
  have onePositionValue :
      (exteriorPositionEquiv index onePosition).1 = colorOneIndex := by
    exact congrArg Subtype.val
      ((exteriorPositionEquiv index).apply_symm_apply
        ⟨colorOneIndex, colorOneMem⟩)
  have positionsDifferent : zeroPosition ≠ onePosition := by
    intro equality
    have valueEquality := congrArg
      (fun position => (exteriorPositionEquiv index position).1) equality
    rw [zeroPositionValue, onePositionValue] at valueEquality
    exact (by decide : colorZeroIndex ≠ colorOneIndex) valueEquality
  let term := fun position : Fin degree =>
    (exteriorPower.ιMulti ℂ degree)
      (exteriorBasisLieActionInput degree colorMixingMotherDirection index
        position)
  have zeroTerm : term zeroPosition = 0 := by
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorMixing_basis]
    simp only [zeroPositionValue, if_pos]
    rw [show -su7FundamentalBasis colorOneIndex =
        (-1 : ℂ) • su7FundamentalBasis colorOneIndex by simp,
      (exteriorPower.ιMulti ℂ degree).map_update_smul]
    have duplicate :
        (Function.update (exteriorBasisInput degree index) zeroPosition
          (su7FundamentalBasis colorOneIndex)) zeroPosition =
        (Function.update (exteriorBasisInput degree index) zeroPosition
          (su7FundamentalBasis colorOneIndex)) onePosition := by
      simp [positionsDifferent.symm, exteriorBasisInput, onePositionValue]
    rw [(exteriorPower.ιMulti ℂ degree).map_eq_zero_of_eq
      _ duplicate positionsDifferent, smul_zero]
  have oneTerm : term onePosition = 0 := by
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorMixing_basis]
    simp only [onePositionValue,
      show colorOneIndex ≠ colorZeroIndex by decide, if_false, if_pos]
    have duplicate :
        (Function.update (exteriorBasisInput degree index) onePosition
          (su7FundamentalBasis colorZeroIndex)) onePosition =
        (Function.update (exteriorBasisInput degree index) onePosition
          (su7FundamentalBasis colorZeroIndex)) zeroPosition := by
      simp [positionsDifferent, exteriorBasisInput, zeroPositionValue]
    exact (exteriorPower.ιMulti ℂ degree).map_eq_zero_of_eq
      _ duplicate positionsDifferent.symm
  have otherTerm (position : Fin degree)
      (notZero : position ≠ zeroPosition)
      (notOne : position ≠ onePosition) : term position = 0 := by
    have valueNotZero :
        (exteriorPositionEquiv index position).1 ≠ colorZeroIndex := by
      intro valueEquality
      apply notZero
      apply (exteriorPositionEquiv index).injective
      apply Subtype.ext
      exact valueEquality.trans zeroPositionValue.symm
    have valueNotOne :
        (exteriorPositionEquiv index position).1 ≠ colorOneIndex := by
      intro valueEquality
      apply notOne
      apply (exteriorPositionEquiv index).injective
      apply Subtype.ext
      exact valueEquality.trans onePositionValue.symm
    unfold term
    rw [exteriorBasisLieActionTerm_eq_update]
    simp only [exteriorBasisInput]
    rw [fundamentalColorMixing_basis]
    simp only [valueNotZero, valueNotOne, if_false]
    apply (exteriorPower.ιMulti ℂ degree).map_coord_zero position
    simp
  have termZero (position : Fin degree) : term position = 0 := by
    by_cases atZero : position = zeroPosition
    · subst position
      exact zeroTerm
    · by_cases atOne : position = onePosition
      · subst position
        exact oneTerm
      · exact otherTerm position atZero atOne
  unfold exteriorBasisLieAction
  change (∑ position : Fin degree, term position) = 0
  exact Finset.sum_eq_zero fun position _ => termZero position

theorem finiteGenerationBreakingTensor_colorCartan_action_zero
    (output input : Fin 2) :
    exteriorMotherLieAction 4 colorCartanMotherDirection
        (finiteGenerationBreakingTensor output input) = 0 := by
  rw [finiteGenerationBreakingTensor, exteriorMotherLieAction_basis]
  exact exteriorBasisLieAction_colorCartan_zero_of_colors_mem 4
    (finiteGenerationScalarIndex output input)
    (finiteGenerationScalarIndex_colorZero_mem output input)
    (finiteGenerationScalarIndex_colorOne_mem output input)

theorem finiteGenerationBreakingTensor_colorMixing_action_zero
    (output input : Fin 2) :
    exteriorMotherLieAction 4 colorMixingMotherDirection
        (finiteGenerationBreakingTensor output input) = 0 := by
  rw [finiteGenerationBreakingTensor, exteriorMotherLieAction_basis]
  exact exteriorBasisLieAction_colorMixing_zero_of_colors_mem 4
    (finiteGenerationScalarIndex output input)
    (finiteGenerationScalarIndex_colorZero_mem output input)
    (finiteGenerationScalarIndex_colorOne_mem output input)

theorem finiteGenerationJointBreakingScalar_colorCartan_action_zero :
    exteriorMotherLieAction 4 colorCartanMotherDirection
        finiteGenerationJointBreakingScalar = 0 := by
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    finiteGenerationBreakingTensor_colorCartan_action_zero]

theorem finiteGenerationJointBreakingScalar_colorMixing_action_zero :
    exteriorMotherLieAction 4 colorMixingMotherDirection
        finiteGenerationJointBreakingScalar = 0 := by
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    finiteGenerationBreakingTensor_colorMixing_action_zero]

theorem sourceP286Potential_zero_embed :
    p286LieBlockEmbed
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 0) =
      positiveSmoothUnifiedSource.legacy.sigma • colorCartanMotherDirection := by
  have scale :
      realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
          (colorCartanGenerator, 0, 0) =
        positiveSmoothUnifiedSource.legacy.sigma •
          (colorCartanGenerator, 0, 0) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp [realScaleP286]
      · apply Subtype.ext
        simp [realScaleP286, realScaleHypercharge]
  rw [sourceP286Potential, scale, p286LieBlockEmbed_real_smul]
  rfl

theorem sourceP286Potential_one_embed :
    p286LieBlockEmbed
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 1) =
      positiveSmoothUnifiedSource.legacy.sigma • colorMixingMotherDirection := by
  have scale :
      realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
          (colorMixingGenerator, 0, 0) =
        positiveSmoothUnifiedSource.legacy.sigma •
          (colorMixingGenerator, 0, 0) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp [realScaleP286]
      · apply Subtype.ext
        simp [realScaleP286, realScaleHypercharge]
  rw [sourceP286Potential, scale, p286LieBlockEmbed_real_smul]
  rfl

theorem positiveSourceOriginScalarGaugeDerivative_eq_zero
    (direction : LorentzianIndex) :
    positiveSourceOriginScalarGaugeDerivative direction = 0 := by
  apply scalarCoordinateEquiv.symm.injective
  unfold positiveSourceOriginScalarGaugeDerivative scalarMotherLieAction
    sourceGeneratedVacuumCoordinates
  simp only [scalarCoordinateEquiv.symm_apply_apply, map_zero]
  rw [positive_sourceGeneratedVacuumBase]
  fin_cases direction
  · change
      exteriorMotherLieAction 4
          (p286LieBlockEmbed
            (sourceP286Potential positiveSmoothUnifiedSource.legacy 0))
          finiteGenerationJointBreakingScalar = 0
    rw [sourceP286Potential_zero_embed,
      exteriorMotherLieAction_real_smul, LinearMap.smul_apply,
      finiteGenerationJointBreakingScalar_colorCartan_action_zero, smul_zero]
  · change
      exteriorMotherLieAction 4
          (p286LieBlockEmbed
            (sourceP286Potential positiveSmoothUnifiedSource.legacy 1))
          finiteGenerationJointBreakingScalar = 0
    rw [sourceP286Potential_one_embed,
      exteriorMotherLieAction_real_smul, LinearMap.smul_apply,
      finiteGenerationJointBreakingScalar_colorMixing_action_zero, smul_zero]
  · simp [sourceP286Potential]
  · simp [sourceP286Potential]

theorem positiveSourceOriginScalarKineticAlgebraic_eq_zero
    (direction : ScalarCoordinateCarrier) :
    positiveSourceOriginScalarKineticAlgebraic direction = 0 := by
  simp [positiveSourceOriginScalarKineticAlgebraic,
    positiveSourceOriginScalarGaugeDerivative_eq_zero,
    scalarCoordinatePairingRe]

theorem positiveSourceOriginP286ScalarCurrent_eq_zero
    (direction : P286GaugeOneForm) :
    positiveSourceOriginP286ScalarCurrent direction = 0 := by
  simp [positiveSourceOriginP286ScalarCurrent,
    positiveSourceOriginScalarGaugeDerivative_eq_zero,
    scalarCoordinatePairingRe]

theorem positiveResidualLimitSixFieldCarrier_scalar_eq_constantVacuum :
    positiveResidualLimitSixFieldCarrier.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  change generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 point =
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  unfold generatedLocalVacuumCoordinates generatedScalarFrame
  rw [generatedTransition_normalized]
  exact scalarCoordinateAction_one _

theorem positiveResidualLimitSixFieldCarrier_gaugeConnectionCoordinate_eq
    (point : BasePoint) (direction : LorentzianIndex) :
    p286CoordinateEquiv
        (positiveResidualLimitSixFieldCarrier.gaugeConnection point direction) =
      sourceP286AffineConnectionCoordinate
        positiveSmoothUnifiedSource.legacy point direction := by
  change p286CoordinateEquiv
      (sourceP286AffineConnectionField
        positiveSmoothUnifiedSource.legacy point direction) = _
  simp [sourceP286AffineConnectionField]

theorem positiveResidualLimitScalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    positiveResidualLimitScalarCovariantDerivative point direction =
      scalarP286ActionBilinear
        (sourceP286AffineConnectionCoordinate
          positiveSmoothUnifiedSource.legacy point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold positiveResidualLimitScalarCovariantDerivative
  rw [positiveResidualLimitSixFieldCarrier_scalar_eq_constantVacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  change scalarMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          (sourceP286AffineConnectionCoordinate
            positiveSmoothUnifiedSource.legacy point direction)))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  rfl

theorem positiveResidualLimitScalarCovariantDerivative_directionalDerivative
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positiveResidualLimitScalarCovariantDerivative point formDirection)
        0 derivativeDirection =
      scalarP286ActionBilinear
        ((1 / 2 : ℝ) •
          p286CoordinateEquiv
            (sourceP286ExteriorDerivativeComponent
              positiveSmoothUnifiedSource.legacy derivativeDirection
              formDirection))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    sourceP286AffineConnectionCoordinate
      positiveSmoothUnifiedSource.legacy point formDirection
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    simpa [connection, sourceP286AffineConnectionField] using
      ((sourceP286AffineConnectionField_smooth
        positiveSmoothUnifiedSource.legacy formDirection).differentiable
          (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).hasFDerivAt.comp
      0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show (fun point =>
      positiveResidualLimitScalarCovariantDerivative point formDirection) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact positiveResidualLimitScalarCovariantDerivative_eq_fixedVacuumAction
      point formDirection]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change scalarP286ActionBilinear
      (fieldDirectionalDerivative connection 0 derivativeDirection)
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  rw [sourceP286AffineConnectionCoordinate_directionalDerivative_origin]

theorem positiveResidualLimitScalarCovariantDerivative_diagonalDerivative_eq_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positiveResidualLimitScalarCovariantDerivative point direction)
        0 direction = 0 := by
  rw [positiveResidualLimitScalarCovariantDerivative_directionalDerivative]
  fin_cases direction <;>
    simp [sourceP286ExteriorDerivativeComponent]

theorem positiveResidualLimitSixFieldCarrier_coframe_eq_canonical
    (point : BasePoint) :
    positiveResidualLimitSixFieldCarrier.coframe point =
      canonicalPhysicalSource.coframeAt point :=
  rfl

theorem positiveResidualLimitSixFieldCarrier_volume_eq_one
    (point : BasePoint) :
    abs (Matrix.det
      (positiveResidualLimitSixFieldCarrier.coframe point)) = 1 := by
  rw [positiveResidualLimitSixFieldCarrier_coframe_eq_canonical,
    canonicalPhysicalSource_coframeAt_det]
  norm_num

theorem positiveResidualLimitSixFieldCarrier_coframe_origin_eq_one :
    positiveResidualLimitSixFieldCarrier.coframe 0 = 1 := by
  rw [positiveResidualLimitSixFieldCarrier_coframe_eq_canonical,
    canonicalPhysicalSource_coframeAt_eq_transvection]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, Matrix.single]

theorem positiveResidualLimitSixFieldCarrier_metricInv_origin_eq_minkowski :
    (lorentzianMetricOfCoframe
      (positiveResidualLimitSixFieldCarrier.coframe 0))⁻¹ =
      minkowskiInternalMetric := by
  have minkowskiInverse :
      minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
    apply Matrix.inv_eq_left_inv
    rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num
  rw [positiveResidualLimitSixFieldCarrier_coframe_origin_eq_one]
  rw [show lorentzianMetricOfCoframe (1 : LorentzianCoframe) =
      minkowskiInternalMetric by
    simp [lorentzianMetricOfCoframe]]
  exact minkowskiInverse

theorem positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
    (first second : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      ((lorentzianMetricOfCoframe
        (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹ first second)) := by
  change Differentiable ℝ (fun point =>
    ((canonicalPhysicalSource.jetAt point).metric⁻¹ first second))
  exact (metricInv_componentwiseSmooth first second).differentiable (by simp)

theorem positiveResidualLimitScalarCovariantDerivative_origin_eq_zero
    (direction : LorentzianIndex) :
    positiveResidualLimitScalarCovariantDerivative 0 direction = 0 := by
  rw [positiveResidualLimitScalarCovariantDerivative_eq_fixedVacuumAction]
  rw [show sourceP286AffineConnectionCoordinate
      positiveSmoothUnifiedSource.legacy 0 direction =
        p286CoordinateEquiv
          (sourceP286Potential positiveSmoothUnifiedSource.legacy direction) by
    simp [sourceP286AffineConnectionCoordinate]]
  have actionAtPotential :
      scalarP286ActionBilinear
          (p286CoordinateEquiv
            (sourceP286Potential positiveSmoothUnifiedSource.legacy direction))
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
        positiveSourceOriginScalarGaugeDerivative direction := by
    unfold scalarP286ActionBilinear
      positiveSourceOriginScalarGaugeDerivative
    change scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (sourceP286Potential positiveSmoothUnifiedSource.legacy
                direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (sourceP286Potential positiveSmoothUnifiedSource.legacy direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
    rw [p286CoordinateEquiv.symm_apply_apply]
  rw [actionAtPotential,
    positiveSourceOriginScalarGaugeDerivative_eq_zero]

theorem positiveResidualLimitScalarCovariantDerivative_differentiable
    (direction : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      positiveResidualLimitScalarCovariantDerivative point direction) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    sourceP286AffineConnectionCoordinate
      positiveSmoothUnifiedSource.legacy point direction
  have connectionDifferentiable : Differentiable ℝ connection := by
    simpa [connection, sourceP286AffineConnectionField] using
      (sourceP286AffineConnectionField_smooth
        positiveSmoothUnifiedSource.legacy direction).differentiable (by simp)
  rw [show (fun point =>
      positiveResidualLimitScalarCovariantDerivative point direction) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact positiveResidualLimitScalarCovariantDerivative_eq_fixedVacuumAction
      point direction]
  exact (action.flip
    (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).differentiable.comp
      connectionDifferentiable

theorem positiveResidualLimitScalarDifferentialMomentum_eq_pairingSums
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) :
    positiveResidualLimitScalarDifferentialMomentum direction
        derivativeDirection point =
      (1 / 2 : ℝ) *
        ((∑ formDirection : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              derivativeDirection formDirection) *
            scalarCoordinatePairingRe direction
              (positiveResidualLimitScalarCovariantDerivative point
                formDirection)) +
        (∑ formDirection : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              formDirection derivativeDirection) *
            scalarCoordinatePairingRe
              (positiveResidualLimitScalarCovariantDerivative point
                formDirection) direction)) := by
  unfold positiveResidualLimitScalarDifferentialMomentum
  rw [positiveResidualLimitSixFieldCarrier_volume_eq_one, one_mul]
  fin_cases derivativeDirection <;>
    simp [scalarVariationDifferentialDirection, scalarCoordinatePairingRe,
      Fin.sum_univ_four] <;>
    ring

def positiveResidualLimitScalarMomentumLeftTerm
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  ((lorentzianMetricOfCoframe
    (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
      derivativeDirection formDirection) *
    scalarCoordinatePairingRe direction
      (positiveResidualLimitScalarCovariantDerivative point formDirection)

def positiveResidualLimitScalarMomentumRightTerm
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  ((lorentzianMetricOfCoframe
    (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
      formDirection derivativeDirection) *
    scalarCoordinatePairingRe
      (positiveResidualLimitScalarCovariantDerivative point formDirection)
      direction

theorem positiveResidualLimitScalarMomentumLeftPairing_differentiable
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      scalarCoordinatePairingRe direction
        (positiveResidualLimitScalarCovariantDerivative point formDirection)) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  exact pairing.differentiable.comp
    (positiveResidualLimitScalarCovariantDerivative_differentiable
      formDirection)

theorem positiveResidualLimitScalarMomentumRightPairing_differentiable
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      scalarCoordinatePairingRe
        (positiveResidualLimitScalarCovariantDerivative point formDirection)
        direction) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  exact pairing.differentiable.comp
    (positiveResidualLimitScalarCovariantDerivative_differentiable
      formDirection)

theorem positiveResidualLimitScalarMomentumLeftTerm_differentiable
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    Differentiable ℝ
      (positiveResidualLimitScalarMomentumLeftTerm direction
        derivativeDirection formDirection) := by
  exact (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
    derivativeDirection formDirection).mul
      (positiveResidualLimitScalarMomentumLeftPairing_differentiable
        direction formDirection)

theorem positiveResidualLimitScalarMomentumRightTerm_differentiable
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    Differentiable ℝ
      (positiveResidualLimitScalarMomentumRightTerm direction
        derivativeDirection formDirection) := by
  exact (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
    formDirection derivativeDirection).mul
      (positiveResidualLimitScalarMomentumRightPairing_differentiable
        direction formDirection)

theorem positiveResidualLimitScalarMomentumLeftPairing_directionalDerivative
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          scalarCoordinatePairingRe direction
            (positiveResidualLimitScalarCovariantDerivative point
              formDirection))
        0 derivativeDirection =
      scalarCoordinatePairingRe direction
        (fieldDirectionalDerivative
          (fun point =>
            positiveResidualLimitScalarCovariantDerivative point formDirection)
          0 derivativeDirection) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  have derivative := pairing.hasFDerivAt.comp 0
    (positiveResidualLimitScalarCovariantDerivative_differentiable
      formDirection).differentiableAt.hasFDerivAt
  change fieldDirectionalDerivative
      (fun point => pairing
        (positiveResidualLimitScalarCovariantDerivative point formDirection))
      0 derivativeDirection =
    pairing
      (fieldDirectionalDerivative
        (fun point =>
          positiveResidualLimitScalarCovariantDerivative point formDirection)
        0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing
      (positiveResidualLimitScalarCovariantDerivative point formDirection)) =
      pairing ∘ (fun point =>
        positiveResidualLimitScalarCovariantDerivative point formDirection) by
    rfl, derivative.fderiv]
  rfl

theorem positiveResidualLimitScalarMomentumRightPairing_directionalDerivative
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          scalarCoordinatePairingRe
            (positiveResidualLimitScalarCovariantDerivative point
              formDirection) direction)
        0 derivativeDirection =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative
          (fun point =>
            positiveResidualLimitScalarCovariantDerivative point formDirection)
          0 derivativeDirection) direction := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  have derivative := pairing.hasFDerivAt.comp 0
    (positiveResidualLimitScalarCovariantDerivative_differentiable
      formDirection).differentiableAt.hasFDerivAt
  change fieldDirectionalDerivative
      (fun point => pairing
        (positiveResidualLimitScalarCovariantDerivative point formDirection))
      0 derivativeDirection =
    pairing
      (fieldDirectionalDerivative
        (fun point =>
          positiveResidualLimitScalarCovariantDerivative point formDirection)
        0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing
      (positiveResidualLimitScalarCovariantDerivative point formDirection)) =
      pairing ∘ (fun point =>
        positiveResidualLimitScalarCovariantDerivative point formDirection) by
    rfl, derivative.fderiv]
  rfl

theorem fieldDirectionalDerivative_mul_of_right_zero
    (left right : BasePoint → ℝ)
    (leftDifferentiable : DifferentiableAt ℝ left 0)
    (rightDifferentiable : DifferentiableAt ℝ right 0)
    (rightZero : right 0 = 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => left point * right point) 0
        direction =
      left 0 * fieldDirectionalDerivative right 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_mul leftDifferentiable rightDifferentiable]
  simp [rightZero]

theorem positiveResidualLimitSixFieldCarrier_metricInv_origin_component
    (first second : LorentzianIndex) :
    ((lorentzianMetricOfCoframe
      (positiveResidualLimitSixFieldCarrier.coframe 0))⁻¹ first second) =
      minkowskiInternalMetric first second := by
  exact congrFun (congrFun
    positiveResidualLimitSixFieldCarrier_metricInv_origin_eq_minkowski first)
      second

theorem positiveResidualLimitScalarMomentumLeftTerm_diagonalDerivative_eq_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (positiveResidualLimitScalarMomentumLeftTerm direction
          derivativeDirection formDirection)
        0 derivativeDirection = 0 := by
  unfold positiveResidualLimitScalarMomentumLeftTerm
  rw [fieldDirectionalDerivative_mul_of_right_zero
    _ _
    (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
      derivativeDirection formDirection).differentiableAt
    (positiveResidualLimitScalarMomentumLeftPairing_differentiable
      direction formDirection).differentiableAt]
  · rw [positiveResidualLimitScalarMomentumLeftPairing_directionalDerivative,
      positiveResidualLimitSixFieldCarrier_metricInv_origin_component]
    fin_cases derivativeDirection <;> fin_cases formDirection <;>
      simp [minkowskiInternalMetric,
        positiveResidualLimitScalarCovariantDerivative_diagonalDerivative_eq_zero,
        scalarCoordinatePairingRe]
  · rw [positiveResidualLimitScalarCovariantDerivative_origin_eq_zero]
    simp [scalarCoordinatePairingRe]

theorem positiveResidualLimitScalarMomentumRightTerm_diagonalDerivative_eq_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (positiveResidualLimitScalarMomentumRightTerm direction
          derivativeDirection formDirection)
        0 derivativeDirection = 0 := by
  unfold positiveResidualLimitScalarMomentumRightTerm
  rw [fieldDirectionalDerivative_mul_of_right_zero
    _ _
    (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
      formDirection derivativeDirection).differentiableAt
    (positiveResidualLimitScalarMomentumRightPairing_differentiable
      direction formDirection).differentiableAt]
  · rw [positiveResidualLimitScalarMomentumRightPairing_directionalDerivative,
      positiveResidualLimitSixFieldCarrier_metricInv_origin_component]
    fin_cases derivativeDirection <;> fin_cases formDirection <;>
      simp [minkowskiInternalMetric,
        positiveResidualLimitScalarCovariantDerivative_diagonalDerivative_eq_zero,
        scalarCoordinatePairingRe]
  · rw [positiveResidualLimitScalarCovariantDerivative_origin_eq_zero]
    simp [scalarCoordinatePairingRe]

theorem positiveResidualLimitScalarMomentumLeftSum_differentiable
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      ∑ formDirection : LorentzianIndex,
        positiveResidualLimitScalarMomentumLeftTerm direction
          derivativeDirection formDirection point) := by
  change Differentiable ℝ
    (∑ formDirection : LorentzianIndex,
      positiveResidualLimitScalarMomentumLeftTerm direction
        derivativeDirection formDirection)
  exact Differentiable.sum fun formDirection _ =>
    positiveResidualLimitScalarMomentumLeftTerm_differentiable direction
      derivativeDirection formDirection

theorem positiveResidualLimitScalarMomentumRightSum_differentiable
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      ∑ formDirection : LorentzianIndex,
        positiveResidualLimitScalarMomentumRightTerm direction
          derivativeDirection formDirection point) := by
  change Differentiable ℝ
    (∑ formDirection : LorentzianIndex,
      positiveResidualLimitScalarMomentumRightTerm direction
        derivativeDirection formDirection)
  exact Differentiable.sum fun formDirection _ =>
    positiveResidualLimitScalarMomentumRightTerm_differentiable direction
      derivativeDirection formDirection

theorem positiveResidualLimitScalarMomentumLeftSum_diagonalDerivative_eq_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          ∑ formDirection : LorentzianIndex,
            positiveResidualLimitScalarMomentumLeftTerm direction
              derivativeDirection formDirection point)
        0 derivativeDirection = 0 := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sum (fun formDirection _ =>
    (positiveResidualLimitScalarMomentumLeftTerm_differentiable direction
      derivativeDirection formDirection).differentiableAt)]
  change (∑ formDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (positiveResidualLimitScalarMomentumLeftTerm direction
        derivativeDirection formDirection) 0 derivativeDirection) = 0
  exact Finset.sum_eq_zero fun formDirection _ =>
    positiveResidualLimitScalarMomentumLeftTerm_diagonalDerivative_eq_zero
      direction derivativeDirection formDirection

theorem positiveResidualLimitScalarMomentumRightSum_diagonalDerivative_eq_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          ∑ formDirection : LorentzianIndex,
            positiveResidualLimitScalarMomentumRightTerm direction
              derivativeDirection formDirection point)
        0 derivativeDirection = 0 := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sum (fun formDirection _ =>
    (positiveResidualLimitScalarMomentumRightTerm_differentiable direction
      derivativeDirection formDirection).differentiableAt)]
  change (∑ formDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (positiveResidualLimitScalarMomentumRightTerm direction
        derivativeDirection formDirection) 0 derivativeDirection) = 0
  exact Finset.sum_eq_zero fun formDirection _ =>
    positiveResidualLimitScalarMomentumRightTerm_diagonalDerivative_eq_zero
      direction derivativeDirection formDirection

theorem positiveResidualLimitScalarDifferentialMomentum_diagonalDerivative_eq_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (positiveResidualLimitScalarDifferentialMomentum direction
          derivativeDirection)
        0 derivativeDirection = 0 := by
  let leftSum := fun point =>
    ∑ formDirection : LorentzianIndex,
      positiveResidualLimitScalarMomentumLeftTerm direction
        derivativeDirection formDirection point
  let rightSum := fun point =>
    ∑ formDirection : LorentzianIndex,
      positiveResidualLimitScalarMomentumRightTerm direction
        derivativeDirection formDirection point
  have momentumFunction :
      positiveResidualLimitScalarDifferentialMomentum direction
          derivativeDirection =
        fun point => (1 / 2 : ℝ) * (leftSum point + rightSum point) := by
    funext point
    rw [positiveResidualLimitScalarDifferentialMomentum_eq_pairingSums]
    rfl
  have leftDifferentiable : DifferentiableAt ℝ leftSum 0 :=
    (positiveResidualLimitScalarMomentumLeftSum_differentiable direction
      derivativeDirection).differentiableAt
  have rightDifferentiable : DifferentiableAt ℝ rightSum 0 :=
    (positiveResidualLimitScalarMomentumRightSum_differentiable direction
      derivativeDirection).differentiableAt
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul
      (a := fun point => leftSum point + rightSum point)
      (leftDifferentiable.add rightDifferentiable)
      (1 / 2 : ℝ),
    fderiv_fun_add leftDifferentiable rightDifferentiable]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change (1 / 2 : ℝ) *
      (fieldDirectionalDerivative leftSum 0 derivativeDirection +
        fieldDirectionalDerivative rightSum 0 derivativeDirection) = 0
  rw [show fieldDirectionalDerivative leftSum 0 derivativeDirection = 0 by
      exact positiveResidualLimitScalarMomentumLeftSum_diagonalDerivative_eq_zero
        direction derivativeDirection,
    show fieldDirectionalDerivative rightSum 0 derivativeDirection = 0 by
      exact positiveResidualLimitScalarMomentumRightSum_diagonalDerivative_eq_zero
        direction derivativeDirection]
  norm_num

theorem positiveResidualLimitScalarDivergence_apply_eq_zero
    (direction : ScalarCoordinateCarrier) :
    positiveResidualLimitScalarDivergence direction = 0 := by
  unfold positiveResidualLimitScalarDivergence
  exact Finset.sum_eq_zero fun derivativeDirection _ =>
    positiveResidualLimitScalarDifferentialMomentum_diagonalDerivative_eq_zero
      direction derivativeDirection

theorem positiveResidualLimitScalarDivergence_eq_zero :
    positiveResidualLimitScalarDivergence = 0 := by
  funext direction
  exact positiveResidualLimitScalarDivergence_apply_eq_zero direction

theorem positiveResidualLimitScalarKineticBalance_eq_zero :
    positiveResidualLimitScalarKineticBalance = 0 := by
  funext direction
  unfold positiveResidualLimitScalarKineticBalance
  rw [positiveSourceOriginScalarKineticAlgebraic_eq_zero,
    positiveResidualLimitScalarDivergence_apply_eq_zero]
  norm_num

theorem residualLimitMatterOrbit_scalarResidual_origin_eq_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        configuration direction 0 = 0 := by
  rw [residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly
      n configuration belongs direction]
  exact congrFun positiveResidualLimitScalarKineticBalance_eq_zero direction

/-- No supplied zero certificate remains at the frozen transport mouth: the
actual scalar residual keep law follows from the source-only balance proof. -/
theorem residualLimitMatterOrbit_scalarActualResidual_transport_positiveClosure
    (initialIndex terminalIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsResidualLimitAndMatterOrbitAt terminalIndex terminal) :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        terminal direction 0) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (fun direction =>
            scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
              initial direction 0) := by
  exact
    (residualLimitMatterOrbit_scalarActualResidual_transport_iff_sourceBalance_zero
      initialIndex terminalIndex initial terminal initialExtends terminalExtends).2
        positiveResidualLimitScalarKineticBalance_eq_zero

/-- The frozen endpoint divergence now matches the framework-required scalar
response without accepting that match or a zero balance as a premise. -/
theorem residualLimitMatterOrbit_scalarRequiredResponse_matches_positiveClosure
    (initialIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource terminal
        direction 0) =
        (sourceSigmaRequiredDifferentialResponseSnapshot
          positiveSmoothUnifiedSource
          (pointwiseResidualResponseSnapshot positiveSmoothUnifiedSource
            initial 0)).scalarDifferentialMomentumDivergence := by
  exact
    (residualLimitMatterOrbit_scalarRequiredResponse_matches_iff_sourceBalance_zero
      initialIndex initial terminal initialExtends terminalExtends).2
        positiveResidualLimitScalarKineticBalance_eq_zero

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitScalarBalanceClosure
