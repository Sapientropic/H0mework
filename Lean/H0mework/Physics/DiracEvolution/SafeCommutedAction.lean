import H0mework.Physics.DiracEvolution.SafeCommutedPrincipal

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicRegularity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineMatterCoordinateFirstOrderCommutator
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeCauchySafeMatterVolterraLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineRadialCurveIntegralFirstJet
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance lowerP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance lowerP286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance lowerP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev BaseCurrent : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source
    fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev PreEC : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source BaseCurrent

private abbrev GlobalTemporal : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalTemporalCurrent Source BaseCurrent

private abbrev Safe : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

private theorem baseCurrent_smooth : BaseCurrent.Smooth :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    Source fixedP506L0CartanECConstraintCauchySafePreparedActual
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate

private theorem baseCurrent_nondegenerate : BaseCurrent.Nondegenerate := by
  intro point
  change Matrix.det
    (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

private theorem baseCurrent_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (BaseCurrent.coframe point) ≠ 0 := by
  change coframeTemporalPrincipalScalar
    (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic point

private theorem current_coframe_contDiff_one : ContDiff ℝ 1 Current.coframe := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact (holonomicCoframe_contDiff Safe
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_smooth).of_le
      (by norm_num)

private theorem current_nondegenerate (point : BasePoint) :
    Matrix.det (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic point

private theorem current_gravityConnection_component_contDiff_one
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ 1 (fun point ↦
      Current.gravityConnection point direction internalOut internalIn) := by
  have incrementRegular : ContDiff ℝ 1
      (cauchySafeJointGlobalECRadialIncrement Source PreEC) :=
    radialCurveIntegral_contDiff_one_of_contDiff
      (cauchySafeJointGlobalECJetCLM Source PreEC)
      fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff_one
  have liftedRegular : ContDiff ℝ 1 (fun point ↦
      radialLorentzConnectionLiftCLM
        (cauchySafeJointGlobalECRadialIncrement Source PreEC point)) :=
    radialLorentzConnectionLiftCLM.contDiff.comp incrementRegular
  have coordinateRegular : ContDiff ℝ 1 (fun point ↦
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement Source PreEC point))) :=
    (radialLorentzConnectionCoordinateCLM direction internalOut internalIn
      ).contDiff.comp liftedRegular
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ 1 (fun point ↦
    PreEC.gravityConnection 0 direction internalOut internalIn +
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement Source PreEC point)))
  exact contDiff_const.add coordinateRegular

private theorem scalarAcceleration_contDiff : ContDiff ℝ ∞
    (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent) :=
  completeJointCauchySafeScalarAccelerationProfile_contDiff Source BaseCurrent
    baseCurrent_smooth baseCurrent_nondegenerate baseCurrent_noncharacteristic

private theorem current_scalar_contDiff_one : ContDiff ℝ 1 Current.scalar := by
  have baseRegular : ContDiff ℝ 1 BaseCurrent.scalar :=
    baseCurrent_smooth.2.2.2.2.2.2.1.of_le (by norm_num)
  have primitiveRegular : ContDiff ℝ 1
      (canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent)) :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff _
      scalarAcceleration_contDiff).of_le (by norm_num)
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ 1
    (BaseCurrent.scalar + canonicalTimeSecondPrimitive
      (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent))
  exact baseRegular.add primitiveRegular

private theorem current_gaugeConnection_contDiff_one
    (direction : LorentzianIndex) :
    ContDiff ℝ 1 (fun point ↦
      p286CoordinateEquiv (Current.gaugeConnection point direction)) := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ 1 (fun point ↦
    p286CoordinateEquiv (BaseCurrent.gaugeConnection point direction))
  exact (baseCurrent_smooth.2.2.2.2.1 direction).of_le (by norm_num)

/-- Canonical one-mode embedding of one physical matter fiber. -/
def matterCoordinateFiberCoefficientLinear :
    MatterCoordinateCarrier →ₗ[ℝ] DiracMatterGalerkinCoefficient 1 where
  toFun coordinates := WithLp.toLp 2 fun index ↦ coordinates index.2
  map_add' first second := by
    apply PiLp.ext
    intro index
    rfl
  map_smul' parameter coordinates := by
    apply PiLp.ext
    intro index
    rfl

def matterCoordinateFiberCoefficientCLM :
    MatterCoordinateCarrier →L[ℝ] DiracMatterGalerkinCoefficient 1 :=
  ⟨matterCoordinateFiberCoefficientLinear,
    matterCoordinateFiberCoefficientLinear.continuous_of_finiteDimensional⟩

/-- Coordinate velocity of the source-owned constant section. -/
def fixedConstantCoordinateVelocityCLM
    (point : BasePoint) : MatterRealEnd :=
  (constantVelocityCLM point).comp matterCoordinateFiberCoefficientCLM

theorem fixedConstantCoordinateVelocityCLM_continuous :
    Continuous fixedConstantCoordinateVelocityCLM := by
  exact constantVelocityCLM_continuous.clm_comp continuous_const

private def constantMatterField
    (coordinates : MatterCoordinateCarrier) :
    BasePoint → DiracExteriorMatterCarrier :=
  fun _ ↦ matterCoordinateEquiv.symm coordinates

theorem fixedConstantCoordinateVelocityCLM_apply
    (point : BasePoint)
    (coordinates : MatterCoordinateCarrier) :
    fixedConstantCoordinateVelocityCLM point coordinates =
      cauchySafeMatterVolterraVelocity Current
        (constantMatterField coordinates) point := by
  change cauchySafeMatterVolterraVelocity Current
      (cauchySafeMatterGalerkinSynthesis (fun _ _ ↦ 1)
        (matterCoordinateFiberCoefficientCLM coordinates)) point =
    cauchySafeMatterVolterraVelocity Current
      (constantMatterField coordinates) point
  apply congrArg
    (cauchySafeMatterVolterraVelocity Current · point)
  funext candidate
  apply matterCoordinateEquiv.injective
  rw [cauchySafeMatterGalerkinSynthesis_coordinates, Fin.sum_univ_one]
  ext coordinate
  simp [diracMatterGalerkinCoefficientMode,
    matterCoordinateFiberCoefficientCLM,
    matterCoordinateFiberCoefficientLinear, constantMatterField]

private theorem fixedConstantCoordinateVelocityCLM_apply_contDiff_one
    (coordinates : MatterCoordinateCarrier) :
    ContDiff ℝ 1 (fun point ↦
      fixedConstantCoordinateVelocityCLM point coordinates) := by
  rw [show (fun point ↦
      fixedConstantCoordinateVelocityCLM point coordinates) =
      cauchySafeMatterVolterraVelocity Current
        (constantMatterField coordinates) by
    funext point
    exact fixedConstantCoordinateVelocityCLM_apply point coordinates]
  rw [contDiff_iff_contDiffAt]
  intro point
  exact cauchySafeMatterVolterraVelocity_contDiffAt_of_local
    (order := 1) Current (constantMatterField coordinates) point
    (current_nondegenerate point) (current_noncharacteristic point)
    current_coframe_contDiff_one.contDiffAt
    (fun direction internalOut internalIn ↦
      (current_gravityConnection_component_contDiff_one direction internalOut
        internalIn).contDiffAt)
    current_scalar_contDiff_one.contDiffAt
    (by
      rw [show (fun target ↦
          matterCoordinateEquiv (constantMatterField coordinates target)) =
        (fun _ : BasePoint ↦ coordinates) by
          funext target
          simp [constantMatterField]]
      have regular : ContDiffAt ℝ ((1 : WithTop ℕ∞) + 1)
          (fun _ : BasePoint ↦ coordinates) point := contDiffAt_const
      convert regular using 1
      norm_num)
    (fun direction ↦
      (current_gaugeConnection_contDiff_one direction).contDiffAt)

theorem fixedConstantCoordinateVelocityCLM_contDiff_one :
    ContDiff ℝ 1 fixedConstantCoordinateVelocityCLM := by
  rw [contDiff_clm_apply_iff]
  exact fixedConstantCoordinateVelocityCLM_apply_contDiff_one

/-- Fixed lower coefficient reconstructed from the same source-owned constant
section response and temporal Hermitian principal. -/
def fixedMatterLowerCoefficient (point : BasePoint) : MatterRealEnd :=
  -(fixedEvolutionPrincipalCoordinateCLM 0 point).comp
    (fixedConstantCoordinateVelocityCLM point)

theorem fixedMatterLowerCoefficient_continuous :
    Continuous fixedMatterLowerCoefficient := by
  exact
    (fixedEvolutionPrincipalCoordinateCLM_contDiff 0).continuous.clm_comp
      fixedConstantCoordinateVelocityCLM_continuous |>.neg

theorem fixedMatterLowerCoefficient_contDiff_one :
    ContDiff ℝ 1 fixedMatterLowerCoefficient := by
  rw [contDiff_clm_apply_iff]
  intro coordinates
  change ContDiff ℝ 1 (fun point ↦
    -fixedEvolutionPrincipalCoordinateCLM 0 point
      (fixedConstantCoordinateVelocityCLM point coordinates))
  exact ((fixedEvolutionPrincipalCoordinateCLM_contDiff 0).clm_apply
    (fixedConstantCoordinateVelocityCLM_contDiff_one.clm_apply
      contDiff_const)).neg

theorem fixedMatterLowerCoefficient_apply
    (point : BasePoint)
    (coordinates : MatterCoordinateCarrier) :
    fixedMatterLowerCoefficient point coordinates =
      -matterCoordinateEquiv
        (diracMatrixMatterAction
          (fixedEvolutionPrincipal 0 point)
          (matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity Current
              (constantMatterField coordinates) point))) := by
  rw [fixedMatterLowerCoefficient]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    fixedConstantCoordinateVelocityCLM_apply]
  rw [show fixedEvolutionPrincipalCoordinateCLM 0 point =
      diracMatrixMatterCoordinateCLM
        (fixedEvolutionPrincipal 0 point) by rfl]
  exact congrArg Neg.neg
    (diracMatrixMatterCoordinateCLM_apply
      (fixedEvolutionPrincipal 0 point)
      (cauchySafeMatterVolterraVelocity Current
        (constantMatterField coordinates) point))

private def centeredMatterField
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : BasePoint → DiracExteriorMatterCarrier :=
  fun candidate ↦ matterCoordinateEquiv.symm (field candidate - field point)

private def coordinateRawDirectionalDerivative
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fieldDirectionalDerivative field point direction)

private theorem coordinateRawDirectionalDerivative_centeredMatterField
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (fieldDifferentiable : DifferentiableAt ℝ field point) :
    matterCoordinateEquiv.symm
        (fieldDirectionalDerivative
          (fun candidate ↦
            matterCoordinateEquiv
              (centeredMatterField field point candidate))
          point direction) =
      coordinateRawDirectionalDerivative field point direction := by
  have constantDifferentiable : DifferentiableAt ℝ
      (fun _candidate : BasePoint ↦ field point) point :=
    differentiableAt_const _
  have derivativeSub :=
    fderiv_fun_sub fieldDifferentiable constantDifferentiable
  unfold centeredMatterField coordinateRawDirectionalDerivative
    fieldDirectionalDerivative
  simp only [matterCoordinateEquiv.apply_symm_apply]
  rw [derivativeSub]
  simp

/-- The source-native temporal solve closes the centered spatial principal
without any supplied residual or target. -/
theorem fixedCenteredVolterraVelocity_coordinateLaw
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point) :
    fixedEvolutionPrincipalCoordinateCLM 0 point
          (cauchySafeMatterVolterraVelocity Current
            (centeredMatterField field point) point) +
        ∑ direction : Fin 3,
          fixedEvolutionPrincipalCoordinateCLM direction.succ point
            (fieldDirectionalDerivative field point direction.succ) =
      0 := by
  let centered := centeredMatterField field point
  let actual := cauchySafeMatterCandidateActual Current centered
  have centeredAt : centered point = 0 := by
    simp [centered, centeredMatterField]
  have actualNoncharacteristic :
      coframeTemporalPrincipalScalar (actual.coframe point) ≠ 0 := by
    change coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0
    rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
    exact
      fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic
        point
  have actionLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      actual point actualNoncharacteristic
  have connectionZero (direction : LorentzianIndex) :
      holonomicMatterConnectionAction actual point direction = 0 := by
    simp [holonomicMatterConnectionAction, actual,
      cauchySafeMatterCandidateActual, centeredAt]
  have timeDerivativeEq :
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          actual point =
        matterCoordinateEquiv.symm
          (cauchySafeMatterVolterraVelocity Current centered point) := by
    unfold cauchySafeMatterVolterraVelocity
    rw [matterCoordinateEquiv.symm_apply_apply]
    unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    rw [connectionZero, sub_zero]
  have spatialDerivativeEq (direction : Fin 3) :
      holonomicMatterCovariantDerivative actual point direction.succ =
        coordinateRawDirectionalDerivative field point direction.succ := by
    rw [← coordinateRawDirectionalDerivative_centeredMatterField field point
      direction.succ fieldDifferentiable]
    simp [holonomicMatterCovariantDerivative, actual,
      cauchySafeMatterCandidateActual, centeredAt, centered]
  change CurrentCoframeMatterTemporalActionLaw (actual.coframe point)
      (holonomicDiracDualCurrentCoframeMatterKnownVector actual point)
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        actual point) at actionLaw
  have transformed := congrArg identityCoframeMatterTimePrincipal actionLaw
  have timeTransform :
      identityCoframeMatterTimePrincipal
          (currentCoframeMatterTemporalPrincipal (actual.coframe point)
            (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
              actual point)) =
        diracMatrixMatterAction
          (coframeCoordinateDiracEvolutionPrincipal
            (Current.coframe point) 0)
          (matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity Current centered point)) := by
    unfold currentCoframeMatterTemporalPrincipal
    rw [timeDerivativeEq]
    exact identityCoframeMatterTimePrincipal_coordinatePrincipal
      (Current.coframe point) 0 _
  have identityAdd (first second : DiracExteriorMatterCarrier) :
      identityCoframeMatterTimePrincipal (first + second) =
        identityCoframeMatterTimePrincipal first +
          identityCoframeMatterTimePrincipal second := by
    simp [identityCoframeMatterTimePrincipal]
  have identityZero :
      identityCoframeMatterTimePrincipal
          (0 : DiracExteriorMatterCarrier) = 0 := by
    simp [identityCoframeMatterTimePrincipal]
  have identitySpatialSum
      (fields : Fin 3 → DiracExteriorMatterCarrier) :
      identityCoframeMatterTimePrincipal
          (Complex.I • ∑ direction, fields direction) =
        ∑ direction,
          identityCoframeMatterTimePrincipal
            (Complex.I • fields direction) := by
    simp [identityCoframeMatterTimePrincipal, Finset.smul_sum, map_sum]
  have knownTransform :
      identityCoframeMatterTimePrincipal
          (holonomicDiracDualCurrentCoframeMatterKnownVector actual point) =
        ∑ direction : Fin 3,
          diracMatrixMatterAction
            (coframeCoordinateDiracEvolutionPrincipal
              (Current.coframe point) direction.succ)
            (coordinateRawDirectionalDerivative field point
              direction.succ) := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    rw [identityAdd]
    have yukawaZero :
        diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (actual.scalar point))
            (actual.matter point) = 0 := by
      simp [actual, cauchySafeMatterCandidateActual, centeredAt]
    rw [yukawaZero, identityZero, add_zero, identitySpatialSum]
    apply Finset.sum_congr rfl
    intro direction _
    rw [spatialDerivativeEq direction]
    exact identityCoframeMatterTimePrincipal_coordinatePrincipal
      (Current.coframe point) direction.succ _
  change identityCoframeMatterTimePrincipal
      (currentCoframeMatterTemporalPrincipal (actual.coframe point)
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
            actual point) +
        holonomicDiracDualCurrentCoframeMatterKnownVector actual point) =
      identityCoframeMatterTimePrincipal 0 at transformed
  rw [identityAdd, timeTransform, knownTransform, identityZero] at transformed
  have mapped := congrArg matterCoordinateEquiv transformed
  simpa [fixedEvolutionPrincipalCoordinateCLM,
    diracMatrixMatterCoordinateCLM_apply, fixedEvolutionPrincipal,
    coordinateRawDirectionalDerivative, centered, map_add, map_sum] using mapped

private def coordinateMatterField
    (field : BasePoint → MatterCoordinateCarrier) :
    BasePoint → DiracExteriorMatterCarrier :=
  fun point ↦ matterCoordinateEquiv.symm (field point)

theorem fixedVolterraVelocity_eq_constant_add_centered
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point) :
    cauchySafeMatterVolterraVelocity Current
        (coordinateMatterField field) point =
      fixedConstantCoordinateVelocityCLM point (field point) +
        cauchySafeMatterVolterraVelocity Current
          (centeredMatterField field point) point := by
  have constantDifferentiable : DifferentiableAt ℝ
      (fun candidate ↦ matterCoordinateEquiv
        (constantMatterField (field point) candidate)) point := by
    simp [constantMatterField]
  have centeredDifferentiable : DifferentiableAt ℝ
      (fun candidate ↦ matterCoordinateEquiv
        (centeredMatterField field point candidate)) point := by
    simpa [centeredMatterField] using fieldDifferentiable.sub
      (differentiableAt_const (c := field point))
  have fieldDecomposition :
      coordinateMatterField field =
        constantMatterField (field point) + centeredMatterField field point := by
    funext candidate
    apply matterCoordinateEquiv.injective
    simp [coordinateMatterField, constantMatterField, centeredMatterField]
  rw [fieldDecomposition,
    cauchySafeMatterVolterraVelocity_add Current
      (constantMatterField (field point)) (centeredMatterField field point)
      point constantDifferentiable centeredDifferentiable,
    fixedConstantCoordinateVelocityCLM_apply]

/-- The complete fixed first-order action operator is exactly the temporal
Volterra defect multiplied by the source-owned positive principal. -/
theorem fixedMatterFirstOrderOperator_eq_temporalVolterraDefect
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point) :
    matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point =
      fixedEvolutionPrincipalCoordinateCLM 0 point
        (fieldDirectionalDerivative field point 0 -
          cauchySafeMatterVolterraVelocity Current
            (coordinateMatterField field) point) := by
  have centeredLaw :=
    fixedCenteredVolterraVelocity_coordinateLaw field point fieldDifferentiable
  have spatialLaw :
      (∑ direction : Fin 3,
        fixedEvolutionPrincipalCoordinateCLM direction.succ point
          (fieldDirectionalDerivative field point direction.succ)) =
        -fixedEvolutionPrincipalCoordinateCLM 0 point
          (cauchySafeMatterVolterraVelocity Current
            (centeredMatterField field point) point) :=
    eq_neg_of_add_eq_zero_right centeredLaw
  have volterraDecomposition :=
    fixedVolterraVelocity_eq_constant_add_centered field point
      fieldDifferentiable
  unfold matterCoordinateFirstOrderOperator fixedMatterLowerCoefficient
  rw [Fin.sum_univ_succ, spatialLaw, volterraDecomposition]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, map_sub, map_add]
  abel

/-- Complete fixed-source commuted action law.  The only forcing is the
derivative of coefficients already emitted by the mother action. -/
theorem fixedMatterFirstOrderOperator_directionalDerivative
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field)
        point commutedDirection =
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fun candidate ↦
            fieldDirectionalDerivative field candidate commutedDirection)
          point +
        (∑ direction : LorentzianIndex,
          (fieldDirectionalDerivative
              (fixedEvolutionPrincipalCoordinateCLM direction) point
              commutedDirection)
            (fieldDirectionalDerivative field point direction)) +
        (fieldDirectionalDerivative fixedMatterLowerCoefficient point
            commutedDirection)
          (field point) := by
  exact matterCoordinateFirstOrderOperator_directionalDerivative
    fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient field
    fixedEvolutionPrincipalCoordinateCLM_contDiff
    fixedMatterLowerCoefficient_contDiff_one fieldSmooth point
    commutedDirection

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
