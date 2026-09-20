import H0mework.Physics.FixedJoint.FixedSectionResponse
import H0mework.Physics.Gauge.GaugeAuxiliaryIntegratedVariation

/-!
# Fixed P506/L0 joint section-response residual

This module substitutes the one source/action-generated section successor
back into the authoritative repaired-root nine-coordinate residual.  The
residual is a downstream consistency readout only: no coordinate, support,
sign, branch, or zero-fiber witness enters the successor defined in the
preceding module.

The target of this file is the complete section, not an isolated convention
projection.  Coordinate lemmas below are assembled into that one carrier.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeScalarVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance sectionResponseResidualP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance sectionResponseResidualP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance sectionResponseResidualP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- The complete authoritative residual section on the one common successor. -/
def fixedP506FormNativeJointActionSuccessorResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSuccessor

/-! ## Repaired-root algebraic coordinates -/

theorem
    fixedP506FormNativeJointActionSuccessorResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506FormNativeJointActionSuccessorResidualSection point
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          FixedP506FormNativeJointActionSuccessor point) =
      0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      positiveSmoothUnifiedSource _ point

theorem
    fixedP506FormNativeJointActionSuccessorResidual_gravityAuxiliary_zero
    (point : BasePoint) :
    (fixedP506FormNativeJointActionSuccessorResidualSection point
      ).gravityAuxiliary = 0 := by
  have equation :
      FormNativeGravityAuxiliaryEquation
        FixedP506FormNativeJointActionSuccessor := by
    unfold FixedP506FormNativeJointActionSuccessor
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
        positiveSmoothUnifiedSource _
  exact congrFun equation point

/-! ## Canonical primitive-restart section

The restart successor was generated without inspecting the residual above.
We now substitute that whole successor into the same nine-coordinate carrier.
The P286 auxiliary coordinate is reduced to the explicit curvature,
live-coframe constitutive operator, and auxiliary normal forms.  This remains
a diagnostic equality: neither this vector nor any coordinatewise negative
is an input to a later action write.
-/

/-- The complete authoritative residual section of the canonical primitive
restart successor. -/
def fixedP506FormNativeJointActionSolvedSuccessorResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506FormNativeJointActionSolvedSuccessorResidualSection point
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          FixedP506FormNativeJointActionSolvedSuccessor point) =
      0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      positiveSmoothUnifiedSource _ point

theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityAuxiliary_zero
    (point : BasePoint) :
    (fixedP506FormNativeJointActionSolvedSuccessorResidualSection point
      ).gravityAuxiliary = 0 := by
  have equation :
      FormNativeGravityAuxiliaryEquation
        FixedP506FormNativeJointActionSolvedSuccessor := by
    unfold FixedP506FormNativeJointActionSolvedSuccessor
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
        positiveSmoothUnifiedSource _
  exact congrFun equation point

/-- Exact all-point coordinate normal form of the active P286 constitutive
residual on the canonical primitive restart. -/
def fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  c3h181FullCurvatureCoordinateNormalForm (-point) -
    formNativeP286CoordinateBlockwiseConstitutive
      (FixedP506FormNativeJointActionSolvedSuccessor.coframe point)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
      (c3h181FullAuxiliaryCoordinateNormalForm (-point))

/-- The same complete P286 vector displayed as the defect between the
identity-coframe constitutive image already generated by the source-owned
primitive and the authoritative live-coframe constitutive image. -/
def fixedP506FormNativeJointActionSolvedP286CoframeHodgeDefectNormalForm
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  liftGaugeTwoFormOperator
      (c3h181StrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
      (c3h181FullAuxiliaryCoordinateNormalForm (-point)) -
    formNativeP286CoordinateBlockwiseConstitutive
      (FixedP506FormNativeJointActionSolvedSuccessor.coframe point)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
      (c3h181FullAuxiliaryCoordinateNormalForm (-point))

theorem
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidual_eq_coframeHodgeDefect
    (point : BasePoint) :
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
        point =
      fixedP506FormNativeJointActionSolvedP286CoframeHodgeDefectNormalForm
        point := by
  unfold
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
    fixedP506FormNativeJointActionSolvedP286CoframeHodgeDefectNormalForm
  rw [c3h181FullAuxiliary_hodge_eq_curvature]

private theorem fixedP506FormNativeBlockwiseCoupling_same
    (parameter : ℝ) (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear
        parameter parameter parameter coordinate =
      parameter • coordinate := by
  apply p286CoordinateEquiv.symm.injective
  simp [formNativeP286BlockwiseCouplingCoordinateLinear,
    formNativeP286BlockwiseCouplingActualLinear]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

private theorem
    fixedP506FormNativeCoordinateBlockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [fixedP506FormNativeBlockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeJointActionSolvedSuccessor.coframe
        (canonicalCauchySlicePoint 0 space) =
      1 := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      1
  rw [fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  have zeroSlice := congrArg
    (fun current : StageNineCauchyState => current.coframe space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.coframe
        space at zeroSlice
  rw [zeroSlice,
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe_one]

/-- The complete P286 auxiliary residual vanishes on the entire generated
time-zero Cauchy slice.  This is a same-successor consistency readout, not an
input to a later write. -/
theorem
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
        (canonicalCauchySlicePoint 0 space) =
      0 := by
  rw [
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidual_eq_coframeHodgeDefect]
  unfold fixedP506FormNativeJointActionSolvedP286CoframeHodgeDefectNormalForm
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice,
    fixedP506FormNativeCoordinateBlockwiseConstitutive_eq_unified]
  exact sub_self _

theorem
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinate_normalForm
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        FixedP506FormNativeJointActionSolvedSuccessor point =
      fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
        point := by
  rw [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq]
  change
    holonomicP286GaugeCurvatureCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor point -
        formNativeP286CoordinateBlockwiseConstitutive
          (FixedP506FormNativeJointActionSolvedSuccessor.coframe point)
          _
          _
          _
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506FormNativeJointActionSolvedSuccessor point) =
      _
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm,
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm]
  rfl

theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_normalForm
    (point : BasePoint) :
    (fixedP506FormNativeJointActionSolvedSuccessorResidualSection point
      ).p286GaugeAuxiliary =
      formNativeP286GaugeCoordinateToActualLinear
        (fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
          point) := by
  funext pair
  apply p286CoordinateEquiv.injective
  have coordinateEquality := congrFun
    (fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinate_normalForm
      point) pair
  simpa [fixedP506FormNativeJointActionSolvedSuccessorResidualSection,
    diracDualFormNativeJointResidualSection,
    diracDualFormNativePointwiseJointResidual,
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate,
    formNativeP286GaugeActualToCoordinateLinear,
    formNativeP286GaugeCoordinateToActualLinear] using coordinateEquality

theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeJointActionSolvedSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary =
      0 := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_normalForm,
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidual_zeroSlice]
  exact map_zero formNativeP286GaugeCoordinateToActualLinear

/-- The three algebraic channels of the same canonical action successor
vanish together on its complete time-zero Cauchy slice. -/
theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidual_algebraic_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeJointActionSolvedSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).gravityMultiplier = 0 ∧
      (fixedP506FormNativeJointActionSolvedSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).gravityAuxiliary = 0 ∧
      (fixedP506FormNativeJointActionSolvedSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary = 0 := by
  exact
    ⟨fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityMultiplier_zero
        _,
      fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityAuxiliary_zero
        _,
      fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space⟩

/-- One carrier-level all-point normal form.  The two repaired-gravity
algebraic channels are discharged, the changed P286 constitutive channel is
in the explicit fixed-lineage coordinate chart, and the remaining six
channels are read directly from the same successor/action occurrence. -/
def fixedP506FormNativeJointActionSolvedSuccessorResidualSectionNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier := 0
    gravityAuxiliary := 0
    p286GaugeAuxiliary :=
      formNativeP286GaugeCoordinateToActualLinear
        (fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
          point)
    lorentzConnection :=
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeJointActionSolvedSuccessor point
    p286GaugeConnection :=
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeJointActionSolvedSuccessor point
    scalar := fun direction =>
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor direction point
    matter := fun direction =>
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor direction point
    conjugateMatter := fun direction =>
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor direction point
    coframe :=
      diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource
        point
        (toContinuumPointField
          FixedP506FormNativeJointActionSolvedSuccessor point) }

theorem
    fixedP506FormNativeJointActionSolvedSuccessorResidualSection_normalForm
    (point : BasePoint) :
    fixedP506FormNativeJointActionSolvedSuccessorResidualSection point =
      fixedP506FormNativeJointActionSolvedSuccessorResidualSectionNormalForm
        point := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityMultiplier_zero
        point
  · exact
      fixedP506FormNativeJointActionSolvedSuccessorResidual_gravityAuxiliary_zero
        point
  · exact
      fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_normalForm
        point
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
