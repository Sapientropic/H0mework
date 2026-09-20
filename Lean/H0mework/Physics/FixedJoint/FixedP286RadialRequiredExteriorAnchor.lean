import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.JointVariation.P286RequiredExteriorProfileNaturality
import H0mework.Physics.ActualGerms.FixedP286AuxiliaryFirstJet
import H0mework.Physics.ActualGerms.FixedZeroSliceCoframe
import H0mework.Physics.ActionForcing.FixedOccurrenceP286ZeroSliceActionProfile
import H0mework.Physics.ConnectionJets.P286GaussRadialSecondJetLift

/-!
# Fixed P506 radial required-exterior anchor

The fixed U6 mother action generates the complete zero-slice P286 Euler
profile `r² · vol₁₂₃(Q_action)`.  This module constructs its canonical
symmetric cubic primitive and subtracts it from the same-lineage algebraic
auxiliary field.  The resulting current-only anchor has pure exterior
derivative equal to the direct required exterior profile at every point of
the canonical time-zero slice.

No residual coordinate, support witness, target profile, endpoint shell,
branch, or equation receipt is accepted by the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualZeroSliceCoframe
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaussRadialSecondJetLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance radialAnchorP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

/-! ## Canonical primitive of the generated radial Euler profile -/

/-- The symmetric cubic primitive forced by the three spatial dimensions:
each spatial auxiliary coordinate receives `r² xᵢ / 5`. -/
def fixedP506L0P286RadialEulerAuxiliaryProfile
    (point : BasePoint) : P286GaugeTwoForm :=
  ∑ axis : Fin 3,
    ((1 / 5 : ℝ) *
      (p286SpatialRadiusSquared point * point axis.succ)) •
      p286GaussAuxiliaryAxisEmbedding
        fixedP506L0U6OccurrenceP286MotherActionCharge axis

theorem fixedP506L0P286RadialEulerAuxiliaryProfile_contDiff :
    ContDiff ℝ ∞ fixedP506L0P286RadialEulerAuxiliaryProfile := by
  unfold fixedP506L0P286RadialEulerAuxiliaryProfile
  apply ContDiff.sum
  intro axis _
  have coefficientSmooth : ContDiff ℝ ∞ (fun candidate : BasePoint =>
      (1 / 5 : ℝ) *
        (p286SpatialRadiusSquared candidate * candidate axis.succ)) := by
    simpa only [p286BaseCoordinate_apply, smul_eq_mul] using
      ContDiff.const_smul (R := ℝ) (1 / 5 : ℝ)
        (p286SpatialRadiusSquared_contDiff.mul
          (p286BaseCoordinate axis.succ).contDiff)
  exact coefficientSmooth.smul contDiff_const

/-- Whole actual carrying the radial primitive while retaining the algebraic
lineage in every other primitive field. -/
def fixedP506L0P286RadialEulerPrimitiveActual :
    StageNineHolonomicConfiguration :=
  { Algebraic with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (fixedP506L0P286RadialEulerAuxiliaryProfile point pair) }

@[simp] theorem fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryCoordinate
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RadialEulerPrimitiveActual point =
      fixedP506L0P286RadialEulerAuxiliaryProfile point := by
  funext pair
  exact p286CoordinateEquiv.apply_symm_apply _

private theorem fixedP506L0P286RadialCubicCoefficient_hasFDerivAt
    (point : BasePoint) (axis : Fin 3) :
    HasFDerivAt
      (fun candidate : BasePoint =>
        (1 / 5 : ℝ) *
          (p286SpatialRadiusSquared candidate * candidate axis.succ))
      ((1 / 5 : ℝ) •
        (p286SpatialRadiusSquared point • p286BaseCoordinate axis.succ +
          (point axis.succ) • (2 • p286SpatialRadialCovector point)))
      point := by
  have product :=
    (p286SpatialRadiusSquared_hasFDerivAt point).mul
      (p286BaseCoordinate axis.succ).hasFDerivAt
  have scaled := product.const_mul (1 / 5 : ℝ)
  simpa only [Pi.mul_apply, p286BaseCoordinate_apply] using scaled

private theorem fixedP506L0P286RadialCubicTerm_directionalDerivative
    (point : BasePoint) (axis : Fin 3)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate : BasePoint =>
          ((1 / 5 : ℝ) *
            (p286SpatialRadiusSquared candidate * candidate axis.succ)) •
              p286GaussAuxiliaryAxisEmbedding
                fixedP506L0U6OccurrenceP286MotherActionCharge axis)
        point direction =
      ((1 / 5 : ℝ) *
        (2 * point axis.succ *
            p286SpatialRadialCovector point
              (coordinateDirection direction) +
          p286SpatialRadiusSquared point *
            p286BaseCoordinate axis.succ
              (coordinateDirection direction))) •
        p286GaussAuxiliaryAxisEmbedding
          fixedP506L0U6OccurrenceP286MotherActionCharge axis := by
  unfold fieldDirectionalDerivative
  rw [((fixedP506L0P286RadialCubicCoefficient_hasFDerivAt point axis
    ).smul_const
      (p286GaussAuxiliaryAxisEmbedding
        fixedP506L0U6OccurrenceP286MotherActionCharge axis)).fderiv]
  simp
  ring

theorem fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryDerivative
    (point : BasePoint) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RadialEulerPrimitiveActual point direction =
      ∑ axis : Fin 3,
        ((1 / 5 : ℝ) *
          (2 * point axis.succ *
              p286SpatialRadialCovector point
                (coordinateDirection direction) +
            p286SpatialRadiusSquared point *
              p286BaseCoordinate axis.succ
                (coordinateDirection direction))) •
          p286GaussAuxiliaryAxisEmbedding
            fixedP506L0U6OccurrenceP286MotherActionCharge axis := by
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RadialEulerPrimitiveActual =
      fixedP506L0P286RadialEulerAuxiliaryProfile by
      funext candidate
      exact
        fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryCoordinate candidate]
  unfold fixedP506L0P286RadialEulerAuxiliaryProfile
  rw [StageNineDiracKineticLocalSpinMaurerCalculus.fieldDirectionalDerivative_finset_sum
    Finset.univ]
  · apply Finset.sum_congr rfl
    intro axis _
    exact
      fixedP506L0P286RadialCubicTerm_directionalDerivative
        point axis direction
  · intro axis _
    have coefficientSmooth : ContDiff ℝ ∞ (fun candidate : BasePoint =>
        (1 / 5 : ℝ) *
          (p286SpatialRadiusSquared candidate * candidate axis.succ)) := by
      simpa only [p286BaseCoordinate_apply, smul_eq_mul] using
        ContDiff.const_smul (R := ℝ) (1 / 5 : ℝ)
          (p286SpatialRadiusSquared_contDiff.mul
            (p286BaseCoordinate axis.succ).contDiff)
    exact coefficientSmooth.smul contDiff_const

/-- Machine-exact global primitive identity for the radial Euler term. -/
theorem fixedP506L0P286RadialEulerPrimitiveActual_exteriorDerivative
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        fixedP506L0P286RadialEulerPrimitiveActual point =
      p286SpatialRadiusSquared point •
        p286SpatialVolumeGaugeThreeForm
          fixedP506L0U6OccurrenceP286MotherActionCharge := by
  funext triple
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RadialEulerPrimitiveActual point =
      fun direction =>
        ∑ axis : Fin 3,
          ((1 / 5 : ℝ) *
            (2 * point axis.succ *
                p286SpatialRadialCovector point
                  (coordinateDirection direction) +
              p286SpatialRadiusSquared point *
                p286BaseCoordinate axis.succ
                  (coordinateDirection direction))) •
            p286GaussAuxiliaryAxisEmbedding
              fixedP506L0U6OccurrenceP286MotherActionCharge axis by
      funext direction
      exact
        fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryDerivative
          point direction]
  fin_cases triple <;>
    simp [pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      p286SpatialVolumeGaugeThreeForm, p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286SpatialRadialCovector_apply, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, p286BaseCoordinate_apply,
      coordinateDirection, threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_three,
      Fin.sum_univ_six]
  all_goals module

/-! ## Same-lineage corrected zero-slice anchor -/

/-- Formal action identity: the direct required profile is `dB - Euler` on
the same current. -/
theorem pointwiseDirectP286RequiredExteriorDerivative_eq_exterior_sub_euler
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    pointwiseDirectP286RequiredExteriorDerivative source current point =
      holonomicP286GaugeAuxiliaryExteriorDerivative current point -
        holonomicFormNativeP286GaugeEulerThreeForm source 0 current point := by
  unfold pointwiseDirectP286RequiredExteriorDerivative
    holonomicFormNativeP286GaugeEulerThreeForm
    formNativePhysicalChargedGaugeCurrentThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  abel

/-- The corrected anchor retains all algebraic-current primitives and
subtracts only the generated radial primitive from its P286 auxiliary. -/
def fixedP506L0P286RequiredExteriorZeroSliceAnchorActual :
    StageNineHolonomicConfiguration :=
  varyP286GaugeAuxiliaryCoordinate Algebraic
    fixedP506L0P286RadialEulerAuxiliaryProfile (-1)

@[simp] theorem
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryCoordinate
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual point =
      holonomicP286GaugeAuxiliaryCoordinate Algebraic point -
        fixedP506L0P286RadialEulerAuxiliaryProfile point := by
  funext pair
  simp [fixedP506L0P286RequiredExteriorZeroSliceAnchorActual,
    varyP286GaugeAuxiliaryCoordinate,
    holonomicP286GaugeAuxiliaryCoordinate, sub_eq_add_neg]

private theorem fixedP506L0P286Algebraic_auxiliary_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate Algebraic)
      (canonicalCauchySlicePoint 0 space) := by
  have coordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate Algebraic =
        holonomicP286GaugeAuxiliaryCoordinate Canonical := by
    simpa [Algebraic, Canonical, Source] using
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical
  rw [coordinateEq]
  apply
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
  change
    Matrix.det
      (Canonical.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0
  exact
    fixedP506L0P286CanonicalGeneratedActual_coframe_nondegenerate_zeroSlice
      space

theorem
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryDerivative
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) direction =
      p286GaugeAuxiliaryDirectionalDerivative Algebraic
          (canonicalCauchySlicePoint 0 space) direction -
        p286GaugeAuxiliaryDirectionalDerivative
          fixedP506L0P286RadialEulerPrimitiveActual
          (canonicalCauchySlicePoint 0 space) direction := by
  let point := canonicalCauchySlicePoint 0 space
  have algebraicDifferentiable : DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate Algebraic) point :=
    fixedP506L0P286Algebraic_auxiliary_differentiableAt_zeroSlice space
  have radialDifferentiable : DifferentiableAt ℝ
      fixedP506L0P286RadialEulerAuxiliaryProfile point :=
    (fixedP506L0P286RadialEulerAuxiliaryProfile_contDiff.differentiable
      (by simp)).differentiableAt
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual =
      fun candidate =>
        holonomicP286GaugeAuxiliaryCoordinate Algebraic candidate -
          fixedP506L0P286RadialEulerAuxiliaryProfile candidate by
      funext candidate
      exact
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryCoordinate
          candidate]
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RadialEulerPrimitiveActual =
      fixedP506L0P286RadialEulerAuxiliaryProfile by
      funext candidate
      exact
        fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryCoordinate candidate]
  unfold fieldDirectionalDerivative
  have derivativeEquality :=
    fderiv_sub algebraicDifferentiable radialDifferentiable
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] P286GaugeTwoForm =>
      derivative (coordinateDirection direction)) derivativeEquality
  change
    (fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate Algebraic -
          fixedP506L0P286RadialEulerAuxiliaryProfile)
        (canonicalCauchySlicePoint 0 space))
          (coordinateDirection direction) = _
  simpa [point] using applied

private theorem
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_sub_local
    (first second : LorentzianIndex → P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
        (first - second) =
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative first -
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative second := by
  funext triple
  simp [pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    orderedP286GaugeTwoFormComponent, Pi.sub_apply, smul_sub,
    Finset.sum_sub_distrib]
  module

theorem
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_exteriorDerivative
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
          (canonicalCauchySlicePoint 0 space) -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          fixedP506L0P286RadialEulerPrimitiveActual
          (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) =
      p286GaugeAuxiliaryDirectionalDerivative Algebraic
          (canonicalCauchySlicePoint 0 space) -
        p286GaugeAuxiliaryDirectionalDerivative
          fixedP506L0P286RadialEulerPrimitiveActual
          (canonicalCauchySlicePoint 0 space) by
      funext direction
      exact
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryDerivative
          space direction]
  exact
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_sub_local _ _

/-- Producer acceptance on the complete canonical zero slice. -/
theorem
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_exteriorDerivative_eq_directRequired
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) =
    pointwiseDirectP286RequiredExteriorDerivative Source Algebraic
        (canonicalCauchySlicePoint 0 space) := by
  rw [pointwiseDirectP286RequiredExteriorDerivative_eq_exterior_sub_euler]
  have radialEuler :
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 space) =
        p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
          p286SpatialVolumeGaugeThreeForm
            fixedP506L0U6OccurrenceP286MotherActionCharge := by
    simpa [Source, Algebraic] using
      (fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm
        space)
  rw [radialEuler]
  rw [← fixedP506L0P286RadialEulerPrimitiveActual_exteriorDerivative]
  exact
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_exteriorDerivative
      space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor
