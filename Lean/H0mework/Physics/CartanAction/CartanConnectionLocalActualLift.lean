import H0mework.Physics.CartanAction.CartanConnectionActualization
import H0mework.Physics.DualVariation.SpinTorsionAcceptance
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation
import H0mework.Physics.Exterior.JointActionLocalActualLift
import H0mework.Physics.Lorentz.LorentzConnectionAlgebraicCurrentRegularity

/-!
# Source/action-generated local Cartan connection field

This module upgrades the repaired-action pointwise Cartan actualizer to a
genuine local connection field.  Starting from the existing source/action
joint local actual, it recomputes at every base point

```text
W13 spin response -> typed torsion -> contorsion -> omegaLC + lift(q)
```

and installs only that generated connection field.  No origin value is
arbitrarily extended, and no curvature, torsion, response, equation,
stationarity receipt, or branch choice is accepted by the constructor.
Curvature remains the derived `d omega + omega wedge omega` readout of the
installed primitive field.

The central self-generation theorem proves that recomputing the action
response on the installed actual returns the same connection.  The apparent
self-reference is harmless because W13 reads only the coframe, matter, and
conjugate-matter fields, all of which the installer preserves definitionally.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionLocalActualLift

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeSpinTorsionAcceptance
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionAlgebraicCurrentRegularity
open StageNineLorentzConnectionActualVariationRegularity
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/- The typed torsion carrier was introduced algebraically.  For this module's
regularity proofs we transport the finite coordinate norm locally; no new
physical structure is added. -/
local instance cartanTorsionNormedAddCommGroup :
    NormedAddCommGroup PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedAddCommGroup

local instance cartanTorsionNormedSpace :
    NormedSpace ℝ PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedSpace ℝ

private def cartanTorsionCoordinateLinearEquiv :
    PointwiseCartanTorsionTwoForm ≃ₗ[ℝ]
      (Fin 6 → LorentzianIndex → ℝ) where
  toFun := PointwiseCartanTorsionTwoForm.component
  invFun := PointwiseCartanTorsionTwoForm.mk
  left_inv torsion := by cases torsion; rfl
  right_inv _ := rfl
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar torsion; rfl

local instance cartanTorsionFiniteDimensional :
    FiniteDimensional ℝ PointwiseCartanTorsionTwoForm :=
  FiniteDimensional.of_injective
    cartanTorsionCoordinateLinearEquiv.toLinearMap
    cartanTorsionCoordinateLinearEquiv.injective

/-- Linear lift from lowered bivector-one-form coordinates to the literal
Lorentz spin-connection carrier. -/
private def lorentzBivectorOneFormConnectionLinearMap :
    LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := lorentzSkewConnectionOfBivectorOneForm_add
  map_smul' := lorentzSkewConnectionOfBivectorOneForm_smul

/-! ## Typed/raw Cartan carrier seam -/

/-- Reconstructing the ordered raw torsion from the typed six-pair package
returns the repository's literal antisymmetric Cartan torsion.  This seam is
purely algebraic and requires no nondegeneracy assumption. -/
theorem rawPointwiseCartanTorsion_actualPointwiseCartanTorsionTwoForm
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection) :
    rawPointwiseCartanTorsion
        (actualPointwiseCartanTorsionTwoForm jet connection) =
      pointwiseCartanTorsion jet connection := by
  funext first second internal
  fin_cases first <;> fin_cases second <;>
    simp [rawPointwiseCartanTorsion,
      actualPointwiseCartanTorsionTwoForm,
      orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      pointwiseCartanTorsion, pairFirst, pairSecond,
      Fin.sum_univ_six]

/-- The typed KIN response is literally the action-facing raw
`star_I (T wedge e)` expression once the carrier reconstruction is exposed. -/
theorem cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm
    (coframe : LorentzianCoframe)
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection) :
    cartanTorsionThreeForm coframe
        (actualPointwiseCartanTorsionTwoForm jet connection) =
      internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm coframe
          (pointwiseCartanTorsion jet connection)) := by
  unfold cartanTorsionThreeForm cartanTorsionCoframeWedgeThreeForm
  rw [rawPointwiseCartanTorsion_actualPointwiseCartanTorsionTwoForm]

/-! ## Pointwise-recomputed field and installer -/

/-- Repaired-action Cartan connection recomputed at every point of the same
source/action-generated local base. -/
def sourceActionGeneratedDiracDualCartanConnectionField
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : LorentzConnectionField :=
  fun point =>
    diracDualFormNativeActionCartanConnectionAt source
      (sourceActionGeneratedJointLocalActualLift source state space) point

/-- Install only the pointwise-recomputed Cartan connection.  All primitive
non-connection fields remain those of the same source/action local base. -/
def sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  { sourceActionGeneratedJointLocalActualLift source state space with
    gravityConnection :=
      sourceActionGeneratedDiracDualCartanConnectionField source state space }

@[simp] theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).coframe =
      (sourceActionGeneratedJointLocalActualLift source state space).coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).gravityConnection =
      sourceActionGeneratedDiracDualCartanConnectionField
        source state space :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_matter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).matter =
      (sourceActionGeneratedJointLocalActualLift source state space).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_conjugateMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).conjugateMatter =
      (sourceActionGeneratedJointLocalActualLift source state space).conjugateMatter :=
  rfl

/-! ## W13 dependency blindness -/

/-- The repaired W13 response is insensitive to every point-field component
except the coframe, primal matter, and conjugate matter that occur in the
Dirac connection variation. -/
theorem diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEqual : first.coframe point = second.coframe point)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionSpinResponseAt source first point =
      diracDualFormNativeActionSpinResponseAt source second point := by
  ext internalPair triple
  change
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus first) point)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus second) point)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair))
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus,
    formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [coframeEqual, matterEqual, conjugateEqual]

/-- Zero-chart W13 is also blind to the base-point label itself: responses at
two contacts agree whenever the three primitive fields actually consumed by
the Dirac connection variation agree there.  This is the dependency seam
needed to prove spatial slice constancy without differentiating through the
complete KIN inverse by hand. -/
theorem diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeEqual : first.coframe firstPoint = second.coframe secondPoint)
    (matterEqual : first.matter firstPoint = second.matter secondPoint)
    (conjugateEqual :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint) :
    diracDualFormNativeActionSpinResponseAt source first firstPoint =
      diracDualFormNativeActionSpinResponseAt source second secondPoint := by
  ext internalPair triple
  change
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 firstPoint
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus first) firstPoint)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 secondPoint
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus second) secondPoint)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair))
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus,
    formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [coframeEqual, matterEqual, conjugateEqual]

/-- Installing the generated connection does not change the response that
generated it.  This is an exact dependency fact, not a fixed-point premise. -/
theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_spinResponse_eq_base
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          source state space) point =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedJointLocalActualLift source state space) point := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · rfl
  · rfl
  · rfl

/-! ## Smoothness of the generated response -/

/-- The repaired physical W13 response is smooth on every smooth,
nondegenerate actual.  This strengthens the earlier continuity readout by
transporting the already-proved smooth action coefficient through the exact
W13 coordinate duality. -/
theorem diracDualFormNativeActionSpinResponseAt_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point =>
      diracDualFormNativeActionSpinResponseAt source configuration point := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro triple
  let direction :=
    loweredLorentzBivectorOneFormCoordinate
      (missingTripleOfOneForm triple) internalPair
  have coefficientSmooth :=
    lorentzMatterSpinSourceCoefficient_contDiff source configuration smooth
      nondegenerate direction
  have responseCoefficientSmooth : ContDiff ℝ ∞ fun point =>
      formNativeLorentzMatterFirstCoefficient source 0 point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point)
        direction := by
    convert coefficientSmooth using 1
    funext point
    rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
    exact
      (lorentzMatterSpinSourceCoefficient_eq_formNativeLorentzMatterFirstCoefficient
        source configuration direction point).symm
  change ContDiff ℝ ∞ fun point =>
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
      formNativeLorentzMatterFirstCoefficient source 0 point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point)
        direction)
  exact (contDiff_const.mul responseCoefficientSmooth).neg

/-! ## Smooth pointwise KIN composition on the source/action local base -/

@[simp] theorem sourceActionGeneratedJointLocalActualLift_coframe_at
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (sourceActionGeneratedJointLocalActualLift source state space).coframe
        point =
      state.coframe space :=
  rfl

/-- The joint local base carries the same constant primitive coframe at every
point, so its actual Fréchet first jet is the zero-derivative jet. -/
theorem sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedJointLocalActualLift source state space).coframe
        point =
      ({ coframe := state.coframe space, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt]

/-- KIN-3 transports the smooth W13 field through its unique fixed-coframe
inverse. -/
theorem sourceActionGeneratedDiracDualCartanTorsionField_contDiff
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    ContDiff ℝ ∞ fun point =>
      diracDualFormNativeActionCartanTorsionAt source
        (sourceActionGeneratedJointLocalActualLift source state space) point := by
  let base := sourceActionGeneratedJointLocalActualLift source state space
  have baseSmooth : base.Smooth :=
    sourceActionGeneratedJointLocalActualLift_smooth source state space
  have baseNondegenerate : base.Nondegenerate :=
    sourceActionGeneratedJointLocalActualLift_nondegenerate source state space
      nondegenerate
  have responseSmooth :=
    diracDualFormNativeActionSpinResponseAt_contDiff source base baseSmooth
      baseNondegenerate
  have inverseSmooth :=
    (cartanTorsionThreeFormLinearEquiv (state.coframe space) nondegenerate)
      |>.symm.toContinuousLinearEquiv.contDiff.comp responseSmooth
  change ContDiff ℝ ∞ (fun point =>
    (cartanTorsionThreeFormLinearEquiv (state.coframe space) nondegenerate).symm
      (diracDualFormNativeActionSpinResponseAt source base point)) at inverseSmooth
  change ContDiff ℝ ∞ fun point =>
    cartanTorsionOfThreeForm (state.coframe space)
      (diracDualFormNativeActionSpinResponseAt source base point)
  simpa only [Function.comp_apply,
    cartanTorsionThreeFormLinearEquiv_symm_apply] using inverseSmooth

/-- KIN-2 transports the generated smooth torsion field through the unique
fixed-coframe contorsion inverse. -/
theorem sourceActionGeneratedDiracDualCartanContorsionField_contDiff
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    ContDiff ℝ ∞ fun point =>
      diracDualFormNativeActionCartanContorsionAt source
        (sourceActionGeneratedJointLocalActualLift source state space) point := by
  have torsionSmooth :=
    sourceActionGeneratedDiracDualCartanTorsionField_contDiff source state
      space nondegenerate
  have inverseSmooth :=
    (cartanContorsionTorsionLinearEquiv (state.coframe space) nondegenerate)
      |>.symm.toContinuousLinearEquiv.contDiff.comp torsionSmooth
  change ContDiff ℝ ∞ (fun point =>
    (cartanContorsionTorsionLinearEquiv (state.coframe space) nondegenerate).symm
      (diracDualFormNativeActionCartanTorsionAt source
        (sourceActionGeneratedJointLocalActualLift source state space) point)) at inverseSmooth
  change ContDiff ℝ ∞ fun point =>
    contorsionOfCartanTorsion (state.coframe space)
      (diracDualFormNativeActionCartanTorsionAt source
        (sourceActionGeneratedJointLocalActualLift source state space) point)
  simpa only [Function.comp_apply,
    cartanContorsionTorsionLinearEquiv_symm_apply] using inverseSmooth

/-- The complete KIN-4 connection field is smooth because the Levi--Civita
baseline is the fixed zero-derivative coframe jet and the generated
contorsion is transported by a finite-dimensional linear lift. -/
theorem sourceActionGeneratedDiracDualCartanConnectionField_contDiff
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    ContDiff ℝ ∞
      (sourceActionGeneratedDiracDualCartanConnectionField source state
        space) := by
  let base := sourceActionGeneratedJointLocalActualLift source state space
  let zeroJet : PointwiseLorentzianCoframeJet :=
    { coframe := state.coframe space, derivative := 0 }
  let contorsionField := fun point =>
    diracDualFormNativeActionCartanContorsionAt source base point
  have contorsionSmooth : ContDiff ℝ ∞ contorsionField := by
    simpa [base, contorsionField] using
      sourceActionGeneratedDiracDualCartanContorsionField_contDiff source
        state space nondegenerate
  have liftedSmooth :=
    lorentzBivectorOneFormConnectionLinearMap.toContinuousLinearMap.contDiff.comp
      contorsionSmooth
  change ContDiff ℝ ∞ (fun point =>
    lorentzSkewConnectionOfBivectorOneForm (contorsionField point)) at liftedSmooth
  have fieldIdentity :
      sourceActionGeneratedDiracDualCartanConnectionField source state space =
        fun point =>
          zeroJet.lorentzSpinConnection +
            lorentzSkewConnectionOfBivectorOneForm
              (contorsionField point) := by
    funext point
    unfold sourceActionGeneratedDiracDualCartanConnectionField
      diracDualFormNativeActionCartanConnectionAt
      cartanAffineSpinConnection
    rw [sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt]
  rw [fieldIdentity]
  exact contDiff_const.add liftedSmooth

theorem
    sourceActionGeneratedDiracDualCartanConnectionField_componentwiseSmooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0)
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      sourceActionGeneratedDiracDualCartanConnectionField source state space
        point direction internalOut internalIn := by
  exact contDiff_pi.mp
    (contDiff_pi.mp
      (contDiff_pi.mp
        (sourceActionGeneratedDiracDualCartanConnectionField_contDiff source
          state space nondegenerate)
        direction)
      internalOut)
    internalIn

/-! ## Installed actual and same-actual closure -/

theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedJointLocalActualLift_smooth source state space
  rcases baseSmooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      sourceActionGeneratedDiracDualCartanConnectionField_componentwiseSmooth
        source state space nondegenerate,
      gravityAuxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space).Nondegenerate := by
  exact sourceActionGeneratedJointLocalActualLift_nondegenerate source state
    space nondegenerate

/-- The installer preserves the algebraically generated `B = II+(e)` branch
of the same local base.  This is the multiplier-equation zero fiber, not a
stored simplicity certificate. -/
theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space) := by
  intro point
  rfl

theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space) := by
  intro point
  exact diracDualFormNativeActionCartanConnectionAt_lorentzSkew source
    (sourceActionGeneratedJointLocalActualLift source state space) point
    nondegenerate

/-- **No-circularity frontier.**  On the installed actual, recomputing W13
from the same source and then rerunning KIN-3/KIN-2/KIN-4 gives the installed
primitive connection at every point. -/
theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection_selfGenerated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          source state space) point := by
  change diracDualFormNativeActionCartanConnectionAt source
      (sourceActionGeneratedJointLocalActualLift source state space) point =
    diracDualFormNativeActionCartanConnectionAt source
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space) point
  unfold
    diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_spinResponse_eq_base]
  simp only [
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_coframe]

/-- Every point of the installed actual realizes the internally regenerated
typed Cartan response.  This remains producer soundness, not an independent
stationarity theorem. -/
theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_typedTorsionSpin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0)
    (point : BasePoint) :
    cartanTorsionThreeForm
        ((sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          source state space).coframe point)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
              source state space).coframe point)
          ((sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
            source state space).gravityConnection point)) =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          source state space) point := by
  rw [
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection_selfGenerated]
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    source
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space)
    point nondegenerate

/-- **Local producer checkpoint.**  The same smooth installed actual obeys
the existing raw repaired-root torsion--spin equation at every point. -/
theorem
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    FormNativeIIPlusTorsionSpinEquation source
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space) := by
  intro point
  rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_typedTorsionSpin
      source state space nondegenerate point

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionLocalActualLift
