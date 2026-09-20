import H0mework.Physics.Coframe.CoframeNativeMatterDualGlobalRadialActionWrite
import H0mework.Physics.Coframe.CoframeNativeMatterGlobalRadialRegularity
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.Source.RadialCurveIntegralSmoothRegularity
import H0mework.Physics.Exterior.GravityReactionInstallation

/-!
# Global regularity of the coframe-native adjoint response one-form

The generated frame-adjoint radial writer requires only the fields it
actually reads.  This module derives global smoothness of its response
one-form from one smooth, nondegenerate holonomic current.  No field equation,
action-law certificate, endpoint, or Hermitian/Yukawa balance is consumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineCoframeNativeConjugateMatterGlobalRadialRegularity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineRadialCurveIntegralSmoothRegularity
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

private def coframeJetCarrier
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (current.coframe point,
    (holonomicCoframeFirstJetAt current.coframe point).derivative)

private theorem coframe_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞ current.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact smooth.1 internal coordinate

private theorem coframeJetCarrier_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞ (coframeJetCarrier current) := by
  refine (coframe_contDiff current smooth).prodMk ?_
  apply contDiff_pi'
  intro derivativeDirection
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun point =>
    current.coframe point internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    smooth.1 internal coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞ (fun point =>
    fderiv ℝ component point
      (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem affineCoframeFamily_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe joint.1)
          joint.2) := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  unfold affineCoframeFieldOfJet coframeJetAffineComponentLinear
  simp only [sum_apply, smul_apply, smul_eq_mul]
  have coframeSmooth : ContDiff ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        current.coframe joint.1 internal coordinate) :=
    (smooth.1 internal coordinate).comp contDiff_fst
  have derivativeSmooth : ∀ derivativeDirection : LorentzianIndex,
      ContDiff ℝ ∞
        (fun joint : BasePoint × BasePoint =>
          (coframeJetCarrier current joint.1).2 derivativeDirection
            internal coordinate) := by
    intro derivativeDirection
    have carrierSmooth : ContDiff ℝ ∞
        (fun joint : BasePoint × BasePoint =>
          coframeJetCarrier current joint.1) :=
      (coframeJetCarrier_contDiff current smooth).comp contDiff_fst
    exact
      contDiff_pi.mp
        (contDiff_pi.mp
          (contDiff_pi.mp (contDiff_snd.comp carrierSmooth)
            derivativeDirection)
          internal)
        coordinate
  exact
    coframeSmooth.add
      (ContDiff.sum fun derivativeDirection _ =>
        (derivativeSmooth derivativeDirection).mul
          ((coframeBaseCoordinate derivativeDirection).contDiff.comp
            contDiff_snd))

private theorem densitizedPrincipalDrift_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          current candidate direction)
      point := by
  let family := fun candidate : BasePoint => fun localPoint : BasePoint =>
    liveCoframeDensitizedAdjointMomentumCoordinates direction
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe candidate)
          localPoint,
        holonomicConjugateMatterCoordinates current candidate)
  have conjugateCoordinatesSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates current joint.1)
      (point, 0) :=
    (holonomicConjugateMatterCoordinates_contDiff current smooth
      ).contDiffAt.comp (point, 0) contDiffAt_fst
  have inner : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        (affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt current.coframe joint.1)
            joint.2,
          holonomicConjugateMatterCoordinates current joint.1))
      (point, 0) :=
    (affineCoframeFamily_contDiff current smooth).contDiffAt.prodMk
      conjugateCoordinatesSmooth
  have innerValue :
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe point) 0,
        holonomicConjugateMatterCoordinates current point) =
      (current.coframe point,
        holonomicConjugateMatterCoordinates current point) := by
    rw [affineCoframeFieldOfJet_origin]
    rfl
  have outer :=
    liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt direction
      (current.coframe point)
      (holonomicConjugateMatterCoordinates current point)
      nondegenerate
  rw [← innerValue] at outer
  have composed : ContDiffAt ℝ ∞
      (liveCoframeDensitizedAdjointMomentumCoordinates direction ∘
        fun joint : BasePoint × BasePoint =>
          (affineCoframeFieldOfJet
              (holonomicCoframeFirstJetAt current.coframe joint.1)
              joint.2,
            holonomicConjugateMatterCoordinates current joint.1))
      (point, 0) :=
    outer.comp (point, 0) inner
  have familyInfinite :
      ContDiffAt ℝ ∞ (Function.uncurry family) (point, 0) :=
    by
      rw [show Function.uncurry family =
        fun joint : BasePoint × BasePoint =>
          liveCoframeDensitizedAdjointMomentumCoordinates direction
            (affineCoframeFieldOfJet
                (holonomicCoframeFirstJetAt current.coframe joint.1)
                joint.2,
              holonomicConjugateMatterCoordinates current joint.1) by
        funext joint
        rfl]
      exact composed
  have derivativeInfinite : ContDiffAt ℝ ∞
      (fun candidate => fderiv ℝ (family candidate) 0) point := by
    exact ContDiffAt.fderiv (m := ∞) familyInfinite contDiffAt_const (by simp)
  have evaluated := derivativeInfinite.clm_apply
    (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : BasePoint => coordinateDirection direction) point)
  change ContDiffAt ℝ ∞
    (fun candidate =>
      fderiv ℝ
          (fun localPoint =>
            liveCoframeDensitizedAdjointMomentumCoordinates direction
              (affineCoframeFieldOfJet
                  (holonomicCoframeFirstJetAt current.coframe candidate)
                  localPoint,
                holonomicConjugateMatterCoordinates current candidate))
          0 (coordinateDirection direction)) point at evaluated
  simpa [family,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm, fieldDirectionalDerivative] using
      evaluated

private theorem matterDualCoordinates_contDiffAt_of_basis
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (dualField : E → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : E)
    (basisSmooth : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ n
        (fun candidate =>
          dualField candidate
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) point) :
    ContDiffAt ℝ n
      (fun candidate => matterDualCoordinates (dualField candidate)) point := by
  apply contDiffAt_piLp'
  intro index
  exact basisSmooth index

private theorem volumeComplex_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      ((generatedVolumeDensity
        (toContinuumPointField current candidate) : ℝ) : ℂ)) point := by
  have volumeReal : ContDiffAt ℝ ∞
      (fun candidate =>
        generatedVolumeDensity (toContinuumPointField current candidate))
      point := by
    change ContDiffAt ℝ ∞
      (fun candidate => abs (Matrix.det (current.coframe candidate))) point
    exact
      (StageNineCoframeVariation.coframe_volume_contDiffAt
        (current.coframe point) nondegenerate).comp point
          (coframe_contDiff current smooth).contDiffAt
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp point volumeReal

private theorem inverseVolumeComplex_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      (((generatedVolumeDensity
        (toContinuumPointField current candidate) : ℝ) : ℂ)⁻¹)) point := by
  exact (volumeComplex_contDiffAt current smooth point nondegenerate).inv (by
    have realNe :
        generatedVolumeDensity (toContinuumPointField current point) ≠ 0 := by
      change abs (Matrix.det (current.coframe point)) ≠ 0
      exact abs_ne_zero.mpr nondegenerate
    exact_mod_cast realNe)

private theorem coframeInverse_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate => (current.coframe candidate)⁻¹)
      point :=
  (coframe_inv_contDiffAt (current.coframe point) nondegenerate).comp point
    (coframe_contDiff current smooth).contDiffAt

private theorem matterCoordinateDualPairing_contDiffAt
    {coordinates : BasePoint → MatterCoordinateCarrier}
    {vector : BasePoint → DiracExteriorMatterCarrier}
    {point : BasePoint}
    (coordinatesRegular : ContDiffAt ℝ ∞ coordinates point)
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterDualOfCoordinates (coordinates candidate) (vector candidate))
      point := by
  rw [show
    (fun candidate =>
      matterDualOfCoordinates (coordinates candidate) (vector candidate)) =
    fun candidate => ∑ index : MatterCoordinateIndex,
      matterCoordinateEquiv (vector candidate) index *
        coordinates candidate index by
    funext candidate
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiffAt.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  exact
    ((projection.restrictScalars ℝ).contDiff.contDiffAt.comp
      point vectorRegular).mul
    ((projection.restrictScalars ℝ).contDiff.contDiffAt.comp
      point coordinatesRegular)

private theorem conjugateApply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞
      (fun candidate => current.conjugateMatter candidate (vector candidate))
      point := by
  rw [show
    (fun candidate => current.conjugateMatter candidate (vector candidate)) =
    fun candidate =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates current candidate)
        (vector candidate) by
    funext candidate
    exact congrArg
      (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
        dual (vector candidate))
      (matterDualOfCoordinates_surjective
        (current.conjugateMatter candidate)).symm]
  exact matterCoordinateDualPairing_contDiffAt
    (holonomicConjugateMatterCoordinates_contDiff current smooth).contDiffAt
    vectorRegular

private theorem livePrincipal_coordinate_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        ((liveCoframeMatterPrincipal
          (current.coframe candidate) direction) (vector candidate))) point := by
  have gammaRegular : ContDiffAt ℝ ∞ (fun candidate =>
      inverseCoframeDiracGamma
        { coframe := current.coframe candidate, derivative := 0 } direction)
      point :=
    (inverseCoframeDiracGamma_contDiffAt
      (current.coframe point) nondegenerate direction).comp point
        (coframe_contDiff current smooth).contDiffAt
  have actual :=
    (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
      |>.contDiffAt.comp point gammaRegular).clm_apply vectorRegular
  have gammaActionRegular : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := current.coframe candidate, derivative := 0 }
            direction)
          (vector candidate))) point := by
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := current.coframe candidate, derivative := 0 }
            direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold liveCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
        gammaActionRegular

private theorem spinLift_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun candidate =>
      diracSpinConnectionLift
        (current.gravityConnection candidate) direction) point := by
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro pair _
  have realRegular : ContDiffAt ℝ ∞ (fun candidate =>
      minkowskiInternalSign (lorentzBivectorFirst pair) *
        current.gravityConnection candidate direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair)) point :=
    contDiffAt_const.mul
      (smooth.2.1 direction (lorentzBivectorFirst pair)
        (lorentzBivectorSecond pair)).contDiffAt
  have complexRegular : ContDiffAt ℝ ∞ (fun candidate =>
      ((minkowskiInternalSign (lorentzBivectorFirst pair) *
        current.gravityConnection candidate direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair) : ℝ) : ℂ))
      point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point realRegular
  exact (contDiffAt_const.mul complexRegular).mul contDiffAt_const

private theorem connectionOperator_coordinate_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        ((holonomicIdentityCoframeMatterConnectionOperator
          current candidate direction) (vector candidate))) point := by
  have spinActionRegular : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (current.gravityConnection candidate) direction)
          (vector candidate))) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (spinLift_contDiffAt current smooth point direction)).clm_apply
            vectorRegular
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (current.gravityConnection candidate) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeRegular : ContDiffAt ℝ ∞ (fun candidate =>
      p286CoordinateEquiv (current.gaugeConnection candidate direction))
      point :=
    (smooth.2.2.2.2.1 direction).contDiffAt
  have gaugeActionRegular : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection candidate direction))
          (vector candidate))) point := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gaugeRegular).clm_apply vectorRegular
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (current.gaugeConnection candidate direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector candidate))))) point at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterConnectionOperator
  simp only [LinearMap.add_apply, map_add]
  exact spinActionRegular.add gaugeActionRegular

private theorem algebraicOperator_coordinate_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          current candidate) (vector candidate))) point := by
  have directionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞ (fun candidate =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
              (current.coframe candidate) direction)
            ((holonomicIdentityCoframeMatterConnectionOperator
              current candidate direction) (vector candidate)))) point := by
    intro direction
    exact livePrincipal_coordinate_contDiffAt current smooth point
      nondegenerate direction
      (connectionOperator_coordinate_contDiffAt current smooth point
        direction vectorRegular)
  have sumRegular : ContDiffAt ℝ ∞ (fun candidate =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
              (current.coframe candidate) direction)
            ((holonomicIdentityCoframeMatterConnectionOperator
              current candidate direction) (vector candidate)))) point :=
    ContDiffAt.sum fun direction _ => directionRegular direction
  have scalarRegular : ContDiffAt ℝ ∞ current.scalar point :=
    smooth.2.2.2.2.2.2.1.contDiffAt
  have yukawaRegular : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (current.scalar candidate))
          (vector candidate))) point := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point scalarRegular).clm_apply vectorRegular
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (current.scalar candidate))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sum]
  exact sumRegular.add yukawaRegular

private theorem algebraicDual_apply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      holonomicDiracDualLiveCoframeAlgebraicDual current candidate
        (vector candidate)) point := by
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  exact
    (volumeComplex_contDiffAt current smooth point nondegenerate).smul
      (conjugateApply_contDiffAt current smooth point
        (algebraicOperator_coordinate_contDiffAt current smooth point
          nondegenerate vectorRegular))

private theorem conjugateDerivativeCoordinates_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun candidate =>
      holonomicConjugateMatterDerivativeCoordinates current candidate
        direction) point :=
  (holonomicConjugateMatterDerivativeCoordinates_contDiff
    current smooth direction).contDiffAt

private theorem frameConjugateDerivative_apply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (internal : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ ∞ (fun candidate =>
      (holonomicFrameConjugateMatterDerivative current candidate internal)
        (vector candidate)) point := by
  unfold holonomicFrameConjugateMatterDerivative
    frameConjugateMatterDerivative
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply ContDiffAt.sum
  intro coordinate _
  have inverseEntryRegular : ContDiffAt ℝ ∞ (fun candidate =>
      (current.coframe candidate)⁻¹ coordinate internal) point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp
        (coframeInverse_contDiffAt current smooth point nondegenerate)
        coordinate) internal
  have inverseComplexRegular : ContDiffAt ℝ ∞ (fun candidate =>
      ((current.coframe candidate)⁻¹ coordinate internal : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point inverseEntryRegular
  unfold holonomicConjugateMatterDerivativeDual
  exact inverseComplexRegular.smul
    (matterCoordinateDualPairing_contDiffAt
      (conjugateDerivativeCoordinates_contDiffAt
        current smooth point coordinate)
      vectorRegular)

private theorem spatialFrameTransport_apply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ ∞ (fun candidate =>
      ∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative current candidate
          spatial.succ).comp
          (identityCoframeMatterPrincipal spatial.succ) vector) point := by
  apply ContDiffAt.sum
  intro spatial _
  simp only [LinearMap.comp_apply]
  exact frameConjugateDerivative_apply_contDiffAt current smooth point
    nondegenerate spatial.succ
    (vector := fun _ => identityCoframeMatterPrincipal spatial.succ vector)
    contDiffAt_const

private theorem spatialPrincipalDrift_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates current) point := by
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  exact ContDiffAt.sum fun direction _ =>
    densitizedPrincipalDrift_contDiffAt current smooth point nondegenerate
      direction.succ

private theorem temporalPrincipalDrift_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates current) point :=
  densitizedPrincipalDrift_contDiffAt current smooth point nondegenerate
    canonicalLorentzianTimeDirection

private theorem totalPrincipalDrift_apply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ ∞ (fun candidate =>
      holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
        current candidate vector) point := by
  unfold holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
  simp only [LinearMap.add_apply]
  exact
    (matterCoordinateDualPairing_contDiffAt
      (spatialPrincipalDrift_contDiffAt current smooth point nondegenerate)
      (vector := fun _ => vector) contDiffAt_const).add
    (matterCoordinateDualPairing_contDiffAt
      (temporalPrincipalDrift_contDiffAt current smooth point nondegenerate)
      (vector := fun _ => vector) contDiffAt_const)

private theorem frameKnownDensitizedDual_apply_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ ∞ (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        current candidate vector) point := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  exact
    (algebraicDual_apply_contDiffAt current smooth point nondegenerate
      (vector := fun _ => vector) contDiffAt_const).sub
      ((volumeComplex_contDiffAt current smooth point nondegenerate).smul
        (spatialFrameTransport_apply_contDiffAt current smooth point
          nondegenerate vector)) |>.sub
      (totalPrincipalDrift_apply_contDiffAt current smooth point
        nondegenerate vector)

private theorem frameActionVelocity_basis_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ ∞ (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
        current candidate
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) point := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  exact
    (inverseVolumeComplex_contDiffAt current smooth point nondegenerate).mul
      (frameKnownDensitizedDual_apply_contDiffAt current smooth point
        nondegenerate
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))))

private theorem conjugateResponseCoordinates_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterDualCoordinates
        (globalFrameTimeConjugateMatterResponseAt current candidate)) point := by
  apply matterDualCoordinates_contDiffAt_of_basis
  intro index
  unfold globalFrameTimeConjugateMatterResponseAt
    globalFrameTimeConjugateMatterGeneratedDerivativeAt
  simp only [LinearMap.sub_apply]
  exact
    (frameActionVelocity_basis_contDiffAt current smooth point
      nondegenerate index).sub
      (frameConjugateDerivative_apply_contDiffAt current smooth point
        nondegenerate 0
        (vector := fun _ => matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) contDiffAt_const)

private theorem coframeRowLinearFunctional_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    ContDiffAt ℝ ∞
      (fun candidate => coframeRowLinearFunctional (current.coframe candidate))
      point := by
  unfold coframeRowLinearFunctional
  apply ContDiffAt.sum
  intro coordinate _
  exact (smooth.1 0 coordinate).contDiffAt.smul contDiffAt_const

private theorem conjugateResponseOneForm_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (coframeNativeGlobalConjugateMatterResponseOneForm current) point := by
  unfold coframeNativeGlobalConjugateMatterResponseOneForm
  apply ContDiffAt.smulRight
  · exact coframeRowLinearFunctional_contDiffAt current smooth point
  · exact conjugateResponseCoordinates_contDiffAt current smooth point
      nondegenerate

/-- Generic public mouth tested by this probe: a smooth nondegenerate current
generates a globally smooth frame-adjoint response one-form. -/
theorem coframeNativeGlobalConjugateMatterResponseOneForm_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    ContDiff ℝ ∞
      (coframeNativeGlobalConjugateMatterResponseOneForm current) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact conjugateResponseOneForm_contDiffAt current smooth point
    (nondegenerate point)

theorem actionGeneratedGlobalFrameTimeMatterActual_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedGlobalFrameTimeMatterActual current).Smooth := by
  have responseSmooth :=
    StageNineCoframeNativeMatterGlobalRadialRegularity.coframeNativeGlobalMatterResponseOneForm_contDiff
      current smooth nondegenerate
  have radialSmooth :
      ContDiff ℝ ∞ (coframeNativeGlobalMatterRadialIncrement current) :=
    radialCurveIntegral_contDiff_infty_of_contDiff
      (coframeNativeGlobalMatterResponseOneForm current) responseSmooth
  rcases smooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, ?_,
      conjugateMatterSmooth⟩
  rw [show
    (fun point => matterCoordinateEquiv
      ((actionGeneratedGlobalFrameTimeMatterActual current).matter point)) =
      fun point => matterCoordinateEquiv (current.matter point) +
        coframeNativeGlobalMatterRadialIncrement current point by
    funext point
    exact actionGeneratedGlobalFrameTimeMatterActual_matterCoordinates
      current point]
  exact matterSmooth.add radialSmooth

theorem actionGeneratedGlobalFrameMatterDualActual_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedGlobalFrameMatterDualActual current).Smooth := by
  let primal := actionGeneratedGlobalFrameTimeMatterActual current
  have primalSmooth : primal.Smooth :=
    actionGeneratedGlobalFrameTimeMatterActual_smooth current smooth
      nondegenerate
  have primalNondegenerate : primal.Nondegenerate :=
    actionGeneratedGlobalFrameTimeMatterActual_nondegenerate current
      nondegenerate
  have responseSmooth : ContDiff ℝ ∞
      (coframeNativeGlobalConjugateMatterResponseOneForm primal) :=
    coframeNativeGlobalConjugateMatterResponseOneForm_contDiff primal
      primalSmooth primalNondegenerate
  have radialSmooth : ContDiff ℝ ∞
      (coframeNativeGlobalConjugateMatterRadialIncrement primal) :=
    radialCurveIntegral_contDiff_infty_of_contDiff
      (coframeNativeGlobalConjugateMatterResponseOneForm primal)
      responseSmooth
  have primalConjugateCoordinatesSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates primal) :=
    holonomicConjugateMatterCoordinates_contDiff primal primalSmooth
  rcases primalSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  let output := actionGeneratedGlobalFrameTimeConjugateMatterActual primal
  have outputConjugateCoordinatesSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates output) := by
    rw [show holonomicConjugateMatterCoordinates output =
      fun point => holonomicConjugateMatterCoordinates primal point +
        coframeNativeGlobalConjugateMatterRadialIncrement primal point by
      funext point
      exact actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinates
        primal point]
    exact primalConjugateCoordinatesSmooth.add radialSmooth
  change output.Smooth
  refine
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      ?_⟩
  intro index
  have coordinateSmooth :=
    (contDiff_piLp 2).mp outputConjugateCoordinatesSmooth index
  change ContDiff ℝ ∞ (fun point =>
    output.conjugateMatter point
      (matterCoordinateEquiv.symm
        (EuclideanSpace.single index (1 : ℂ))))
  simpa [holonomicConjugateMatterCoordinates, matterDualCoordinates] using
    coordinateSmooth

theorem installFormNativeGravityReaction_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (installFormNativeGravityReaction current).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, ?_,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  intro internalPair spacetimePair
  change ContDiff ℝ ∞ (fun point =>
    formNativeGravityReactionField current point internalPair spacetimePair)
  exact formNativeGravityReactionField_component_contDiff current
    connectionSmooth auxiliarySmooth internalPair spacetimePair

#print axioms coframeNativeGlobalConjugateMatterResponseOneForm_contDiff
#print axioms actionGeneratedGlobalFrameMatterDualActual_smooth
#print axioms installFormNativeGravityReaction_smooth

end
end StageNineCoframeNativeConjugateMatterGlobalRadialRegularity
end PhysicsCore
end SaturationMonoid
