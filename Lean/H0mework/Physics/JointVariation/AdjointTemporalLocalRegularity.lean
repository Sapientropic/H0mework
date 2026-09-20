import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity

/-!
# Local regularity of the complete-joint adjoint temporal profile

The complete-joint adjoint writer recomputes its live-coframe velocity after
the same Cartan restart as the primal writer.  This module proves continuity
of that already-generated correction at an arbitrary smooth,
nondegenerate, noncharacteristic occurrence.  The proof stays on the real
finite-coordinate carrier and differentiates the action-owned affine
coframe momentum once.

No residual coordinate, target derivative, branch, zero-fiber receipt, or
free coefficient enters the theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActualVariationRegularity
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance localP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance localP286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance localP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private theorem coframe_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞ current.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact smooth.1 internal coordinate

private def coframeJetCarrier
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (current.coframe point,
    (holonomicCoframeFirstJetAt current.coframe point).derivative)

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
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem coframeJetCarrier_contDiffAt_one_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point) :
    ContDiffAt ℝ 1 (coframeJetCarrier current) point := by
  refine (coframeRegular.of_le (by norm_num)).prodMk ?_
  apply contDiffAt_pi'
  intro derivativeDirection
  apply contDiffAt_pi'
  intro internal
  apply contDiffAt_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun candidate =>
    current.coframe candidate internal coordinate
  have componentRegular : ContDiffAt ℝ 2 component point :=
    contDiffAt_pi.mp (contDiffAt_pi.mp coframeRegular internal) coordinate
  have derivativeRegular : ContDiffAt ℝ 1
      (fun candidate => fderiv ℝ component candidate) point :=
    componentRegular.fderiv_right (m := 1) (by norm_num)
  change ContDiffAt ℝ 1
    (fun candidate =>
      fderiv ℝ component candidate
        (coordinateDirection derivativeDirection)) point
  exact derivativeRegular.clm_apply contDiffAt_const

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
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ n (fun candidate =>
      matterDualCoordinates (dualField candidate)) point := by
  apply contDiffAt_piLp'
  intro index
  exact basisSmooth index

private theorem liveCoframeAlgebraicDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeAlgebraicDual configuration point vector =
      ((generatedVolumeDensity
        (toContinuumPointField configuration point) : ℝ) : ℂ) *
        configuration.conjugateMatter point
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            configuration point) vector) :=
  rfl

private theorem liveCoframeKnownDensitizedDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        configuration point vector =
      holonomicDiracDualLiveCoframeAlgebraicDual configuration point vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              configuration point)
            vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              configuration point)
            vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              configuration point)
            vector :=
  rfl

private theorem liveCoframeActionVelocity_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration point vector =
      (((generatedVolumeDensity
        (toContinuumPointField configuration point) : ℝ) : ℂ)⁻¹) *
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          configuration point
          (currentCoframeMatterTemporalPrincipalInverse
            (configuration.coframe point) vector) :=
  rfl

theorem liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt
    (direction : LorentzianIndex)
    (coframe : LorentzianCoframe)
    (coordinates : MatterCoordinateCarrier)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (liveCoframeDensitizedAdjointMomentumCoordinates direction)
      (coframe, coordinates) := by
  apply contDiffAt_piLp'
  intro index
  unfold liveCoframeDensitizedAdjointMomentumCoordinates
    matterDualCoordinates
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  have volumeReal : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        abs (Matrix.det joint.1))
      (coframe, coordinates) :=
    (StageNineCoframeVariation.coframe_volume_contDiffAt
      coframe nondegenerate).comp
        (coframe, coordinates) contDiffAt_fst
  have volumeComplex : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        ((abs (Matrix.det joint.1) : ℝ) : ℂ))
      (coframe, coordinates) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp
      (coframe, coordinates) volumeReal
  have pairingSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 direction)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      (coframe, coordinates) := by
    rw [show
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 direction)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))) =
      fun joint =>
        ∑ coordinate : MatterCoordinateIndex,
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 direction)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ))))
              coordinate *
            joint.2 coordinate by
      funext joint
      exact matterDualOfCoordinates_apply _ _]
    apply ContDiffAt.sum
    intro coordinate _
    have gammaSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          inverseCoframeDiracGamma
            { coframe := joint.1, derivative := 0 } direction)
        (coframe, coordinates) := by
      let gamma := fun candidate : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := candidate, derivative := 0 } direction
      have outer : ContDiffAt ℝ ∞ gamma coframe :=
        inverseCoframeDiracGamma_contDiffAt
          coframe nondegenerate direction
      have inner : ContDiffAt ℝ ∞
          (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
            joint.1)
          (coframe, coordinates) :=
        contDiffAt_fst
      have composed : ContDiffAt ℝ ∞
          (gamma ∘
            (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
              joint.1))
          (coframe, coordinates) :=
        outer.comp (coframe, coordinates) inner
      change ContDiffAt ℝ ∞
        (gamma ∘
          (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
            joint.1))
        (coframe, coordinates)
      exact composed
    have basisCoordinatesSmooth : ContDiffAt ℝ ∞
        (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        (coframe, coordinates) :=
      contDiffAt_const
    have gammaActionSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.1, derivative := 0 } direction)
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))))
        (coframe, coordinates) := by
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.contDiffAt.comp (coframe, coordinates) gammaSmooth).clm_apply
            basisCoordinatesSmooth
      change ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.1, derivative := 0 } direction)
              (matterCoordinateEquiv.symm
                (matterCoordinateEquiv
                  (matterCoordinateEquiv.symm
                    (EuclideanSpace.single index (1 : ℂ)))))))
        (coframe, coordinates) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    have principalCarrierSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal joint.1 direction)
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))))
        (coframe, coordinates) := by
      unfold liveCoframeMatterPrincipal
      simp only [LinearMap.smul_apply, map_smul]
      exact
        (contDiffAt_const :
          ContDiffAt ℝ ∞
            (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
              (Complex.I : ℂ))
            (coframe, coordinates)).smul gammaActionSmooth
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj coordinate).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    have principalCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 direction)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ))))
              coordinate)
        (coframe, coordinates) :=
      (projection.restrictScalars ℝ).contDiff.contDiffAt.comp
        (coframe, coordinates) principalCarrierSmooth
    have dualCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          joint.2 coordinate)
        (coframe, coordinates) := by
      fun_prop
    exact principalCoordinateSmooth.mul dualCoordinateSmooth
  exact volumeComplex.mul pairingSmooth

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

private theorem affineCoframeFamily_contDiffAt_one_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point) :
    ContDiffAt ℝ 1
      (fun joint : BasePoint × BasePoint =>
        affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe joint.1)
          joint.2)
      (point, 0) := by
  apply contDiffAt_pi'
  intro internal
  apply contDiffAt_pi'
  intro coordinate
  unfold affineCoframeFieldOfJet coframeJetAffineComponentLinear
  simp only [sum_apply, smul_apply, smul_eq_mul]
  have coframeRegularAtJoint : ContDiffAt ℝ 1
      (fun joint : BasePoint × BasePoint =>
        current.coframe joint.1 internal coordinate)
      (point, 0) :=
    (contDiffAt_pi.mp
      (contDiffAt_pi.mp (coframeRegular.of_le (by norm_num)) internal)
      coordinate).comp (point, 0) contDiffAt_fst
  have derivativeRegular : ∀ derivativeDirection : LorentzianIndex,
      ContDiffAt ℝ 1
        (fun joint : BasePoint × BasePoint =>
          (coframeJetCarrier current joint.1).2 derivativeDirection
            internal coordinate)
        (point, 0) := by
    intro derivativeDirection
    have carrierRegular : ContDiffAt ℝ 1
        (fun joint : BasePoint × BasePoint =>
          coframeJetCarrier current joint.1)
        (point, 0) :=
      (coframeJetCarrier_contDiffAt_one_of_local
        current point coframeRegular).comp (point, 0) contDiffAt_fst
    exact
      contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (contDiffAt_pi.mp (contDiffAt_snd.comp (point, 0) carrierRegular)
            derivativeDirection)
          internal)
        coordinate
  exact
    coframeRegularAtJoint.add
      (ContDiffAt.sum fun derivativeDirection _ =>
        (derivativeRegular derivativeDirection).mul
          ((coframeBaseCoordinate derivativeDirection).contDiff.contDiffAt.comp
            (point, 0) contDiffAt_snd))

private theorem restart_liveCoframeDensitizedMomentumFamily_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (Function.uncurry
        (fun candidate : BasePoint => fun localPoint : BasePoint =>
          liveCoframeDensitizedAdjointMomentumCoordinates direction
            (affineCoframeFieldOfJet
                (holonomicCoframeFirstJetAt current.coframe candidate)
                localPoint,
              holonomicConjugateMatterCoordinates restarted candidate)))
      (point, 0) := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have conjugateCoordinatesSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates restarted joint.1)
      (point, 0) := by
    have base : ContDiff ℝ ∞
        (holonomicConjugateMatterCoordinates current) :=
      holonomicConjugateMatterCoordinates_contDiff current smooth
    rw [show
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates restarted joint.1) =
      fun joint =>
        holonomicConjugateMatterCoordinates current joint.1 by
      funext joint
      unfold holonomicConjugateMatterCoordinates restarted
      rw [
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
    exact base.contDiffAt.comp (point, 0) contDiffAt_fst
  have inner : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        (affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt current.coframe joint.1)
            joint.2,
          holonomicConjugateMatterCoordinates restarted joint.1))
      (point, 0) :=
    (affineCoframeFamily_contDiff current smooth).contDiffAt.prodMk
      conjugateCoordinatesSmooth
  have innerValue :
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe point) 0,
        holonomicConjugateMatterCoordinates restarted point) =
      (current.coframe point,
        holonomicConjugateMatterCoordinates restarted point) := by
    rw [affineCoframeFieldOfJet_origin]
    rfl
  have outer :=
    liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt direction
      (current.coframe point)
      (holonomicConjugateMatterCoordinates restarted point)
      nondegenerate
  rw [← innerValue] at outer
  exact outer.comp (point, 0) inner

private theorem restart_liveCoframeDensitizedPrincipalDrift_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          restarted candidate direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  let family := fun candidate : BasePoint => fun localPoint : BasePoint =>
    liveCoframeDensitizedAdjointMomentumCoordinates direction
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe candidate)
          localPoint,
        holonomicConjugateMatterCoordinates restarted candidate)
  have familyInfinite :
      ContDiffAt ℝ ∞ (Function.uncurry family) (point, 0) :=
    restart_liveCoframeDensitizedMomentumFamily_contDiffAt
      source current smooth point nondegenerate direction
  have sectionInfinite :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (0 : BasePoint)) point :=
    contDiffAt_const
  have derivativeInfinite : ContDiffAt ℝ ∞
      (fun candidate => fderiv ℝ (family candidate) 0)
      point := by
    exact ContDiffAt.fderiv (m := ∞) familyInfinite sectionInfinite (by simp)
  have evaluated :=
    derivativeInfinite.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : BasePoint => coordinateDirection direction) point)
  change ContDiffAt ℝ ∞
    (fun candidate =>
      fderiv ℝ
          (fun localPoint =>
            liveCoframeDensitizedAdjointMomentumCoordinates direction
              (affineCoframeFieldOfJet
                  (holonomicCoframeFirstJetAt current.coframe candidate)
                  localPoint,
                holonomicConjugateMatterCoordinates restarted candidate))
          0 (coordinateDirection direction))
      point at evaluated
  simpa [restarted, family,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm, fieldDirectionalDerivative] using
      evaluated

private theorem
    restart_liveCoframeDensitizedMomentumFamily_contDiffAt_one_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 1
      (Function.uncurry
        (fun candidate : BasePoint => fun localPoint : BasePoint =>
          liveCoframeDensitizedAdjointMomentumCoordinates direction
            (affineCoframeFieldOfJet
                (holonomicCoframeFirstJetAt current.coframe candidate)
                localPoint,
              holonomicConjugateMatterCoordinates restarted candidate)))
      (point, 0) := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have conjugateCoordinatesRegular : ContDiffAt ℝ 1
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates restarted joint.1)
      (point, 0) := by
    have projectionRegular : ContDiffAt ℝ 1
        (fun joint : BasePoint × BasePoint => joint.1) (point, 0) :=
      contDiffAt_fst
    have base : ContDiffAt ℝ 1
        (holonomicConjugateMatterCoordinates current ∘
          fun joint : BasePoint × BasePoint => joint.1)
        (point, 0) :=
      conjugateRegular.comp (point, 0) projectionRegular
    simpa only [restarted, holonomicConjugateMatterCoordinates,
      Function.comp_def,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
      using base
  have inner : ContDiffAt ℝ 1
      (fun joint : BasePoint × BasePoint =>
        (affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt current.coframe joint.1)
            joint.2,
          holonomicConjugateMatterCoordinates restarted joint.1))
      (point, 0) :=
    (affineCoframeFamily_contDiffAt_one_of_local
      current point coframeRegular).prodMk conjugateCoordinatesRegular
  have innerValue :
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe point) 0,
        holonomicConjugateMatterCoordinates restarted point) =
      (current.coframe point,
        holonomicConjugateMatterCoordinates restarted point) := by
    rw [affineCoframeFieldOfJet_origin]
    rfl
  have outer : ContDiffAt ℝ 1
      (liveCoframeDensitizedAdjointMomentumCoordinates direction)
      (current.coframe point,
        holonomicConjugateMatterCoordinates restarted point) :=
    (liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt direction
      (current.coframe point)
      (holonomicConjugateMatterCoordinates restarted point)
      nondegenerate).of_le (by norm_num)
  rw [← innerValue] at outer
  exact outer.comp (point, 0) inner

/-- A source-native Cartan restart has continuous directional principal
drift at a point with a local C² coframe and C¹ conjugate coordinate field. -/
theorem
    restart_liveCoframeDensitizedPrincipalDrift_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          restarted candidate direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  let family := fun candidate : BasePoint => fun localPoint : BasePoint =>
    liveCoframeDensitizedAdjointMomentumCoordinates direction
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt current.coframe candidate)
          localPoint,
        holonomicConjugateMatterCoordinates restarted candidate)
  have familyRegular :
      ContDiffAt ℝ 1 (Function.uncurry family) (point, 0) :=
    restart_liveCoframeDensitizedMomentumFamily_contDiffAt_one_of_local
      source current point nondegenerate coframeRegular conjugateRegular
        direction
  have sectionRegular :
      ContDiffAt ℝ 0 (fun _ : BasePoint => (0 : BasePoint)) point :=
    contDiffAt_const
  have derivativeRegular : ContDiffAt ℝ 0
      (fun candidate => fderiv ℝ (family candidate) 0)
      point := by
    exact ContDiffAt.fderiv (m := 0) familyRegular sectionRegular (by norm_num)
  have evaluated :=
    derivativeRegular.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ 0
          (fun _ : BasePoint => coordinateDirection direction) point)
  change ContDiffAt ℝ 0
    (fun candidate =>
      fderiv ℝ
          (fun localPoint =>
            liveCoframeDensitizedAdjointMomentumCoordinates direction
              (affineCoframeFieldOfJet
                  (holonomicCoframeFirstJetAt current.coframe candidate)
                  localPoint,
                holonomicConjugateMatterCoordinates restarted candidate))
          0 (coordinateDirection direction))
      point at evaluated
  simpa [restarted, family,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm, fieldDirectionalDerivative] using
      evaluated

private theorem restart_coframe_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
      ).coframe = current.coframe :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
    source current

private theorem restart_volume_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        ((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have volumeReal : ContDiffAt ℝ ∞
      (fun candidate =>
        generatedVolumeDensity
          (toContinuumPointField restarted candidate))
      point := by
    change ContDiffAt ℝ ∞
      (fun candidate => abs (Matrix.det (restarted.coframe candidate))) point
    have outer : ContDiffAt ℝ ∞
        (fun coframe : LorentzianCoframe => abs (Matrix.det coframe))
        (restarted.coframe point) := by
      rw [congrFun (restart_coframe_eq_current source current) point]
      exact
        StageNineCoframeVariation.coframe_volume_contDiffAt
          (current.coframe point) nondegenerate
    have inner : ContDiffAt ℝ ∞ restarted.coframe point := by
      rw [restart_coframe_eq_current source current]
      exact (coframe_contDiff current smooth).contDiffAt
    exact outer.comp point inner
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp point volumeReal

private theorem restart_inverseVolume_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        (((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ)⁻¹))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  exact
    (restart_volume_contDiffAt source current smooth point nondegenerate).inv
      (by
        have determinantNe : Matrix.det (restarted.coframe point) ≠ 0 := by
          rw [congrFun (restart_coframe_eq_current source current) point]
          exact nondegenerate
        have volumeNeReal :
            generatedVolumeDensity
                (toContinuumPointField restarted point) ≠ 0 := by
          unfold generatedVolumeDensity toContinuumPointField
          exact abs_ne_zero.mpr determinantNe
        exact_mod_cast volumeNeReal)

private theorem restart_volume_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        ((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have volumeReal : ContDiffAt ℝ 0
      (fun candidate =>
        generatedVolumeDensity
          (toContinuumPointField restarted candidate))
      point := by
    change ContDiffAt ℝ 0
      (fun candidate => abs (Matrix.det (restarted.coframe candidate))) point
    have outer : ContDiffAt ℝ 0
        (fun coframe : LorentzianCoframe => abs (Matrix.det coframe))
        (restarted.coframe point) := by
      rw [congrFun (restart_coframe_eq_current source current) point]
      exact
        (StageNineCoframeVariation.coframe_volume_contDiffAt
          (current.coframe point) nondegenerate).of_le (by norm_num)
    have inner : ContDiffAt ℝ 0 restarted.coframe point := by
      rw [restart_coframe_eq_current source current]
      exact coframeRegular
    exact outer.comp point inner
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp point volumeReal

private theorem restart_inverseVolume_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        (((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ)⁻¹))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  exact
    (restart_volume_contDiffAt_of_local source current point nondegenerate
      coframeRegular).inv
      (by
        have determinantNe : Matrix.det (restarted.coframe point) ≠ 0 := by
          rw [congrFun (restart_coframe_eq_current source current) point]
          exact nondegenerate
        have volumeNeReal :
            generatedVolumeDensity
                (toContinuumPointField restarted point) ≠ 0 := by
          unfold generatedVolumeDensity toContinuumPointField
          exact abs_ne_zero.mpr determinantNe
        exact_mod_cast volumeNeReal)

private theorem restart_conjugateCoordinates_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates restarted) point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show holonomicConjugateMatterCoordinates restarted =
      holonomicConjugateMatterCoordinates current by
    funext candidate
    unfold holonomicConjugateMatterCoordinates restarted
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  exact
    (holonomicConjugateMatterCoordinates_contDiff current smooth).contDiffAt

private theorem restart_conjugateDerivativeCoordinates_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicConjugateMatterDerivativeCoordinates
          restarted candidate direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate =>
      holonomicConjugateMatterDerivativeCoordinates
        restarted candidate direction) =
    fun candidate =>
      holonomicConjugateMatterDerivativeCoordinates
        current candidate direction by
    funext candidate
    unfold holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates restarted
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  exact
    (holonomicConjugateMatterDerivativeCoordinates_contDiff
      current smooth direction).contDiffAt

private theorem restart_conjugateCoordinates_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates restarted) point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show holonomicConjugateMatterCoordinates restarted =
      holonomicConjugateMatterCoordinates current by
    funext candidate
    unfold holonomicConjugateMatterCoordinates restarted
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  exact conjugateRegular

private theorem restart_conjugateDerivativeCoordinates_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicConjugateMatterDerivativeCoordinates
          restarted candidate direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate =>
      holonomicConjugateMatterDerivativeCoordinates
        restarted candidate direction) =
    fun candidate =>
      holonomicConjugateMatterDerivativeCoordinates
        current candidate direction by
    funext candidate
    unfold holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates restarted
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  exact
    (conjugateRegular.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const

private theorem matterCoordinateDualPairing_contDiffAt
    {n : WithTop ℕ∞}
    {coordinates : BasePoint → MatterCoordinateCarrier}
    {vector : BasePoint → DiracExteriorMatterCarrier}
    {point : BasePoint}
    (coordinatesRegular : ContDiffAt ℝ n coordinates point)
    (vectorRegular : ContDiffAt ℝ n
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    ContDiffAt ℝ n
      (fun candidate => matterDualOfCoordinates (coordinates candidate)
        (vector candidate))
      point := by
  rw [show
    (fun candidate =>
      matterDualOfCoordinates (coordinates candidate) (vector candidate)) =
    fun candidate =>
      ∑ index : MatterCoordinateIndex,
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

private theorem restart_conjugateApply_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate => restarted.conjugateMatter candidate
        (vector candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate => restarted.conjugateMatter candidate
      (vector candidate)) =
    fun candidate =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates restarted candidate)
        (vector candidate) by
    funext candidate
    exact congrArg
      (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
        dual (vector candidate))
      (matterDualOfCoordinates_surjective
        (restarted.conjugateMatter candidate)).symm]
  exact matterCoordinateDualPairing_contDiffAt
    ((restart_conjugateCoordinates_contDiffAt
      source current smooth point).of_le (by decide))
    vectorRegular

private theorem restart_conjugateApply_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate => restarted.conjugateMatter candidate
        (vector candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate => restarted.conjugateMatter candidate
      (vector candidate)) =
    fun candidate =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates restarted candidate)
        (vector candidate) by
    funext candidate
    exact congrArg
      (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
        dual (vector candidate))
      (matterDualOfCoordinates_surjective
        (restarted.conjugateMatter candidate)).symm]
  exact matterCoordinateDualPairing_contDiffAt
    (restart_conjugateCoordinates_contDiffAt_of_local
      source current point conjugateRegular)
    vectorRegular

private theorem restart_livePrincipal_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
            (restarted.coframe candidate) direction)
            (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeRegular : ContDiffAt ℝ ∞ restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact (coframe_contDiff current smooth).contDiffAt
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have gammaRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          direction)
      point := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate direction
    rw [← coframeAt] at outer
    exact outer.comp point coframeRegular
  have gammaActionRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction)
            (vector candidate)))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point (gammaRegular.of_le (by decide))).clm_apply
          vectorRegular
    change ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold liveCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
        gammaActionRegular

private theorem restart_livePrincipal_coordinate_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
            (restarted.coframe candidate) direction)
            (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have restartedCoframeRegular : ContDiffAt ℝ 0 restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact coframeRegular
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have gammaRegular : ContDiffAt ℝ 0
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          direction)
      point := by
    have outer : ContDiffAt ℝ 0
        (fun candidate : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := candidate, derivative := 0 } direction)
        (current.coframe point) :=
      (inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate direction).of_le (by norm_num)
    rw [← coframeAt] at outer
    exact outer.comp point restartedCoframeRegular
  have gammaActionRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction)
            (vector candidate)))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaRegular).clm_apply vectorRegular
    change ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold liveCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    (contDiffAt_const :
      ContDiffAt ℝ 0 (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
        gammaActionRegular

private theorem restart_temporalPrincipalScalar_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        coframeTemporalPrincipalScalar (restarted.coframe candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeRegular : ContDiffAt ℝ ∞ restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact (coframe_contDiff current smooth).contDiffAt
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have inverseRegular : ContDiffAt ℝ ∞
      (fun candidate => (restarted.coframe candidate)⁻¹)
      point := by
    have outer :=
      StageNineCoframeVariation.coframe_inv_contDiffAt
        (current.coframe point) nondegenerate
    rw [← coframeAt] at outer
    exact outer.comp point coframeRegular
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntryRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (restarted.coframe candidate)⁻¹
          (0 : LorentzianIndex) internal)
      point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntryRegular.pow 2)

private theorem restart_temporalPrincipalInverse_basis_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (index : MatterCoordinateIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeRegular : ContDiffAt ℝ ∞ restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact (coframe_contDiff current smooth).contDiffAt
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have qComplexRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        ((coframeTemporalPrincipalScalar
          (restarted.coframe candidate) : ℝ) : ℂ))
      point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (restart_temporalPrincipalScalar_contDiffAt
        source current smooth point nondegenerate)
  have qComplexNe :
      ((coframeTemporalPrincipalScalar
        (restarted.coframe point) : ℝ) : ℂ) ≠ 0 := by
    rw [coframeAt]
    exact_mod_cast noncharacteristic
  have qInverseRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (((coframeTemporalPrincipalScalar
          (restarted.coframe candidate) : ℝ) : ℂ)⁻¹))
      point :=
    qComplexRegular.inv qComplexNe
  have gammaTimeRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          (0 : LorentzianIndex))
      point := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate (0 : LorentzianIndex)
    rw [← coframeAt] at outer
    exact outer.comp point coframeRegular
  have basisRegular : ContDiffAt ℝ ∞
      (fun _ : BasePoint =>
        matterCoordinateEquiv
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      point :=
    contDiffAt_const
  have gammaActionRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (gammaTimeRegular.of_le (by decide))).clm_apply basisRegular
    change ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    ((qInverseRegular.of_le (by decide)).smul
      ((contDiffAt_const :
        ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
          gammaActionRegular))

private theorem restart_temporalPrincipalScalar_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        coframeTemporalPrincipalScalar (restarted.coframe candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have restartedCoframeRegular : ContDiffAt ℝ 0 restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact coframeRegular
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have inverseRegular : ContDiffAt ℝ 0
      (fun candidate => (restarted.coframe candidate)⁻¹)
      point := by
    have outer : ContDiffAt ℝ 0
        (fun candidate : LorentzianCoframe => candidate⁻¹)
        (current.coframe point) :=
      (StageNineCoframeVariation.coframe_inv_contDiffAt
        (current.coframe point) nondegenerate).of_le (by norm_num)
    rw [← coframeAt] at outer
    exact outer.comp point restartedCoframeRegular
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntryRegular : ContDiffAt ℝ 0
      (fun candidate =>
        (restarted.coframe candidate)⁻¹
          (0 : LorentzianIndex) internal)
      point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntryRegular.pow 2)

private theorem restart_temporalPrincipalInverse_basis_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point)
    (index : MatterCoordinateIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have restartedCoframeRegular : ContDiffAt ℝ 0 restarted.coframe point := by
    rw [restart_coframe_eq_current source current]
    exact coframeRegular
  have coframeAt : restarted.coframe point = current.coframe point :=
    congrFun (restart_coframe_eq_current source current) point
  have qComplexRegular : ContDiffAt ℝ 0
      (fun candidate =>
        ((coframeTemporalPrincipalScalar
          (restarted.coframe candidate) : ℝ) : ℂ))
      point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (restart_temporalPrincipalScalar_contDiffAt_of_local
        source current point nondegenerate coframeRegular)
  have qComplexNe :
      ((coframeTemporalPrincipalScalar
        (restarted.coframe point) : ℝ) : ℂ) ≠ 0 := by
    rw [coframeAt]
    exact_mod_cast noncharacteristic
  have qInverseRegular : ContDiffAt ℝ 0
      (fun candidate =>
        (((coframeTemporalPrincipalScalar
          (restarted.coframe candidate) : ℝ) : ℂ)⁻¹))
      point :=
    qComplexRegular.inv qComplexNe
  have gammaTimeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          (0 : LorentzianIndex))
      point := by
    have outer : ContDiffAt ℝ 0
        (fun candidate : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := candidate, derivative := 0 }
            (0 : LorentzianIndex))
        (current.coframe point) :=
      (inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate
        (0 : LorentzianIndex)).of_le (by norm_num)
    rw [← coframeAt] at outer
    exact outer.comp point restartedCoframeRegular
  have basisRegular : ContDiffAt ℝ 0
      (fun _ : BasePoint =>
        matterCoordinateEquiv
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      point :=
    contDiffAt_const
  have gammaActionRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaTimeRegular).clm_apply basisRegular
    change ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    qInverseRegular.smul
      ((contDiffAt_const :
        ContDiffAt ℝ 0 (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
          gammaActionRegular)

private theorem restart_spinLift_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        diracSpinConnectionLift
          (restarted.gravityConnection candidate) direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro pair _
  have realCoefficientRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          restarted.gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair))
      point :=
    contDiffAt_const.mul
      ((cartanReactionRestart_connection_component_contDiffAt
        source current smooth point nondegenerate direction
        (lorentzBivectorFirst pair) (lorentzBivectorSecond pair)).of_le
          (by decide))
  have complexCoefficientRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          restarted.gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ))
      point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point realCoefficientRegular
  exact (contDiffAt_const.mul complexCoefficientRegular).mul contDiffAt_const

private theorem restart_spinLift_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (direction : LorentzianIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        diracSpinConnectionLift
          (restarted.gravityConnection candidate) direction)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro pair _
  have realCoefficientRegular : ContDiffAt ℝ 0
      (fun candidate =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          restarted.gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair))
      point :=
    contDiffAt_const.mul
      (cartanReactionRestart_connection_component_contDiffAt_of_local
        source current point nondegenerate coframeRegular
        (matterRegular.of_le (by norm_num))
        conjugateRegular direction (lorentzBivectorFirst pair)
        (lorentzBivectorSecond pair))
  have complexCoefficientRegular : ContDiffAt ℝ 0
      (fun candidate =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          restarted.gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ))
      point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point realCoefficientRegular
  exact (contDiffAt_const.mul complexCoefficientRegular).mul contDiffAt_const

private theorem restart_connectionOperator_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicIdentityCoframeMatterConnectionOperator
            restarted candidate direction) (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have spinActionRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (restarted.gravityConnection candidate) direction)
            (vector candidate)))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (restart_spinLift_contDiffAt
            source current smooth point nondegenerate direction)).clm_apply
          vectorRegular
    change ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (restarted.gravityConnection candidate) direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        p286CoordinateEquiv
          (restarted.gaugeConnection candidate direction))
      point := by
    simpa [restarted] using
      (smooth.2.2.2.2.1 direction).contDiffAt.of_le (by decide)
  have gaugeActionRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (restarted.gaugeConnection candidate direction))
            (vector candidate)))
      point := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gaugeRegular).clm_apply vectorRegular
    change ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (restarted.gaugeConnection candidate direction))))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterConnectionOperator
  simp only [LinearMap.add_apply, map_add]
  exact spinActionRegular.add gaugeActionRegular

private theorem restart_connectionOperator_coordinate_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicIdentityCoframeMatterConnectionOperator
            restarted candidate direction) (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have spinActionRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (restarted.gravityConnection candidate) direction)
            (vector candidate)))
      point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (restart_spinLift_contDiffAt_of_local source current point
            nondegenerate coframeRegular matterRegular conjugateRegular
            direction)).clm_apply vectorRegular
    change ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (restarted.gravityConnection candidate) direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have restartedGaugeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        p286CoordinateEquiv
          (restarted.gaugeConnection candidate direction))
      point := by
    simpa [restarted] using gaugeRegular direction
  have gaugeActionRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (restarted.gaugeConnection candidate direction))
            (vector candidate)))
      point := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point restartedGaugeRegular).clm_apply vectorRegular
    change ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (restarted.gaugeConnection candidate direction))))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterConnectionOperator
  simp only [LinearMap.add_apply, map_add]
  exact spinActionRegular.add gaugeActionRegular

private theorem restart_scalar_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞ (fun candidate => restarted.scalar candidate) point := by
  dsimp only
  simpa using smooth.2.2.2.2.2.2.1.contDiffAt.of_le (by decide)

private theorem restart_scalar_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0 (fun candidate => restarted.scalar candidate) point := by
  dsimp only
  simpa using scalarRegular

private theorem restart_algebraicOperator_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have directionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (restarted.coframe candidate) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                restarted candidate direction) (vector candidate))))
        point := by
    intro direction
    exact
      restart_livePrincipal_coordinate_contDiffAt
        source current smooth point nondegenerate direction
        (restart_connectionOperator_coordinate_contDiffAt
          source current smooth point nondegenerate direction vectorRegular)
  have sumRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (restarted.coframe candidate) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                restarted candidate direction) (vector candidate))))
      point :=
    ContDiffAt.sum fun direction _ => directionRegular direction
  have yukawaRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (restarted.scalar candidate))
            (vector candidate)))
      point := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (restart_scalar_contDiffAt source current smooth point)).clm_apply
            vectorRegular
    change ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (restarted.scalar candidate))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sum]
  exact sumRegular.add yukawaRegular

private theorem restart_algebraicOperator_coordinate_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have directionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (restarted.coframe candidate) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                restarted candidate direction) (vector candidate))))
        point := by
    intro direction
    exact
      restart_livePrincipal_coordinate_contDiffAt_of_local
        source current point nondegenerate
        (coframeRegular.of_le (by norm_num)) direction
        (restart_connectionOperator_coordinate_contDiffAt_of_local
          source current point nondegenerate coframeRegular matterRegular
          conjugateRegular gaugeRegular direction vectorRegular)
  have sumRegular : ContDiffAt ℝ 0
      (fun candidate =>
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (restarted.coframe candidate) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                restarted candidate direction) (vector candidate))))
      point :=
    ContDiffAt.sum fun direction _ => directionRegular direction
  have yukawaRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (restarted.scalar candidate))
            (vector candidate)))
      point := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point
          (restart_scalar_contDiffAt_of_local
            source current point scalarRegular)).clm_apply vectorRegular
    change ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (restarted.scalar candidate))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector candidate)))))
      point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sum]
  exact sumRegular.add yukawaRegular

private theorem restart_spatialTransportCoordinates_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        restarted)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  apply contDiffAt_piLp'
  intro index
  change ContDiffAt ℝ ∞
    (fun candidate =>
      ∑ direction : Fin 3,
        ((generatedVolumeDensity
            (toContinuumPointField restarted candidate) : ℝ) : ℂ) *
          matterDualOfCoordinates
              (holonomicConjugateMatterDerivativeCoordinates
                restarted candidate direction.succ)
              ((liveCoframeMatterPrincipal
                  (restarted.coframe candidate) direction.succ)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))
    point
  apply ContDiffAt.sum
  intro direction _
  have vectorRegular :=
    restart_livePrincipal_coordinate_contDiffAt
      source current smooth point nondegenerate direction.succ
      (vector := fun _ =>
        matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))
      contDiffAt_const
  have derivativePairingRegular :=
    matterCoordinateDualPairing_contDiffAt
      ((restart_conjugateDerivativeCoordinates_contDiffAt
        source current smooth point direction.succ).of_le (by decide))
      vectorRegular
  exact
    ((restart_volume_contDiffAt
      source current smooth point nondegenerate).of_le
        (by decide)).mul derivativePairingRegular

private theorem restart_spatialTransportCoordinates_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        restarted)
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  apply contDiffAt_piLp'
  intro index
  change ContDiffAt ℝ 0
    (fun candidate =>
      ∑ direction : Fin 3,
        ((generatedVolumeDensity
            (toContinuumPointField restarted candidate) : ℝ) : ℂ) *
          matterDualOfCoordinates
              (holonomicConjugateMatterDerivativeCoordinates
                restarted candidate direction.succ)
              ((liveCoframeMatterPrincipal
                  (restarted.coframe candidate) direction.succ)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))
    point
  apply ContDiffAt.sum
  intro direction _
  have vectorRegular :=
    restart_livePrincipal_coordinate_contDiffAt_of_local
      source current point nondegenerate coframeRegular direction.succ
      (vector := fun _ =>
        matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))
      contDiffAt_const
  have derivativePairingRegular :=
    matterCoordinateDualPairing_contDiffAt
      (restart_conjugateDerivativeCoordinates_contDiffAt_of_local
        source current point conjugateRegular direction.succ)
      vectorRegular
  exact
    (restart_volume_contDiffAt_of_local
      source current point nondegenerate coframeRegular).mul
        derivativePairingRegular

private theorem restart_spatialPrincipalDrift_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates restarted)
      point := by
  dsimp only
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  exact ContDiffAt.sum fun direction _ =>
    restart_liveCoframeDensitizedPrincipalDrift_contDiffAt
      source current smooth point nondegenerate direction.succ

private theorem restart_temporalPrincipalDrift_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates restarted)
      point := by
  dsimp only
  exact
    restart_liveCoframeDensitizedPrincipalDrift_contDiffAt
      source current smooth point nondegenerate
        canonicalLorentzianTimeDirection

private theorem restart_spatialPrincipalDrift_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates restarted)
      point := by
  dsimp only
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  exact ContDiffAt.sum fun direction _ =>
    restart_liveCoframeDensitizedPrincipalDrift_contDiffAt_of_local
      source current point nondegenerate coframeRegular conjugateRegular
        direction.succ

private theorem restart_temporalPrincipalDrift_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates restarted)
      point := by
  dsimp only
  exact
    restart_liveCoframeDensitizedPrincipalDrift_contDiffAt_of_local
      source current point nondegenerate coframeRegular conjugateRegular
        canonicalLorentzianTimeDirection

private theorem restart_knownDensitizedDual_apply_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate (vector candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have algebraicVectorRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point :=
    restart_algebraicOperator_coordinate_contDiffAt
      source current smooth point nondegenerate vectorRegular
  have algebraicPairingRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        restarted.conjugateMatter candidate
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point :=
    restart_conjugateApply_contDiffAt
      source current smooth point algebraicVectorRegular
  have algebraicDualRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate))
      point := by
    rw [show
      (fun candidate =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate)) =
      (fun candidate =>
        ((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ) *
          restarted.conjugateMatter candidate
            ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
              restarted candidate) (vector candidate))) by
      funext candidate
      exact liveCoframeAlgebraicDual_apply
        restarted candidate (vector candidate)]
    exact
      ((restart_volume_contDiffAt
        source current smooth point nondegenerate).of_le
          (by decide)).mul algebraicPairingRegular
  have spatialTransportRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_spatialTransportCoordinates_contDiffAt
        source current smooth point nondegenerate)
      vectorRegular
  have spatialDriftRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_spatialPrincipalDrift_contDiffAt
        source current smooth point nondegenerate)
      vectorRegular
  have temporalDriftRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_temporalPrincipalDrift_contDiffAt
        source current smooth point nondegenerate)
      vectorRegular
  rw [show
    (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        restarted candidate (vector candidate)) =
    (fun candidate =>
      holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              restarted candidate)
            (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate)) by
      funext candidate
      exact liveCoframeKnownDensitizedDual_apply
        restarted candidate (vector candidate)]
  exact
    ((algebraicDualRegular.sub spatialTransportRegular).sub
      spatialDriftRegular).sub temporalDriftRegular

private theorem restart_knownDensitizedDual_apply_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv (vector candidate)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate (vector candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeRegularOne : ContDiffAt ℝ 1 current.coframe point :=
    coframeRegular.of_le (by norm_num)
  have coframeRegularZero : ContDiffAt ℝ 0 current.coframe point :=
    coframeRegular.of_le (by norm_num)
  have conjugateRegularZero : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point :=
    conjugateRegular.of_le (by norm_num)
  have algebraicVectorRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point :=
    restart_algebraicOperator_coordinate_contDiffAt_of_local
      source current point nondegenerate coframeRegularOne scalarRegular
      matterRegular conjugateRegularZero gaugeRegular vectorRegular
  have algebraicPairingRegular : ContDiffAt ℝ 0
      (fun candidate =>
        restarted.conjugateMatter candidate
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            restarted candidate) (vector candidate)))
      point :=
    restart_conjugateApply_contDiffAt_of_local
      source current point conjugateRegularZero algebraicVectorRegular
  have algebraicDualRegular : ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate))
      point := by
    rw [show
      (fun candidate =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate)) =
      (fun candidate =>
        ((generatedVolumeDensity
          (toContinuumPointField restarted candidate) : ℝ) : ℂ) *
          restarted.conjugateMatter candidate
            ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
              restarted candidate) (vector candidate))) by
      funext candidate
      exact liveCoframeAlgebraicDual_apply
        restarted candidate (vector candidate)]
    exact
      (restart_volume_contDiffAt_of_local
        source current point nondegenerate coframeRegularZero).mul
          algebraicPairingRegular
  have spatialTransportRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_spatialTransportCoordinates_contDiffAt_of_local
        source current point nondegenerate coframeRegularZero
          conjugateRegular)
      vectorRegular
  have spatialDriftRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_spatialPrincipalDrift_contDiffAt_of_local
        source current point nondegenerate coframeRegular conjugateRegular)
      vectorRegular
  have temporalDriftRegular : ContDiffAt ℝ 0
      (fun candidate =>
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate))
      point :=
    matterCoordinateDualPairing_contDiffAt
      (restart_temporalPrincipalDrift_contDiffAt_of_local
        source current point nondegenerate coframeRegular conjugateRegular)
      vectorRegular
  rw [show
    (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        restarted candidate (vector candidate)) =
    (fun candidate =>
      holonomicDiracDualLiveCoframeAlgebraicDual
          restarted candidate (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              restarted candidate)
            (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate) -
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              restarted candidate)
            (vector candidate)) by
      funext candidate
      exact liveCoframeKnownDensitizedDual_apply
        restarted candidate (vector candidate)]
  exact
    ((algebraicDualRegular.sub spatialTransportRegular).sub
      spatialDriftRegular).sub temporalDriftRegular

private theorem restart_liveAdjointActionVelocity_basis_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (index : MatterCoordinateIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            restarted candidate
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have knownRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point :=
    restart_knownDensitizedDual_apply_contDiffAt
      source current smooth point nondegenerate
      (restart_temporalPrincipalInverse_basis_contDiffAt
        source current smooth point nondegenerate noncharacteristic index)
  rw [show
    (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          restarted candidate
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
    (fun candidate =>
      (((generatedVolumeDensity
        (toContinuumPointField restarted candidate) : ℝ) : ℂ)⁻¹) *
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))) by
      funext candidate
      exact liveCoframeActionVelocity_apply
        restarted candidate
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))]
  exact
    (restart_inverseVolume_contDiffAt
      source current smooth point nondegenerate).of_le
        (by decide) |>.mul knownRegular

private theorem
    restart_liveAdjointActionVelocity_basis_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (index : MatterCoordinateIndex) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            restarted candidate
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeRegularZero : ContDiffAt ℝ 0 current.coframe point :=
    coframeRegular.of_le (by norm_num)
  have knownRegular : ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      point :=
    restart_knownDensitizedDual_apply_contDiffAt_of_local
      source current point nondegenerate coframeRegular scalarRegular
      matterRegular conjugateRegular gaugeRegular
      (restart_temporalPrincipalInverse_basis_contDiffAt_of_local
        source current point nondegenerate noncharacteristic
          coframeRegularZero index)
  rw [show
    (fun candidate =>
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          restarted candidate
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
    (fun candidate =>
      (((generatedVolumeDensity
        (toContinuumPointField restarted candidate) : ℝ) : ℂ)⁻¹) *
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          restarted candidate
          (currentCoframeMatterTemporalPrincipalInverse
            (restarted.coframe candidate)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))) by
      funext candidate
      exact liveCoframeActionVelocity_apply
        restarted candidate
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))]
  exact
    (restart_inverseVolume_contDiffAt_of_local
      source current point nondegenerate coframeRegularZero).mul knownRegular

private theorem restart_liveAdjointActionVelocity_coordinates_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            restarted candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  exact matterDualCoordinates_contDiffAt_of_basis
    (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity restarted)
    point
    (restart_liveAdjointActionVelocity_basis_contDiffAt
      source current smooth point nondegenerate noncharacteristic)

private theorem
    restart_liveAdjointActionVelocity_coordinates_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point) :
    let restarted :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
    ContDiffAt ℝ 0
      (fun candidate =>
        matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            restarted candidate))
      point := by
  dsimp only
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  exact matterDualCoordinates_contDiffAt_of_basis
    (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity restarted)
    point
    (restart_liveAdjointActionVelocity_basis_contDiffAt_of_local
      source current point nondegenerate noncharacteristic coframeRegular
      scalarRegular matterRegular conjugateRegular gaugeRegular)

private theorem recenteredCurrent_coframeFirstJet_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration current contact).coframe 0 =
      holonomicCoframeFirstJetAt current.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => current.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => current.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => current.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem recenteredCurrent_spinResponse_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionSpinResponseAt source current contact := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · exact fullyRecenterHolonomicConfiguration_matter_origin _ _
  · exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem recenteredCurrent_actionCartanConnection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionCartanConnectionAt source current contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredCurrent_coframeFirstJet_origin,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    recenteredCurrent_spinResponse_origin]

private theorem profileRestart_coframeFirstJet_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (completeJointGeneratedProfileRestartCurrent
          source current contact).coframe 0 =
      holonomicCoframeFirstJetAt
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).coframe contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  exact recenteredCurrent_coframeFirstJet_origin current contact

private theorem profileRestart_connection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        source current contact).gravityConnection 0 =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravityConnection contact := by
  change
    diracDualFormNativeActionCartanConnectionAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionCartanConnectionAt source current contact
  exact recenteredCurrent_actionCartanConnection_origin source current contact

private theorem profileRestart_gaugeConnection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        source current contact).gaugeConnection 0 =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gaugeConnection contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  exact fullyRecenterHolonomicConfiguration_gaugeConnection_origin _ _

private theorem profileRestart_scalar_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        source current contact).scalar 0 =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).scalar contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]
  exact fullyRecenterHolonomicConfiguration_scalar_origin _ _

private theorem profileRestart_conjugateMatter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        source current contact).conjugateMatter 0 =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).conjugateMatter contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem profileRestart_conjugateMatterDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (completeJointGeneratedProfileRestartCurrent source current contact)
        0 direction =
      holonomicConjugateMatterDerivativeDual
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        contact direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  change
    matterDualOfCoordinates
        (fieldDirectionalDerivative
          ((fun point =>
            matterDualCoordinates (current.conjugateMatter point)) ∘
              canonicalSpacetimeContactTranslation contact)
          0 direction) =
      matterDualOfCoordinates
        (fieldDirectionalDerivative
          (fun point => matterDualCoordinates (current.conjugateMatter point))
          contact direction)
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp [canonicalSpacetimeContactTranslation]

private theorem liveAdjointActionVelocity_primalWrite_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration 0 := by
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro direction
    rfl

private theorem profileRestart_liveAdjointActionVelocity_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (completeJointGeneratedProfileRestartCurrent source current contact)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        contact := by
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · exact profileRestart_coframeFirstJet_origin source current contact
  · exact profileRestart_connection_origin source current contact
  · exact profileRestart_gaugeConnection_origin source current contact
  · exact profileRestart_scalar_origin source current contact
  · exact profileRestart_conjugateMatter_origin source current contact
  · exact profileRestart_conjugateMatterDerivative_origin source current contact

private theorem profile_adjointVelocity_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      source current contact).adjointVelocity =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        contact := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    liveAdjointActionVelocity_primalWrite_origin,
    profileRestart_liveAdjointActionVelocity_origin]

/-- Exact action-data normal form of the complete-joint adjoint correction.
The contact recenter is eliminated in favor of the same current's Cartan
restart at that contact. -/
theorem completeJointAdjointTemporalCoordinateCorrection_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    completeJointAdjointTemporalCoordinateCorrection source current contact =
      matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current)
            contact) -
        fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates current)
          contact canonicalLorentzianTimeDirection := by
  unfold completeJointAdjointTemporalCoordinateCorrection
  rw [profile_adjointVelocity_normalForm]

/-- Arbitrary-contact smoothness of the action-generated adjoint temporal
correction.  Nondegeneracy and noncharacteristicity describe the supplied
current at the occurrence; no response or equation certificate is supplied. -/
theorem completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (completeJointAdjointTemporalCoordinateCorrection source current)
      point := by
  rw [show
    completeJointAdjointTemporalCoordinateCorrection source current =
      fun contact =>
        matterDualCoordinates
            (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
              (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current)
              contact) -
          fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates current)
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact completeJointAdjointTemporalCoordinateCorrection_normalForm
      source current contact]
  exact
    (restart_liveAdjointActionVelocity_coordinates_contDiffAt
      source current smooth point nondegenerate noncharacteristic).sub
    ((holonomicConjugateMatterDerivativeCoordinates_contDiff
      current smooth canonicalLorentzianTimeDirection).contDiffAt.of_le
        (by decide))

/-- Minimal local regularity mouth for the complete-joint adjoint correction.
The extra coframe derivative pays for the action-owned affine momentum drift;
the conjugate first jet pays both its spatial transport and the subtracted
current temporal derivative.  No global `Smooth` receipt, residual, target
velocity, or branch choice is supplied. -/
theorem completeJointAdjointTemporalCoordinateCorrection_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection source current)
      point := by
  rw [show
    completeJointAdjointTemporalCoordinateCorrection source current =
      fun contact =>
        matterDualCoordinates
            (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
              (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current)
              contact) -
          fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates current)
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact completeJointAdjointTemporalCoordinateCorrection_normalForm
      source current contact]
  have derivativeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates current)
          candidate canonicalLorentzianTimeDirection) point := by
    unfold fieldDirectionalDerivative
    exact
      (conjugateRegular.fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const
  exact
    (restart_liveAdjointActionVelocity_coordinates_contDiffAt_of_local
      source current point nondegenerate noncharacteristic coframeRegular
      scalarRegular matterRegular conjugateRegular gaugeRegular).sub
        derivativeRegular

/-- Backward-compatible continuity mouth for consumers that require only the
zeroth-order readout. -/
theorem completeJointAdjointTemporalCoordinateCorrection_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection source current)
      point :=
  (completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
    source current smooth point nondegenerate noncharacteristic).of_le
      (by decide)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
