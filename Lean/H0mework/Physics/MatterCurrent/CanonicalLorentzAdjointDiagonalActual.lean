import H0mework.Physics.Cauchy.CanonicalCauchyCoordinateProjection
import H0mework.Physics.MatterCurrent.CanonicalLorentzAdjointCauchyUpdate

/-!
# C3h196: exact P506/L0 post-Lorentz adjoint diagonal actual

C3h195 generates one branch-free whole-slice adjoint Cauchy response from the
actual C3h189 final slice.  This module installs exactly that generated
conjugate-matter path on the diagonal of the existing C3h189 holonomic actual.
The other eight primitive fields, including their genuine spacetime jets, are
retained rather than reconstructed from a frozen Cauchy path.

The construction consumes no residual coordinate, current support, event,
scheduler, branch witness, or target receipt.  Its response operator remains
the C3h195 unique faithful-zero-fiber operator.  Future source-owned event
provenance can be attached only after the actual is fixed and therefore cannot
select a branch or turn this local actualization into global source-time
evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdate
open StageNineCoframeScalarMatterRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure
open SU7ExteriorBreakingYukawa
open SU7MotherGaugeTheory

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
      (canonicalTimeProjection point)).conjugateMatter
    (canonicalSpatialProjection point)

def positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0 with
    conjugateMatter :=
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter }

theorem positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_adjointPathFidelity
    (time : ℝ) (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint time space) =
      (positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate time).conjugateMatter
        space := by
  simp only [positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual,
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter,
    canonicalTimeProjection_slice, canonicalSpatialProjection_slice]

theorem fixedMatterDual_apply_coordinate_contDiff
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (field : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (smooth : ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv (field localSpace))) :
    ContDiff ℝ ∞ (fun localSpace => dual (field localSpace)) := by
  rw [show
    (fun localSpace => dual (field localSpace)) =
      fun localSpace =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (field localSpace) index *
            dual (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
    funext localSpace
    simpa using
      (matterDual_coordinate_expansion dual
        (matterCoordinateEquiv (field localSpace)))]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have coordinateSmooth : ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv (field localSpace) index) := by
    exact (projection.restrictScalars ℝ).contDiff.comp smooth
  exact coordinateSmooth.mul contDiff_const

private abbrev positiveFinalState : StageNineCauchyState :=
  positiveP506MatterCurrentCanonicalLorentzFinalCauchyState

private abbrev positivePriorActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0

theorem canonicalZeroSlice_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 =
      fun localSpace =>
        EuclideanSpace.single canonicalLorentzianTimeDirection 0 +
          canonicalSpatialInclusion localSpace by
    funext localSpace
    exact canonicalCauchySlicePoint_eq_const_add_inclusion 0 localSpace]
  exact contDiff_const.add canonicalSpatialInclusion.contDiff

theorem positiveFinalState_gravityConnection_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ (fun localSpace =>
      positiveFinalState.gravityConnection localSpace formDirection
        internalOut internalIn) := by
  change ContDiff ℝ ∞ (fun localSpace =>
    positivePriorActual.gravityConnection
      (canonicalCauchySlicePoint 0 localSpace) formDirection
      internalOut internalIn)
  exact
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth
      0).2.1 formDirection internalOut internalIn
      |>.comp canonicalZeroSlice_contDiff

theorem positiveFinalState_scalar_contDiff :
    ContDiff ℝ ∞ positiveFinalState.scalar := by
  change ContDiff ℝ ∞ (fun localSpace =>
    positivePriorActual.scalar (canonicalCauchySlicePoint 0 localSpace))
  exact
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth
      0).2.2.2.2.2.2.1.comp canonicalZeroSlice_contDiff

theorem positiveFinalState_spinLift_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fun localSpace =>
      diracSpinConnectionLift
        (positiveFinalState.gravityConnection localSpace) direction) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro pair _
  have realCoefficientSmooth : ContDiff ℝ ∞ (fun localSpace =>
      minkowskiInternalSign (lorentzBivectorFirst pair) *
        positiveFinalState.gravityConnection localSpace direction
          (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair)) :=
    contDiff_const.mul
      (positiveFinalState_gravityConnection_contDiff direction
        (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
  have complexCoefficientSmooth : ContDiff ℝ ∞ (fun localSpace =>
      ((minkowskiInternalSign (lorentzBivectorFirst pair) *
        positiveFinalState.gravityConnection localSpace direction
          (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp realCoefficientSmooth
  exact (contDiff_const.mul complexCoefficientSmooth).mul contDiff_const

theorem positiveFinalState_algebraicResponse_coordinate_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv
        (actionGeneratedMatterAlgebraicOperator positiveFinalState localSpace
          matter)) := by
  have gaugeConnectionZero : positiveFinalState.gaugeConnection = 0 := by
    funext localSpace direction
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_canonicalZeroSlice_zero
        localSpace direction
  have matterCoordinatesConstant : ContDiff ℝ ∞ (fun _ : StageNineSpatialPoint =>
      matterCoordinateEquiv matter) := contDiff_const
  have spinSummandSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞ (fun localSpace =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (diracMatrixMatterAction
              (diracSpinConnectionLift
                (positiveFinalState.gravityConnection localSpace) direction)
              matter))) := by
    intro direction
    have innerSmooth : ContDiff ℝ ∞ (fun localSpace =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (positiveFinalState.gravityConnection localSpace) direction)
            matter)) := by
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
          (positiveFinalState_spinLift_contDiff direction)).clm_apply
            matterCoordinatesConstant
      change ContDiff ℝ ∞ (fun localSpace =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (positiveFinalState.gravityConnection localSpace) direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv matter)))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : StageNineSpatialPoint => diracGamma direction))).clm_apply
            innerSmooth
    change ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (diracMatrixMatterAction
                (diracSpinConnectionLift
                  (positiveFinalState.gravityConnection localSpace) direction)
                matter))))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have spinSumSmooth : ContDiff ℝ ∞ (fun localSpace =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (diracMatrixMatterAction
              (diracSpinConnectionLift
                (positiveFinalState.gravityConnection localSpace) direction)
              matter))) := by
    apply ContDiff.sum
    intro direction _
    exact spinSummandSmooth direction
  have yukawaSmooth : ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm
            (positiveFinalState.scalar localSpace)) matter)) := by
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        positiveFinalState_scalar_contDiff).clm_apply matterCoordinatesConstant
    change ContDiff ℝ ∞ (fun localSpace =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm
            (positiveFinalState.scalar localSpace))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv matter)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  rw [show (fun localSpace =>
      matterCoordinateEquiv
        (actionGeneratedMatterAlgebraicOperator positiveFinalState localSpace
          matter)) =
    fun localSpace =>
      Complex.I •
          (∑ direction : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction (diracGamma direction)
                (diracMatrixMatterAction
                  (diracSpinConnectionLift
                    (positiveFinalState.gravityConnection localSpace)
                    direction) matter))) +
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm
              (positiveFinalState.scalar localSpace)) matter) by
    funext localSpace
    unfold actionGeneratedMatterAlgebraicOperator
      cauchyMatterVariationConnectionOperator
    rw [gaugeConnectionZero]
    simp only [Pi.zero_apply, p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, map_add, map_smul, map_sum,
      add_zero]]
  have phasedSpinSumSmooth : ContDiff ℝ ∞ (fun localSpace =>
      Complex.I •
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma direction)
              (diracMatrixMatterAction
                (diracSpinConnectionLift
                  (positiveFinalState.gravityConnection localSpace) direction)
                matter))) :=
    (contDiff_const : ContDiff ℝ ∞
      (fun _ : StageNineSpatialPoint => Complex.I)).smul spinSumSmooth
  exact phasedSpinSumSmooth.add yukawaSmooth

theorem positiveVelocity_apply_eq_algebraic
    (localSpace : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    positiveP506MatterCurrentCanonicalLorentzAdjointVelocity localSpace matter =
      diracSpinZeroMatterCoordinate
        (actionGeneratedMatterAlgebraicOperator positiveFinalState localSpace
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection matter)) := by
  have conjugateMatterConstant : positiveFinalState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
    funext space
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice
        space
  unfold positiveP506MatterCurrentCanonicalLorentzAdjointVelocity
    currentCanonicalFullActionLorentzAdjointVelocity
    actionGeneratedConjugateMatterTimeDerivative
    actionGeneratedConjugateMatterKnownDual
    actionGeneratedConjugateMatterSpatialTransport
    cauchyConjugateMatterSpatialDerivative
    cauchyConjugateMatterSpatialDerivativeCoordinate
  rw [conjugateMatterConstant]
  simp [matterDualCoordinates, matterDualOfCoordinates]

theorem positiveVelocity_coordinate_smooth
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ (fun localSpace =>
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity localSpace
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
  rw [show (fun localSpace =>
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity localSpace
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
    fun localSpace =>
      diracSpinZeroMatterCoordinate
        (actionGeneratedMatterAlgebraicOperator positiveFinalState localSpace
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))) by
    funext localSpace
    exact positiveVelocity_apply_eq_algebraic localSpace _]
  exact fixedMatterDual_apply_coordinate_contDiff
    diracSpinZeroMatterCoordinate _
    (positiveFinalState_algebraicResponse_coordinate_contDiff _)

theorem positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter_coordinate_contDiff
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ (fun point =>
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
  rw [show (fun point =>
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
    fun point =>
      positiveFinalState.conjugateMatter
          (canonicalSpatialProjection point)
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) +
        canonicalTimeProjection point •
          positiveP506MatterCurrentCanonicalLorentzAdjointVelocity
            (canonicalSpatialProjection point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
    funext point
    exact
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 (canonicalSpatialProjection point) (canonicalTimeProjection point) _]
  have baselineSmooth : ContDiff ℝ ∞ (fun point =>
      positiveFinalState.conjugateMatter
        (canonicalSpatialProjection point)
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
    rw [show (fun point =>
        positiveFinalState.conjugateMatter
          (canonicalSpatialProjection point)
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) =
      fun _ : BasePoint =>
        diracSpinZeroMatterCoordinate
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) by
      funext point
      rw [show positiveFinalState.conjugateMatter
          (canonicalSpatialProjection point) =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) by
        exact
          positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice
            (canonicalSpatialProjection point)]]
    exact contDiff_const
  have velocitySmooth : ContDiff ℝ ∞ (fun point =>
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity
        (canonicalSpatialProjection point)
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) :=
    (positiveVelocity_coordinate_smooth index).comp
      canonicalSpatialProjection.contDiff
  exact baselineSmooth.add
    (canonicalTimeProjection.contDiff.smul velocitySmooth)

theorem conjugateMatterOverlay_smooth
    (base : StageNineHolonomicConfiguration)
    (newConjugateMatter :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (baseSmooth : base.Smooth)
    (newConjugateMatterSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        newConjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index 1))) :
    ({ base with conjugateMatter := newConjugateMatter } :
      StageNineHolonomicConfiguration).Smooth := by
  rcases baseSmooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, _⟩
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
    scalarSmooth, matterSmooth, newConjugateMatterSmooth⟩

theorem conjugateMatterOverlay_nondegenerate
    (base : StageNineHolonomicConfiguration)
    (newConjugateMatter :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (baseNondegenerate : base.Nondegenerate) :
    ({ base with conjugateMatter := newConjugateMatter } :
      StageNineHolonomicConfiguration).Nondegenerate := by
  intro point
  exact baseNondegenerate point

theorem canonicalCauchyRestriction_zero_conjugateMatterOverlay
    (base : StageNineHolonomicConfiguration)
    (newConjugateMatter :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (zeroSliceFidelity : ∀ localSpace,
      newConjugateMatter (canonicalCauchySlicePoint 0 localSpace) =
        base.conjugateMatter (canonicalCauchySlicePoint 0 localSpace)) :
    canonicalCauchyRestriction 0
        ({ base with conjugateMatter := newConjugateMatter } :
          StageNineHolonomicConfiguration) =
      canonicalCauchyRestriction 0 base := by
  apply StageNineCauchyState.ext <;> try rfl
  funext localSpace
  exact zeroSliceFidelity localSpace

theorem positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_smooth :
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.Smooth := by
  exact conjugateMatterOverlay_smooth _ _
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0)
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter_coordinate_contDiff

theorem positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_nondegenerate :
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.Nondegenerate := by
  exact conjugateMatterOverlay_nondegenerate _ _
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_nondegenerate 0)

theorem positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_zeroSlice :
    canonicalCauchyRestriction 0
        positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual =
      positiveFinalState := by
  change canonicalCauchyRestriction 0
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual =
    canonicalCauchyRestriction 0 positivePriorActual
  apply canonicalCauchyRestriction_zero_conjugateMatterOverlay
  intro localSpace
  simp only [
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalConjugateMatter,
    canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  change
    (positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate 0).conjugateMatter
        localSpace =
      positiveFinalState.conjugateMatter localSpace
  exact congrArg (·.conjugateMatter localSpace)
    (currentCanonicalFullActionLorentzAdjointCauchyUpdate_zero
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      0)

/-! ## Exact actual authority -/

/-- The diagonal installation changes only the adjoint primitive field.  This
predicate deliberately excludes the conjugate-matter field itself. -/
def RetainsEightNonAdjointPrimitiveFields
    (candidate baseline : StageNineHolonomicConfiguration) : Prop :=
  candidate.coframe = baseline.coframe ∧
    candidate.gravityConnection = baseline.gravityConnection ∧
    candidate.gravityAuxiliary = baseline.gravityAuxiliary ∧
    candidate.gravitySimplicityMultiplier =
      baseline.gravitySimplicityMultiplier ∧
    candidate.gaugeConnection = baseline.gaugeConnection ∧
    candidate.gaugeAuxiliary = baseline.gaugeAuxiliary ∧
    candidate.scalar = baseline.scalar ∧
    candidate.matter = baseline.matter

private theorem conjugateMatterOverlay_retainsEightNonAdjointPrimitiveFields
    (baseline : StageNineHolonomicConfiguration)
    (newConjugateMatter :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    RetainsEightNonAdjointPrimitiveFields
      ({ baseline with conjugateMatter := newConjugateMatter } :
        StageNineHolonomicConfiguration)
      baseline := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_retainsPriorFields :
    RetainsEightNonAdjointPrimitiveFields
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0) := by
  exact conjugateMatterOverlay_retainsEightNonAdjointPrimitiveFields _ _

theorem
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_responseVelocity_unique
    (candidate :
      StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw : ∀ localSpace,
      IdentityCoframeConjugateMatterTimeActionLaw
        positiveP506MatterCurrentCanonicalLorentzFinalCauchyState
        localSpace (candidate localSpace)) :
    candidate =
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity := by
  exact currentCanonicalFullActionLorentzAdjointVelocity_unique
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    0 candidate candidateLaw

theorem
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_responseFaithfulZeroFiber :
    positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate 1 =
        positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate 0 ↔
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity = 0 := by
  exact currentCanonicalFullActionLorentzAdjointCauchyUpdate_faithfulZeroFiber
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    0

/-- C3h196 is a local holonomic actualization of the already-generated C3h195
response.  It neither supplies a new action receipt nor counts the action-law
substitution as an independent constraint. -/
structure PositiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActualLaw :
    Prop where
  priorC3h195 :
    PositiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdateLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  retainsPriorFields :
    RetainsEightNonAdjointPrimitiveFields
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
  smooth :
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.Smooth
  nondegenerate :
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.Nondegenerate
  zeroSlice :
    canonicalCauchyRestriction 0
        positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual =
      positiveP506MatterCurrentCanonicalLorentzFinalCauchyState
  adjointPathFidelity : ∀ time localSpace,
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint time localSpace) =
      (positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate time).conjugateMatter
        localSpace
  responseVelocityUnique : ∀ candidate :
      StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier,
    (∀ localSpace,
      IdentityCoframeConjugateMatterTimeActionLaw
        positiveP506MatterCurrentCanonicalLorentzFinalCauchyState
        localSpace (candidate localSpace)) →
      candidate =
        positiveP506MatterCurrentCanonicalLorentzAdjointVelocity
  responseFaithfulZeroFiber :
    positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate 1 =
        positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate 0 ↔
      positiveP506MatterCurrentCanonicalLorentzAdjointVelocity = 0

/-- Frontier theorem: the branch-free C3h195 response now has one smooth,
nondegenerate, exact-lineage holonomic diagonal actual. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_realizes_C3h196 :
    PositiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActualLaw where
  priorC3h195 :=
    positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate_realizes_C3h195
  exactP506L0Lineage :=
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_exactP506L0Lineage
  retainsPriorFields :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_retainsPriorFields
  smooth :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_smooth
  nondegenerate :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_nondegenerate
  zeroSlice :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_zeroSlice
  adjointPathFidelity :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_adjointPathFidelity
  responseVelocityUnique :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_responseVelocity_unique
  responseFaithfulZeroFiber :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_responseFaithfulZeroFiber

/-! ## Opaque future source-owned provenance transport -/

structure SourceOwnedProvenanceLorentzAdjointDiagonalActual
    (Provenance : Type*) where
  sourceOwnedProvenance : Provenance
  actual : StageNineHolonomicConfiguration

/-- Provenance is attached after the physical actual is fixed.  In
particular, P286 current support cannot be reinterpreted here as an event or a
branch selector. -/
def transportSourceOwnedProvenanceToLorentzAdjointDiagonalActual
    {Provenance : Type*} (provenance : Provenance) :
    SourceOwnedProvenanceLorentzAdjointDiagonalActual Provenance where
  sourceOwnedProvenance := provenance
  actual :=
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

@[simp] theorem
    transportSourceOwnedProvenanceToLorentzAdjointDiagonalActual_provenance
    {Provenance : Type*} (provenance : Provenance) :
    (transportSourceOwnedProvenanceToLorentzAdjointDiagonalActual
      provenance).sourceOwnedProvenance = provenance :=
  rfl

@[simp] theorem
    transportSourceOwnedProvenanceToLorentzAdjointDiagonalActual_actual
    {Provenance : Type*} (provenance : Provenance) :
    (transportSourceOwnedProvenanceToLorentzAdjointDiagonalActual
      provenance).actual =
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
