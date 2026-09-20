import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzMatterActionNormalForm

/-!
# C3h207d: latest-current same-actual Lorentz matter-spin tangency

The latest current and the full action first generate the C3h203 judged
actual.  This module then differentiates that actual's Lorentz matter-spin
coefficient in finite faithful matter coordinates.  Both product-rule legs
come from the same actual first germ exposed by C3h207b; the synchronized
action normal form of C3h207c is used only after the genuine derivative has
been constructed.

Thus the result is a same-actual response readout, not a residual-defined
correction and not a supplied tangency certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterSpinTangency

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConnectionSectorSourceBalance
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionVariation
open StageNineLorentzTemporalGaussFirstVariation
open StageNineMatterActionTimeVelocity
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzFirstVariationObstruction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterActionNormalForm
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterFirstGermReadout
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

private abbrev JudgedActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedLorentzActual

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_coframe_one
    (point : BasePoint) :
    JudgedActual.coframe point = (1 : LorentzianCoframe) := by
  exact currentFullSynchronizedLorentzActualFirstJetLift_coframe_one
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0
    preContorsionFullLorentzTriangularCurrent_coframe_origin point

/-! ## Finite faithful temporal-spin coordinates -/

def positiveP506MatterCurrentTemporalSpinCoordinateLinear
    (internalPair : Fin 6) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ((matterCoordinateEquiv.toLinearMap.comp
      ((positiveP506MatterCurrentTemporalSpinAction internalPair).comp
        matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap
    ).restrictScalars ℝ

@[simp] theorem positiveP506MatterCurrentTemporalSpinCoordinateLinear_apply
    (internalPair : Fin 6)
    (coordinates : MatterCoordinateCarrier) :
    positiveP506MatterCurrentTemporalSpinCoordinateLinear
        internalPair coordinates =
      matterCoordinateEquiv
        (positiveP506MatterCurrentTemporalSpinActionVector internalPair
          (matterCoordinateEquiv.symm coordinates)) := by
  rfl

def positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
    (internalPair : Fin 6)
    (point : BasePoint) : MatterCoordinateCarrier :=
  positiveP506MatterCurrentTemporalSpinCoordinateLinear internalPair
    (matterCoordinateEquiv (JudgedActual.matter point))

theorem
    positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector_contDiff
    (internalPair : Fin 6) :
    ContDiff ℝ ∞
      (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
        internalPair) := by
  rcases positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth with
    ⟨_, _, _, _, _, _, _, matterSmooth, _⟩
  exact
    (positiveP506MatterCurrentTemporalSpinCoordinateLinear
      internalPair).contDiff.comp matterSmooth

theorem
    positiveP506MatterCurrentFullSynchronizedConjugateMatterCoordinate_contDiff
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      JudgedActual.conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_eq_localField]
  exact actionGeneratedConjugateMatterLocalField_smooth
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0 index

theorem
    positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector_directionalDerivative
    (internalPair : Fin 6)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
          internalPair)
        0 derivativeDirection =
      positiveP506MatterCurrentTemporalSpinCoordinateLinear internalPair
        (actionGeneratedMatterLocalJetCoordinate
          positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0
          derivativeDirection) := by
  let coordinates : BasePoint → MatterCoordinateCarrier := fun point =>
    matterCoordinateEquiv (JudgedActual.matter point)
  let action :=
    positiveP506MatterCurrentTemporalSpinCoordinateLinear internalPair
  have coordinatesDifferentiable : DifferentiableAt ℝ coordinates 0 := by
    rcases positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth with
      ⟨_, _, _, _, _, _, _, matterSmooth, _⟩
    exact (matterSmooth.differentiable (by simp)).differentiableAt
  have composed :=
    action.hasFDerivAt.comp 0 coordinatesDifferentiable.hasFDerivAt
  rw [show
    positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
        internalPair =
      action ∘ coordinates by rfl]
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change
    action (fieldDirectionalDerivative coordinates 0 derivativeDirection) =
      _
  rw [show
    fieldDirectionalDerivative coordinates 0 derivativeDirection =
      actionGeneratedMatterLocalJetCoordinate
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0
        derivativeDirection by
    exact
      positiveP506MatterCurrentFullSynchronizedLorentzActual_matter_completeFirstGerm
        derivativeDirection]

theorem
    positiveP506MatterCurrentFullSynchronizedConjugateMatterCoordinate_directionalDerivative
    (index : MatterCoordinateIndex)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          JudgedActual.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        0 direction =
      actionGeneratedConjugateMatterLocalJet
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0
        direction
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) := by
  exact
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_completeFirstGerm
      direction
      (matterCoordinateEquiv.symm
        (EuclideanSpace.single index (1 : ℂ)))

/-! ## Dependency-light product-rule helpers -/

private theorem fieldDirectionalDerivative_matterCoordinate_apply_at_origin
    (field : BasePoint → MatterCoordinateCarrier)
    (differentiable : DifferentiableAt ℝ field 0)
    (index : MatterCoordinateIndex)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => field point index) 0 direction =
      fieldDirectionalDerivative field 0 direction index := by
  have coordinateDerivative :=
    ((PiLp.hasFDerivAt_apply (p := 2)
      (E := fun _ : MatterCoordinateIndex => ℂ)
      (field 0) index).comp 0 differentiable.hasFDerivAt).fderiv
  have equality := congrArg
    (fun derivative : BasePoint →L[ℝ] ℂ =>
      derivative (coordinateDirection direction))
    coordinateDerivative
  have functionEquality :
      ((fun value : MatterCoordinateCarrier => value index) ∘ field) =
        (fun point => field point index) := by
    rfl
  rw [functionEquality] at equality
  unfold fieldDirectionalDerivative
  simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using equality

private theorem fieldDirectionalDerivative_mul_complex_at_origin
    (first second : BasePoint → ℂ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point * second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction * second 0 +
        first 0 * fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_mul firstDifferentiable secondDifferentiable]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

private theorem fieldDirectionalDerivative_re_complex_at_origin
    (field : BasePoint → ℂ)
    (differentiable : DifferentiableAt ℝ field 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => (field point).re) 0 direction =
      (fieldDirectionalDerivative field 0 direction).re := by
  have composed :=
    Complex.reCLM.hasFDerivAt.comp 0 differentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point => (field point).re) = Complex.reCLM ∘ field by rfl,
    composed.fderiv]
  rfl

private theorem fieldDirectionalDerivative_finset_sum_real_at_origin
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldSmooth : ∀ index, ContDiff ℝ ∞ (field index))
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      ((fieldSmooth index).differentiable (by simp)).differentiableAt
        |>.hasFDerivAt
  have sumDerivativePointwise :
      HasFDerivAt
        (fun point => ∑ index, field index point)
        (∑ index, fderiv ℝ (field index) 0) 0 := by
    convert sumDerivative using 1
    funext point
    simp
  unfold fieldDirectionalDerivative
  rw [sumDerivativePointwise.fderiv]
  simp

/-! ## Same-actual Lorentz coefficient and derivative -/

private theorem canonicalTemporalSingle_eq_einsteinCartanDirection
    (internalPair : Fin 6) :
    canonicalLorentzTemporalBivectorOneForm
        (EuclideanSpace.single internalPair (1 : ℝ)) =
      einsteinCartanLorentzCoordinateDirection
        canonicalLorentzianTimeDirection internalPair := by
  funext formDirection candidatePair
  fin_cases formDirection <;>
    simp [canonicalLorentzTemporalBivectorOneForm,
      einsteinCartanLorentzCoordinateDirection,
      canonicalLorentzianTimeDirection]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_normalForm
    (internalPair : Fin 6) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource JudgedActual
        (canonicalLorentzTemporalBivectorOneForm
          (EuclideanSpace.single internalPair (1 : ℝ))) =
      fun point =>
        (JudgedActual.conjugateMatter point
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (JudgedActual.matter point))).re := by
  rw [canonicalTemporalSingle_eq_einsteinCartanDirection]
  funext point
  unfold lorentzMatterSpinSourceCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterLorentzConnectionVariation
  simp only [toContinuumPointField]
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_coframe_one point]
  simp only [Matrix.det_one, abs_one, one_mul,
    matterDualFrameRelative_zeroChart]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp only [inverseCoframeDiracGamma_identity]
  simp [positiveP506MatterCurrentTemporalSpinActionVector,
    einsteinCartanLorentzCoordinateDirection,
    matterDerivativeFrameRelative_zeroChart,
    Fin.sum_univ_four]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_coordinateExpansion
    (internalPair : Fin 6) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource JudgedActual
        (canonicalLorentzTemporalBivectorOneForm
          (EuclideanSpace.single internalPair (1 : ℝ))) =
      fun point =>
        ∑ index : MatterCoordinateIndex,
          (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
                internalPair point index *
            JudgedActual.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))).re := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_normalForm]
  funext point
  have vectorFidelity :
      matterCoordinateEquiv.symm
          (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
            internalPair point) =
        positiveP506MatterCurrentTemporalSpinActionVector internalPair
          (JudgedActual.matter point) := by
    simp only [
      positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector,
      positiveP506MatterCurrentTemporalSpinCoordinateLinear_apply,
      LinearEquiv.symm_apply_apply]
  rw [← vectorFidelity, matterDual_coordinate_expansion]
  simp only [Complex.re_sum]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_directionalDerivative_coordinateExpansion
    (internalPair : Fin 6)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          JudgedActual
          (canonicalLorentzTemporalBivectorOneForm
            (EuclideanSpace.single internalPair (1 : ℝ))))
        0 derivativeDirection =
      ∑ index : MatterCoordinateIndex,
        ((positiveP506MatterCurrentTemporalSpinCoordinateLinear internalPair
              (actionGeneratedMatterLocalJetCoordinate
                positiveP506MatterCurrentFullSynchronizedMatterCauchyState
                0 derivativeDirection)) index *
            JudgedActual.conjugateMatter 0
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))) +
          positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
              internalPair 0 index *
            actionGeneratedConjugateMatterLocalJet
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0 derivativeDirection
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))).re := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_coordinateExpansion]
  let vectorCoordinate : MatterCoordinateIndex → BasePoint → ℂ :=
    fun index point =>
      positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
        internalPair point index
  let dualCoordinate : MatterCoordinateIndex → BasePoint → ℂ :=
    fun index point =>
      JudgedActual.conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))
  have vectorCoordinateSmooth (index : MatterCoordinateIndex) :
      ContDiff ℝ ∞ (vectorCoordinate index) := by
    exact
      ((contDiff_piLp 2).mp
        (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector_contDiff
          internalPair)) index
  have dualCoordinateSmooth (index : MatterCoordinateIndex) :
      ContDiff ℝ ∞ (dualCoordinate index) := by
    exact
      positiveP506MatterCurrentFullSynchronizedConjugateMatterCoordinate_contDiff
        index
  have summandSmooth (index : MatterCoordinateIndex) :
      ContDiff ℝ ∞ fun point =>
        (vectorCoordinate index point * dualCoordinate index point).re := by
    exact Complex.reCLM.contDiff.comp
      ((vectorCoordinateSmooth index).mul (dualCoordinateSmooth index))
  change
    fieldDirectionalDerivative
        (fun point =>
          ∑ index : MatterCoordinateIndex,
            (vectorCoordinate index point * dualCoordinate index point).re)
        0 derivativeDirection =
      _
  rw [fieldDirectionalDerivative_finset_sum_real_at_origin
    (fun index point =>
      (vectorCoordinate index point * dualCoordinate index point).re)
    summandSmooth derivativeDirection]
  apply Finset.sum_congr rfl
  intro index _
  rw [fieldDirectionalDerivative_re_complex_at_origin
    (fun point =>
      vectorCoordinate index point * dualCoordinate index point)
    (((vectorCoordinateSmooth index).mul (dualCoordinateSmooth index)
      ).differentiable (by simp)).differentiableAt
    derivativeDirection]
  rw [fieldDirectionalDerivative_mul_complex_at_origin
    (vectorCoordinate index) (dualCoordinate index)
    ((vectorCoordinateSmooth index).differentiable
      (by simp)).differentiableAt
    ((dualCoordinateSmooth index).differentiable
      (by simp)).differentiableAt
    derivativeDirection]
  dsimp only [vectorCoordinate, dualCoordinate]
  rw [
    fieldDirectionalDerivative_matterCoordinate_apply_at_origin
      (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
        internalPair)
      ((positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector_contDiff
        internalPair).differentiable (by simp)).differentiableAt
      index derivativeDirection,
    positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector_directionalDerivative,
    positiveP506MatterCurrentFullSynchronizedConjugateMatterCoordinate_directionalDerivative]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_directionalDerivative
    (internalPair : Fin 6)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          JudgedActual
          (canonicalLorentzTemporalBivectorOneForm
            (EuclideanSpace.single internalPair (1 : ℝ))))
        0 derivativeDirection =
      (JudgedActual.conjugateMatter 0
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (matterCoordinateEquiv.symm
              (actionGeneratedMatterLocalJetCoordinate
                positiveP506MatterCurrentFullSynchronizedMatterCauchyState
                0 derivativeDirection))) +
        actionGeneratedConjugateMatterLocalJet
          positiveP506MatterCurrentFullSynchronizedMatterCauchyState
          0 derivativeDirection
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (JudgedActual.matter 0))).re := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_directionalDerivative_coordinateExpansion
      internalPair derivativeDirection]
  have primalFidelity :
      matterCoordinateEquiv.symm
          (positiveP506MatterCurrentTemporalSpinCoordinateLinear internalPair
            (actionGeneratedMatterLocalJetCoordinate
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0 derivativeDirection)) =
        positiveP506MatterCurrentTemporalSpinActionVector internalPair
          (matterCoordinateEquiv.symm
            (actionGeneratedMatterLocalJetCoordinate
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0 derivativeDirection)) := by
    simp only [
      positiveP506MatterCurrentTemporalSpinCoordinateLinear_apply,
      LinearEquiv.symm_apply_apply]
  have originFidelity :
      matterCoordinateEquiv.symm
          (positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector
            internalPair 0) =
        positiveP506MatterCurrentTemporalSpinActionVector internalPair
          (JudgedActual.matter 0) := by
    simp only [
      positiveP506MatterCurrentFullSynchronizedTemporalSpinCoordinateVector,
      positiveP506MatterCurrentTemporalSpinCoordinateLinear_apply,
      LinearEquiv.symm_apply_apply]
  rw [← primalFidelity, ← originFidelity,
    matterDual_coordinate_expansion,
    matterDual_coordinate_expansion]
  simp only [Complex.add_re, Complex.re_sum, Finset.sum_add_distrib]

/-! ## All-coordinate same-actual decision -/

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm_basis
    (internalPair : Fin 6) :
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
        (EuclideanSpace.single internalPair (1 : ℝ)) =
      ((actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0)
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (positiveP506MatterCurrentFullSynchronizedMatterCauchyState.matter
              0)) +
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState.conjugateMatter
          0
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0))).re := by
  unfold
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
    lorentzTemporalGaussMatterSpinTangencyTerm
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinCoefficient_basis_directionalDerivative]
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_matter_origin,
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_origin]
  rw [
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_origin]
  simp only [actionGeneratedMatterLocalJetCoordinate,
    actionGeneratedConjugateMatterLocalJet,
    canonicalLorentzianTimeDirection, Matrix.cons_val,
    LinearEquiv.symm_apply_apply]
  rw [add_comm]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm_basis_eq_zero
    (internalPair : Fin 6) :
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
        (EuclideanSpace.single internalPair (1 : ℝ)) =
      0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm_basis,
    positiveP506MatterCurrentFullSynchronizedMatterSpinTimeReadout_eq_zero]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm_two_eq_zero :
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
        (EuclideanSpace.single (2 : Fin 6) (1 : ℝ)) =
      0 := by
  exact
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm_basis_eq_zero
      2

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterSpinTangency
