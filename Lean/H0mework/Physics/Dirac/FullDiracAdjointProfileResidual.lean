import H0mework.Physics.Dirac.FullDiracAdjointCoupledTemporalResidual

/-!
# Source-profile full Dirac-adjoint residual

The coupled temporal residual is the canonical-time primitive of one exact
source-profile mismatch.  The retained Carry derivative contributes zero
because Carry is already one full Dirac material.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointProfileResidual

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineEnrichedProofFreeSource
open StageNineFullDiracAdjointCoupledTemporalResidual
open StageNineFullDiracAdjointMaterial
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped Interval

noncomputable section

local instance (priority := high) profileResidualBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance (priority := high) profileResidualBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Profiles (point : BasePoint) : CompleteJointGeneratedProfiles :=
  sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry point

/-- Canonical full adjoint transported to the faithful finite coordinate
carrier used by the temporal writer. -/
def fullCanonicalDiracAdjointCoordinate
    (coordinates : MatterCoordinateCarrier) : MatterCoordinateCarrier :=
  matterDualCoordinates
    (fullCanonicalDiracAdjoint (matterCoordinateEquiv.symm coordinates))

/-- Complex antilinearity becomes real linearity on finite coordinates. -/
def fullCanonicalDiracAdjointCoordinateRealLinear :
    MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun := fullCanonicalDiracAdjointCoordinate
  map_add' first second := by
    simp [fullCanonicalDiracAdjointCoordinate, map_add,
      fullCanonicalDiracAdjoint_add, matterDualCoordinates_add]
  map_smul' scalar coordinates := by
    unfold fullCanonicalDiracAdjointCoordinate
    have mapReal :=
      (matterCoordinateEquiv.symm.toLinearMap.restrictScalars ℝ).map_smul
        scalar coordinates
    change matterCoordinateEquiv.symm (scalar • coordinates) =
      scalar • matterCoordinateEquiv.symm coordinates at mapReal
    rw [mapReal]
    change matterDualCoordinates
      (fullCanonicalDiracAdjoint ((scalar : ℂ) •
        matterCoordinateEquiv.symm coordinates)) = _
    rw [fullCanonicalDiracAdjoint_smul, matterDualCoordinates_smul]
    simp

def fullCanonicalDiracAdjointCoordinateRealCLM :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ⟨fullCanonicalDiracAdjointCoordinateRealLinear,
    fullCanonicalDiracAdjointCoordinateRealLinear.continuous_of_finiteDimensional⟩

@[simp] theorem fullCanonicalDiracAdjointCoordinateRealCLM_apply
    (coordinates : MatterCoordinateCarrier) :
    fullCanonicalDiracAdjointCoordinateRealCLM coordinates =
      fullCanonicalDiracAdjointCoordinate coordinates :=
  rfl

/-- Coordinate reconstruction returns the original canonical dual. -/
theorem matterDualOfCoordinates_fullCanonicalCoordinate
    (coordinates : MatterCoordinateCarrier) :
    matterDualOfCoordinates
        (fullCanonicalDiracAdjointCoordinate coordinates) =
      fullCanonicalDiracAdjoint
        (matterCoordinateEquiv.symm coordinates) := by
  exact matterDualOfCoordinates_surjective _

/-- Canonical adjoint coordinates commute with an interval-integrable real
Bochner integral. -/
theorem fullCanonicalDiracAdjointCoordinate_intervalIntegral
    (profile : ℝ → MatterCoordinateCarrier)
    {initial terminal : ℝ}
    (integrable : IntervalIntegrable profile volume initial terminal) :
    fullCanonicalDiracAdjointCoordinate
        (∫ time in initial..terminal, profile time) =
      ∫ time in initial..terminal,
        fullCanonicalDiracAdjointCoordinate (profile time) := by
  exact
    (fullCanonicalDiracAdjointCoordinateRealCLM.intervalIntegral_comp_comm
      integrable).symm

/-- Formal-adjoint mismatch of the source-generated target velocity. -/
def profileVelocityFormalAdjointResidual
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterDualCoordinates (Profiles point).adjointVelocity -
    fullCanonicalDiracAdjointCoordinate
      (matterCoordinateEquiv (Profiles point).matterVelocity)

/-- Formal-adjoint mismatch in the retained current derivative. -/
def currentDerivativeFormalAdjointResidual
    (point : BasePoint) : MatterCoordinateCarrier :=
  fieldDirectionalDerivative
      (holonomicConjugateMatterCoordinates Carry) point
      canonicalLorentzianTimeDirection -
    fullCanonicalDiracAdjointCoordinate
      (fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
        point canonicalLorentzianTimeDirection)

/-- Pointwise correction mismatch before temporal integration. -/
def pointwiseCorrectionFormalAdjointResidual
    (point : BasePoint) : MatterCoordinateCarrier :=
  completeJointAdjointTemporalCoordinateCorrection Source Carry point -
    fullCanonicalDiracAdjointCoordinate
      (completeJointMatterTemporalCoordinateCorrection Source Carry point)

/-- The correction contains exactly the generated-profile mismatch minus the
retained-current mismatch. -/
theorem pointwiseCorrectionFormalAdjointResidual_eq_profile_sub_current
    (point : BasePoint) :
    pointwiseCorrectionFormalAdjointResidual point =
      profileVelocityFormalAdjointResidual point -
        currentDerivativeFormalAdjointResidual point := by
  unfold pointwiseCorrectionFormalAdjointResidual
    profileVelocityFormalAdjointResidual
    currentDerivativeFormalAdjointResidual
    completeJointAdjointTemporalCoordinateCorrection
    completeJointMatterTemporalCoordinateCorrection
  have mapSub :
      fullCanonicalDiracAdjointCoordinate
          (matterCoordinateEquiv (Profiles point).matterVelocity -
            fieldDirectionalDerivative
              (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
              point canonicalLorentzianTimeDirection) =
        fullCanonicalDiracAdjointCoordinate
            (matterCoordinateEquiv (Profiles point).matterVelocity) -
          fullCanonicalDiracAdjointCoordinate
            (fieldDirectionalDerivative
              (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
              point canonicalLorentzianTimeDirection) :=
    fullCanonicalDiracAdjointCoordinateRealLinear.map_sub _ _
  rw [mapSub]
  abel

private theorem carry_coordinatePairing (point : BasePoint) :
    holonomicConjugateMatterCoordinates Carry point =
      fullCanonicalDiracAdjointCoordinate
        (matterCoordinateEquiv (Carry.matter point)) := by
  rw [← canonicalCauchySlicePoint_projections point]
  have paired := carry_fullDiracAdjointPaired
    (canonicalTimeProjection point) (canonicalSpatialProjection point)
  unfold FullDiracAdjointPaired at paired
  unfold holonomicConjugateMatterCoordinates
    fullCanonicalDiracAdjointCoordinate
  rw [paired, matterCoordinateEquiv.symm_apply_apply]

/-- Differentiating an already paired Carry creates no new residual. -/
theorem currentDerivativeFormalAdjointResidual_zero
    (point : BasePoint) :
    currentDerivativeFormalAdjointResidual point = 0 := by
  unfold currentDerivativeFormalAdjointResidual
  have functionEq :
      holonomicConjugateMatterCoordinates Carry =
        fun candidate =>
          fullCanonicalDiracAdjointCoordinate
            (matterCoordinateEquiv (Carry.matter candidate)) := by
    funext candidate
    exact carry_coordinatePairing candidate
  rw [functionEq]
  unfold fieldDirectionalDerivative
  have matterDifferentiable :
      DifferentiableAt ℝ
        (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
        point :=
    (actionSelectedCarry_matterCoordinates_contDiff.differentiable
      (by simp)).differentiableAt
  have composed :=
    fullCanonicalDiracAdjointCoordinateRealCLM.hasFDerivAt.comp point
      matterDifferentiable.hasFDerivAt
  change
    (fderiv ℝ
        (fullCanonicalDiracAdjointCoordinateRealCLM ∘
          fun candidate => matterCoordinateEquiv (Carry.matter candidate))
        point) (coordinateDirection canonicalLorentzianTimeDirection) -
      fullCanonicalDiracAdjointCoordinate
        ((fderiv ℝ
          (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
          point) (coordinateDirection canonicalLorentzianTimeDirection)) = 0
  rw [composed.fderiv, ContinuousLinearMap.comp_apply,
    fullCanonicalDiracAdjointCoordinateRealCLM_apply]
  simp

/-- The earliest pointwise source term is the generated profile-velocity
mismatch itself. -/
theorem pointwiseCorrectionFormalAdjointResidual_eq_profileVelocity
    (point : BasePoint) :
    pointwiseCorrectionFormalAdjointResidual point =
      profileVelocityFormalAdjointResidual point := by
  rw [pointwiseCorrectionFormalAdjointResidual_eq_profile_sub_current,
    currentDerivativeFormalAdjointResidual_zero, sub_zero]

private theorem carry_matterCorrection_continuous :
    Continuous
      (completeJointMatterTemporalCoordinateCorrection Source Carry) :=
  carry_matterCorrection_contDiff.continuous

private theorem carry_adjointCorrection_continuous :
    Continuous
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) :=
  carry_adjointCorrection_contDiff.continuous

private def canonicalTimeLine
    (space : StageNineSpatialPoint) : ℝ → BasePoint :=
  fun time => canonicalCauchySlicePoint time space

private theorem canonicalTimeLine_continuous
    (space : StageNineSpatialPoint) :
    Continuous (canonicalTimeLine space) := by
  unfold canonicalTimeLine
  have lineEq :
    (fun time => canonicalCauchySlicePoint time space) =
      fun time =>
        canonicalCauchySlicePoint 0 space +
          time • coordinateDirection canonicalLorentzianTimeDirection := by
    funext time
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  rw [lineEq]
  exact continuous_const.add (continuous_id.smul continuous_const)

private def matterCorrectionLine (point : BasePoint) :
    ℝ → MatterCoordinateCarrier :=
  (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
    canonicalTimeLine (canonicalSpatialProjection point)

private def adjointCorrectionLine (point : BasePoint) :
    ℝ → MatterCoordinateCarrier :=
  (completeJointAdjointTemporalCoordinateCorrection Source Carry) ∘
    canonicalTimeLine (canonicalSpatialProjection point)

private theorem matterCorrectionLine_intervalIntegrable (point : BasePoint) :
    IntervalIntegrable (matterCorrectionLine point) volume 0
      (canonicalTimeProjection point) := by
  exact (carry_matterCorrection_continuous.comp
    (canonicalTimeLine_continuous (canonicalSpatialProjection point))
    ).intervalIntegrable (0 : ℝ) (canonicalTimeProjection point)

private theorem adjointCorrectionLine_intervalIntegrable (point : BasePoint) :
    IntervalIntegrable (adjointCorrectionLine point) volume 0
      (canonicalTimeProjection point) := by
  exact (carry_adjointCorrection_continuous.comp
    (canonicalTimeLine_continuous (canonicalSpatialProjection point))
    ).intervalIntegrable (0 : ℝ) (canonicalTimeProjection point)

private theorem fullCanonicalMatterCorrectionLine_intervalIntegrable
    (point : BasePoint) :
    IntervalIntegrable
      (fun time => fullCanonicalDiracAdjointCoordinate
        (matterCorrectionLine point time)) volume 0
      (canonicalTimeProjection point) := by
  apply Continuous.intervalIntegrable
  exact fullCanonicalDiracAdjointCoordinateRealCLM.continuous.comp
    (carry_matterCorrection_continuous.comp
      (canonicalTimeLine_continuous (canonicalSpatialProjection point)))

private theorem matterDualOfCoordinates_sub
    (first second : MatterCoordinateCarrier) :
    matterDualOfCoordinates (first - second) =
      matterDualOfCoordinates first - matterDualOfCoordinates second := by
  apply matterDualCoordinates_injective
  simp [matterDualCoordinates_sub]

/-- The coupled residual is exactly the canonical-time primitive of the
source-generated profile-velocity mismatch. -/
theorem coupledTemporalSourceOperatorResidual_eq_profileVelocityPrimitive
    (point : BasePoint) :
    coupledTemporalSourceOperatorResidual point =
      matterDualOfCoordinates
        (canonicalTimePrimitive profileVelocityFormalAdjointResidual point) := by
  unfold coupledTemporalSourceOperatorResidual
    coupledTemporalMatterCorrection coupledTemporalAdjointCorrection
    fullDiracAdjointResidual
  rw [← matterDualOfCoordinates_fullCanonicalCoordinate,
    ← matterDualOfCoordinates_sub]
  apply congrArg matterDualOfCoordinates
  have matterIntegrable : IntervalIntegrable
      (fun time => completeJointMatterTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time
          (canonicalSpatialProjection point))) volume 0
      (canonicalTimeProjection point) := by
    simpa [matterCorrectionLine, canonicalTimeLine, Function.comp_def] using
      matterCorrectionLine_intervalIntegrable point
  have adjointIntegrable : IntervalIntegrable
      (fun time => completeJointAdjointTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time
          (canonicalSpatialProjection point))) volume 0
      (canonicalTimeProjection point) := by
    simpa [adjointCorrectionLine, canonicalTimeLine, Function.comp_def] using
      adjointCorrectionLine_intervalIntegrable point
  have canonicalIntegrable : IntervalIntegrable
      (fun time => fullCanonicalDiracAdjointCoordinate
        (completeJointMatterTemporalCoordinateCorrection Source Carry
          (canonicalCauchySlicePoint time
            (canonicalSpatialProjection point)))) volume 0
      (canonicalTimeProjection point) := by
    simpa [matterCorrectionLine, canonicalTimeLine, Function.comp_def] using
      fullCanonicalMatterCorrectionLine_intervalIntegrable point
  unfold canonicalTimePrimitive
  rw [fullCanonicalDiracAdjointCoordinate_intervalIntegral _
      matterIntegrable,
    ← intervalIntegral.integral_sub
      adjointIntegrable canonicalIntegrable]
  apply intervalIntegral.integral_congr
  intro time _
  exact pointwiseCorrectionFormalAdjointResidual_eq_profileVelocity _

private theorem matterDualOfCoordinates_eq_zero_iff
    (coordinates : MatterCoordinateCarrier) :
    matterDualOfCoordinates coordinates = 0 ↔ coordinates = 0 := by
  constructor
  · intro zero
    have coordinateZero := congrArg matterDualCoordinates zero
    simpa using coordinateZero
  · rintro rfl
    exact matterDualOfCoordinates_zero

/-- Final exact criterion: only the integrated source-profile velocity
mismatch can obstruct the full material law. -/
theorem coupledTemporalSourceOperatorResidual_eq_zero_iff_profileVelocityPrimitive
    (point : BasePoint) :
    coupledTemporalSourceOperatorResidual point = 0 ↔
      canonicalTimePrimitive profileVelocityFormalAdjointResidual point = 0 := by
  rw [coupledTemporalSourceOperatorResidual_eq_profileVelocityPrimitive,
    matterDualOfCoordinates_eq_zero_iff]

end
end StageNineFullDiracAdjointProfileResidual
end SaturationMonoid.PhysicsCore
