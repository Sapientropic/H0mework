import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal

/-!
# Parameter regularity of the coframe matter Euler read

The repaired scalar--matter coframe density reads exactly five finite
coordinate families: the scalar, its covariant first jet, the primal matter,
its covariant first jet, and the independent dual coordinates.  This module
keeps that inventory explicit and proves both continuity and `C¹` regularity
of the coframe Euler coordinate from the corresponding regularity of those
generated parameters and the live coframe.

This is a readout theorem.  It accepts no Euler value, residual, target,
branch, completed field, or stationarity certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- Exact finite parameter inventory read by the matter coframe density. -/
abbrev CoframeMatterActionParameter :=
  ScalarCoordinateCarrier ×
    (LorentzianIndex → ScalarCoordinateCarrier) ×
      MatterCoordinateCarrier ×
        (LorentzianIndex → MatterCoordinateCarrier) ×
          MatterCoordinateCarrier

def coframeMatterActionParameterOfField
    (field : StageNineContinuumPointField) :
    CoframeMatterActionParameter :=
  (field.scalar,
    fun direction => field.scalarCovariantDerivative direction,
    matterCoordinateEquiv field.matter,
    fun direction => matterCoordinateEquiv
      (field.matterCovariantDerivative direction),
    matterDualCoordinates field.conjugateMatter)

@[simp] theorem
    coframeMatterActionParameterOfField_restrictContinuumPointFieldToIIPlus
    (field : StageNineContinuumPointField) :
    coframeMatterActionParameterOfField
        (StageNineIIPlusRestriction.restrictContinuumPointFieldToIIPlus field) =
      coframeMatterActionParameterOfField field :=
  rfl

/-- Reconstruct only the five action-visible fields from their coordinates.
All other point-field slots are definitionally absent from this sector. -/
def coframeMatterActionPointField
    (parameter : CoframeMatterActionParameter)
    (coframe : LorentzianCoframe) : StageNineContinuumPointField where
  coframe := coframe
  gravityCurvature := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeCurvature := 0
  gaugeAuxiliary := 0
  scalar := parameter.1
  scalarCovariantDerivative := parameter.2.1
  matter := matterCoordinateEquiv.symm parameter.2.2.1
  matterCovariantDerivative := fun direction =>
    matterCoordinateEquiv.symm (parameter.2.2.2.1 direction)
  conjugateMatter := matterDualOfCoordinates parameter.2.2.2.2

/-- Coordinate normal form of the repaired matter density with its coframe
argument kept live. -/
def coframeMatterActionCoordinateDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (parameter : CoframeMatterActionParameter)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedDiracDualFormNativeMatterDensity source 0 point
    (coframeMatterActionPointField parameter coframe)

theorem diracDualFormNativeCoframeMatterDensity_eq_coordinateDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point field =
      coframeMatterActionCoordinateDensity source point
        (coframeMatterActionParameterOfField field) := by
  funext candidate
  unfold diracDualFormNativeCoframeMatterDensity
    coframeMatterActionCoordinateDensity
    coframeMatterActionParameterOfField
    coframeMatterActionPointField
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
  simp only [withCoframe, scalarFrameRelativeCoordinates_zeroChart_local,
    matterFrameRelative_zeroChart_local,
    matterDualFrameRelative_zeroChart_local,
    matterCoordinateEquiv.symm_apply_apply,
    matterDualOfCoordinates_surjective]

/-- Joint smoothness of the finite matter-parameter/coframe density on the
nondegenerate coframe locus. -/
theorem coframeMatterActionCoordinateDensity_joint_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (center : CoframeMatterActionParameter × LorentzianCoframe)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (Function.uncurry (coframeMatterActionCoordinateDensity source point))
      center := by
  let volume := fun joint :
      CoframeMatterActionParameter × LorentzianCoframe =>
    abs (Matrix.det joint.2)
  let scalarCoefficient := fun joint :
      CoframeMatterActionParameter × LorentzianCoframe =>
    (1 / 2 : ℝ) *
        ∑ first : LorentzianIndex,
          ∑ second : LorentzianIndex,
            ((lorentzianMetricOfCoframe joint.2)⁻¹ first second) *
              scalarCoordinatePairingRe
                (joint.1.2.1 first) (joint.1.2.1 second) -
      scalarCoordinateSquaredNorm
        (joint.1.1 - sourceGeneratedVacuumCoordinates source)
  let kineticCoefficient := fun joint :
      CoframeMatterActionParameter × LorentzianCoframe =>
    ((matterDualOfCoordinates joint.1.2.2.2.2)
      ((Complex.I : ℂ) •
        ∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.2, derivative := 0 } direction)
            (matterCoordinateEquiv.symm
              (joint.1.2.2.2.1 direction)))).re
  let yukawaCoefficient := fun joint :
      CoframeMatterActionParameter × LorentzianCoframe =>
    ((matterDualOfCoordinates joint.1.2.2.2.2)
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm joint.1.1)
        (matterCoordinateEquiv.symm joint.1.2.2.1))).re
  have volumeRegular : ContDiffAt ℝ ∞ volume center :=
    ((coframe_volume_contDiffAt center.2 nondegenerate).comp center
      contDiffAt_snd).of_le (by norm_num)
  have scalarRegular : ContDiffAt ℝ ∞ scalarCoefficient center := by
    dsimp only [scalarCoefficient]
    have metricInverseRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (lorentzianMetricOfCoframe joint.2)⁻¹) center :=
      ((lorentzianMetric_inv_contDiffAt center.2 nondegenerate).comp center
        contDiffAt_snd).of_le (by norm_num)
    have scalarPairingRegular (first second : LorentzianIndex) :
        ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            scalarCoordinatePairingRe
              (joint.1.2.1 first) (joint.1.2.1 second)) center := by
      unfold scalarCoordinatePairingRe
      apply ContDiffAt.sum
      intro index _
      let projection : ScalarCoordinateCarrier →L[ℝ] ℂ :=
        (PiLp.projₗ (𝕜 := ℂ) 2
          (fun _ : ScalarBasisIndex => ℂ) index)
          |>.toContinuousLinearMap |>.restrictScalars ℝ
      have firstRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            joint.1.2.1 first index) center := by
        change ContDiffAt ℝ ∞
          (fun joint => projection (joint.1.2.1 first)) center
        fun_prop
      have secondRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            joint.1.2.1 second index) center := by
        change ContDiffAt ℝ ∞
          (fun joint => projection (joint.1.2.1 second)) center
        fun_prop
      have conjugateRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            star (joint.1.2.1 first index)) center := by
        change ContDiffAt ℝ ∞
          (fun joint => Complex.conjCLE (joint.1.2.1 first index)) center
        exact
          Complex.conjCLE.contDiff.contDiffAt.comp center firstRegular
      exact
        Complex.reCLM.contDiff.contDiffAt.comp center
          (conjugateRegular.mul secondRegular)
    have kineticRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (1 / 2 : ℝ) *
            ∑ first : LorentzianIndex,
              ∑ second : LorentzianIndex,
                ((lorentzianMetricOfCoframe joint.2)⁻¹ first second) *
                  scalarCoordinatePairingRe
                    (joint.1.2.1 first) (joint.1.2.1 second)) center := by
      apply ContDiffAt.mul contDiffAt_const
      apply ContDiffAt.sum
      intro first _
      apply ContDiffAt.sum
      intro second _
      exact
        (contDiffAt_pi.mp
          (contDiffAt_pi.mp metricInverseRegular first) second).mul
          (scalarPairingRegular first second)
    have potentialRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          scalarCoordinateSquaredNorm
            (joint.1.1 - sourceGeneratedVacuumCoordinates source)) center := by
      unfold scalarCoordinateSquaredNorm
      apply ContDiffAt.sum
      intro index _
      let projection : ScalarCoordinateCarrier →L[ℝ] ℂ :=
        (PiLp.projₗ (𝕜 := ℂ) 2
          (fun _ : ScalarBasisIndex => ℂ) index)
          |>.toContinuousLinearMap |>.restrictScalars ℝ
      have coordinateRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            (joint.1.1 - sourceGeneratedVacuumCoordinates source) index)
          center := by
        change ContDiffAt ℝ ∞
          (fun joint => projection
            (joint.1.1 - sourceGeneratedVacuumCoordinates source)) center
        fun_prop
      have realRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            ((joint.1.1 - sourceGeneratedVacuumCoordinates source) index).re)
          center :=
        Complex.reCLM.contDiff.contDiffAt.comp center
          coordinateRegular
      have imaginaryRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            ((joint.1.1 - sourceGeneratedVacuumCoordinates source) index).im)
          center :=
        Complex.imCLM.contDiff.contDiffAt.comp center
          coordinateRegular
      simpa only [Complex.normSq_apply] using
        (realRegular.mul realRegular).add
          (imaginaryRegular.mul imaginaryRegular)
    exact kineticRegular.sub potentialRegular
  have kineticRegular : ContDiffAt ℝ ∞ kineticCoefficient center := by
    dsimp only [kineticCoefficient]
    have gammaRegular : ∀ direction : LorentzianIndex,
        ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            inverseCoframeDiracGamma
              { coframe := joint.2, derivative := 0 } direction) center := by
      intro direction
      exact
        ((inverseCoframeDiracGamma_contDiffAt center.2 nondegenerate direction
          ).comp center contDiffAt_snd).of_le (by norm_num)
    have directionRegular : ∀ direction : LorentzianIndex,
        ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := joint.2, derivative := 0 } direction)
                (matterCoordinateEquiv.symm
                  (joint.1.2.2.2.1 direction)))) center := by
      intro direction
      have derivativeRegular : ContDiffAt ℝ ∞
          (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
            joint.1.2.2.2.1 direction) center := by
        fun_prop
      have actual :=
        ((diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
          |>.contDiff.contDiffAt).comp center
              (gammaRegular direction)).clm_apply derivativeRegular
      change ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } direction)
              (matterCoordinateEquiv.symm
                (joint.1.2.2.2.1 direction)))) center at actual
      exact actual
    have vectorRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          matterCoordinateEquiv
            ((Complex.I : ℂ) •
              ∑ direction : LorentzianIndex,
                diracMatrixMatterAction
                  (inverseCoframeDiracGamma
                    { coframe := joint.2, derivative := 0 } direction)
                  (matterCoordinateEquiv.symm
                    (joint.1.2.2.2.1 direction)))) center := by
      simp only [map_smul, map_sum]
      exact
        (contDiffAt_const : ContDiffAt ℝ ∞
          (fun _ : CoframeMatterActionParameter × LorentzianCoframe =>
            (Complex.I : ℂ)) center).smul
          (ContDiffAt.sum fun direction _ => directionRegular direction)
    have complexRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (matterDualOfCoordinates joint.1.2.2.2.2)
            ((Complex.I : ℂ) •
              ∑ direction : LorentzianIndex,
                diracMatrixMatterAction
                  (inverseCoframeDiracGamma
                    { coframe := joint.2, derivative := 0 } direction)
                  (matterCoordinateEquiv.symm
                    (joint.1.2.2.2.1 direction)))) center := by
      rw [show
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (matterDualOfCoordinates joint.1.2.2.2.2)
            ((Complex.I : ℂ) •
              ∑ direction : LorentzianIndex,
                diracMatrixMatterAction
                  (inverseCoframeDiracGamma
                    { coframe := joint.2, derivative := 0 } direction)
                  (matterCoordinateEquiv.symm
                    (joint.1.2.2.2.1 direction)))) =
          fun joint =>
            ∑ index : MatterCoordinateIndex,
              matterCoordinateEquiv
                  ((Complex.I : ℂ) •
                    ∑ direction : LorentzianIndex,
                      diracMatrixMatterAction
                        (inverseCoframeDiracGamma
                          { coframe := joint.2, derivative := 0 } direction)
                        (matterCoordinateEquiv.symm
                          (joint.1.2.2.2.1 direction))) index *
                joint.1.2.2.2.2 index by
        funext joint
        exact matterDualOfCoordinates_apply _ _]
      apply ContDiffAt.sum
      intro index _
      exact
        ((contDiffAt_piLp 2).mp vectorRegular index).mul (by fun_prop)
    exact
      Complex.reCLM.contDiff.contDiffAt.comp center
        complexRegular
  have yukawaRegular : ContDiffAt ℝ ∞ yukawaCoefficient center := by
    dsimp only [yukawaCoefficient]
    have vectorRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm joint.1.1)
              (matterCoordinateEquiv.symm joint.1.2.2.1))) center := by
      exact
        ((diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap
          |>.contDiff.contDiffAt).comp center
              (by fun_prop)).clm_apply (by fun_prop)
    have complexRegular : ContDiffAt ℝ ∞
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (matterDualOfCoordinates joint.1.2.2.2.2)
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm joint.1.1)
              (matterCoordinateEquiv.symm joint.1.2.2.1))) center := by
      rw [show
        (fun joint : CoframeMatterActionParameter × LorentzianCoframe =>
          (matterDualOfCoordinates joint.1.2.2.2.2)
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm joint.1.1)
              (matterCoordinateEquiv.symm joint.1.2.2.1))) =
          fun joint =>
            ∑ index : MatterCoordinateIndex,
              matterCoordinateEquiv
                  (diracDualRightChiralYukawaAction
                    (scalarCoordinateEquiv.symm joint.1.1)
                    (matterCoordinateEquiv.symm joint.1.2.2.1)) index *
                joint.1.2.2.2.2 index by
        funext joint
        exact matterDualOfCoordinates_apply _ _]
      apply ContDiffAt.sum
      intro index _
      exact
        ((contDiffAt_piLp 2).mp vectorRegular index).mul (by fun_prop)
    exact
      Complex.reCLM.contDiff.contDiffAt.comp center
        complexRegular
  unfold Function.uncurry coframeMatterActionCoordinateDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity
    scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
    coframeMatterActionPointField
  simp only [scalarFrameRelativeCoordinates_zeroChart_local,
    matterFrameRelative_zeroChart_local,
    matterDualFrameRelative_zeroChart_local]
  change ContDiffAt ℝ ∞
    (fun joint =>
      volume joint * scalarCoefficient joint +
        (volume joint * kineticCoefficient joint +
          volume joint * yukawaCoefficient joint)) center
  exact (volumeRegular.mul scalarRegular).add
    ((volumeRegular.mul kineticRegular).add
      (volumeRegular.mul yukawaRegular))

theorem diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterEulerCovector source point field variation =
      fderiv ℝ
          (coframeMatterActionCoordinateDensity source point
            (coframeMatterActionParameterOfField field))
          field.coframe variation := by
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [diracDualFormNativeCoframeMatterDensity_eq_coordinateDensity]

/-- In the canonical zero chart the coframe matter density has no explicit
spacetime-point dependence.  All local dependence is carried by the actual
point-field parameter. -/
theorem diracDualFormNativeCoframeMatterDensity_point_independent
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point field =
      diracDualFormNativeCoframeMatterDensity source 0 field := by
  funext candidate
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
  simp

/-- Point-independence transported to the generated coframe Euler covector. -/
theorem diracDualFormNativeCoframeMatterEulerCovector_point_independent
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterEulerCovector source point field =
      diracDualFormNativeCoframeMatterEulerCovector source 0 field := by
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [diracDualFormNativeCoframeMatterDensity_point_independent]

/-- A smooth finite parameter/coframe family transfers any requested common
differentiability order to the generated matter Euler coordinate.  The result
is still the actual density derivative, not a supplied Euler receipt. -/
theorem diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_of_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞}
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : E → StageNineContinuumPointField) (center : E)
    (parameterRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun candidate =>
        coframeMatterActionParameterOfField (field candidate)) center)
    (coframeRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun candidate => (field candidate).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun candidate =>
        diracDualFormNativeCoframeMatterEulerCovector source point
          (field candidate) (coframeCoordinateDirection row column)) center := by
  let selected : E → CoframeMatterActionParameter × LorentzianCoframe :=
    fun candidate =>
      (coframeMatterActionParameterOfField (field candidate),
        (field candidate).coframe)
  let family :
      (CoframeMatterActionParameter × LorentzianCoframe) →
        LorentzianCoframe → ℝ :=
    fun carrier candidate =>
      coframeMatterActionCoordinateDensity source point carrier.1 candidate
  have familyJointSmooth : ContDiffAt ℝ ∞ (Function.uncurry family)
      (selected center, (field center).coframe) := by
    have base :=
      coframeMatterActionCoordinateDensity_joint_contDiffAt source point
        (coframeMatterActionParameterOfField (field center),
          (field center).coframe) nondegenerate
    have projectionRegular : ContDiffAt ℝ ∞
        (fun joint :
            (CoframeMatterActionParameter × LorentzianCoframe) ×
              LorentzianCoframe => (joint.1.1, joint.2))
        (selected center, (field center).coframe) := by
      fun_prop
    exact base.comp
      (selected center, (field center).coframe) projectionRegular
  have outerRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun carrier : CoframeMatterActionParameter × LorentzianCoframe =>
        fderiv ℝ (family carrier) carrier.2
          (coframeCoordinateDirection row column))
      (selected center) := by
    have familyJointNext : ContDiffAt ℝ
        ((n + 1 : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry family)
        (selected center, (field center).coframe) :=
      familyJointSmooth.of_le
        (show ((n + 1 : ℕ∞) : WithTop ℕ∞) ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)
    exact
      (ContDiffAt.fderiv (m := (n : WithTop ℕ∞))
        (by simpa using familyJointNext) (by fun_prop)
        (by simp)).clm_apply contDiffAt_const
  have selectedRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      selected center :=
    parameterRegular.prodMk coframeRegular
  rw [show
    (fun candidate =>
      diracDualFormNativeCoframeMatterEulerCovector source point
        (field candidate) (coframeCoordinateDirection row column)) =
      ((fun carrier : CoframeMatterActionParameter × LorentzianCoframe =>
        fderiv ℝ (family carrier) carrier.2
          (coframeCoordinateDirection row column)) ∘ selected) by
    funext candidate
    rw [diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv]
    rfl]
  exact outerRegular.comp center selectedRegular

theorem diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : E → StageNineContinuumPointField) (center : E)
    (parameterRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        coframeMatterActionParameterOfField (field candidate)) center)
    (coframeRegular : ContDiffAt ℝ ∞
      (fun candidate => (field candidate).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        diracDualFormNativeCoframeMatterEulerCovector source point
          (field candidate) (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_of_order
    source point field center parameterRegular coframeRegular nondegenerate
      row column

/-- A continuous live five-parameter/coframe family produces a continuous
matter Euler coordinate. -/
theorem diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : E → StageNineContinuumPointField) (center : E)
    (parameterRegular : ContDiffAt ℝ 0
      (fun candidate =>
        coframeMatterActionParameterOfField (field candidate)) center)
    (coframeRegular : ContDiffAt ℝ 0
      (fun candidate => (field candidate).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun candidate =>
        diracDualFormNativeCoframeMatterEulerCovector source point
          (field candidate) (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_of_order
    source point field center parameterRegular coframeRegular nondegenerate
      row column

/-- A `C¹` live five-parameter/coframe family produces a `C¹` matter Euler
coordinate.  The derivative is generated by the smooth finite action
density; no Euler output is accepted as input. -/
theorem diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : E → StageNineContinuumPointField) (center : E)
    (parameterRegular : ContDiffAt ℝ 1
      (fun candidate =>
        coframeMatterActionParameterOfField (field candidate)) center)
    (coframeRegular : ContDiffAt ℝ 1
      (fun candidate => (field candidate).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun candidate =>
        diracDualFormNativeCoframeMatterEulerCovector source point
          (field candidate) (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_of_order
    source point field center parameterRegular coframeRegular nondegenerate
      row column

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
