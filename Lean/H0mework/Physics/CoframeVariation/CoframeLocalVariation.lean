import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.Coframe.CoframeLocalVariation

/-!
# Local coframe variation of the Dirac-dual form-native action

This module reissues the coframe derivative after the repaired Dirac-dual
Yukawa operator has opened a new root-action epoch.  The new local density is
assembled directly from the live gravity BF, holonomic constraint, gauge,
scalar, kinetic, and repaired Yukawa blocks.  It is not defined as a
difference from the historical action.

Only one analytic ingredient is new: the repaired Yukawa vector is constant
under a coframe-only replacement, while its density retains the live volume
factor.  The kinetic inverse-frame response, scalar response, gauge
constitutive response, and direct `II+` reaction keep their previously proved
formulation-neutral calculus.

The Euler covectors below are action-generated readouts of this new local
root.  No equation, stationarity receipt, fixed actual, or target covector is
accepted as input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeLocalVariation

open DiracExteriorMatterAction
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity
open DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Repaired matter regularity under a live coframe -/

/-- Coordinate smoothness of the kinetic vector alone.  This extracts the
formulation-neutral inverse-frame calculation before either Yukawa epoch is
chosen. -/
theorem generatedContinuumMatterKineticVector_withCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumMatterKineticVector source 0 point
            (withCoframe field candidate))) field.coframe := by
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := candidate, derivative := 0 } direction)
              (matterDerivativeFrameRelative source 0 point
                field.matterCovariantDerivative direction))) field.coframe := by
    intro direction
    let derivativeCoordinates : MatterCoordinateCarrier :=
      matterCoordinateEquiv
        (matterDerivativeFrameRelative source 0 point
          field.matterCovariantDerivative direction)
    let actionLinear : DiracMatrix →L[ℝ] MatterCoordinateCarrier :=
      ((LinearMap.flip coframeDiracMatrixMatterCoordinateBilinear)
        derivativeCoordinates).toContinuousLinearMap.restrictScalars ℝ
    have actionSmooth : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := candidate, derivative := 0 } direction)
              (matterCoordinateEquiv.symm derivativeCoordinates)))
        field.coframe := by
      change ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          actionLinear
            (inverseCoframeDiracGamma
              { coframe := candidate, derivative := 0 } direction))
        field.coframe
      exact actionLinear.contDiff.contDiffAt.comp field.coframe
        (inverseCoframeDiracGamma_contDiffAt field.coframe
          nondegenerate direction)
    simpa only [derivativeCoordinates,
      matterCoordinateEquiv.symm_apply_apply] using actionSmooth
  have kineticSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        Complex.I •
          ∑ direction : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := candidate, derivative := 0 } direction)
                (matterDerivativeFrameRelative source 0 point
                  field.matterCovariantDerivative direction)))
      field.coframe := by
    exact
      (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : LorentzianCoframe => (Complex.I : ℂ)) field.coframe).smul
        (ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction)
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, map_smul, map_sum]
  exact kineticSmooth

/-- The separately densitized kinetic block remains smooth in the live
coframe. -/
theorem generatedDensitizedContinuumMatterKineticDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        generatedDensitizedContinuumMatterKineticDensity source 0 point
          (withCoframe field candidate)) field.coframe := by
  let vector := fun candidate : LorentzianCoframe =>
    generatedContinuumMatterKineticVector source 0 point
      (withCoframe field candidate)
  let dual : Module.Dual ℂ DiracExteriorMatterCarrier :=
    matterDualFrameRelative source 0 point field.conjugateMatter
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        matterCoordinateEquiv (vector candidate)) field.coframe :=
    generatedContinuumMatterKineticVector_withCoframe_coordinate_contDiffAt
      source point field nondegenerate
  have pairingSumSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector candidate) index *
            dual (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) field.coframe := by
    apply ContDiffAt.sum
    intro index _
    let coordinateLinear : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index)
        |>.toContinuousLinearMap |>.restrictScalars ℝ
    have coordinateSmooth : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv (vector candidate) index) field.coframe :=
      coordinateLinear.contDiff.contDiffAt.comp field.coframe
        vectorCoordinateSmooth
    exact coordinateSmooth.mul contDiffAt_const
  have dualPairingSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe => dual (vector candidate))
      field.coframe := by
    rw [show (fun candidate : LorentzianCoframe => dual (vector candidate)) =
        fun candidate => ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector candidate) index *
            dual (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext candidate
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion dual
          (matterCoordinateEquiv (vector candidate))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        (dual (vector candidate)).re) field.coframe :=
    Complex.reCLM.contDiff.contDiffAt.comp field.coframe dualPairingSmooth
  have volumeSmooth := generatedVolumeDensity_withCoframe_contDiffAt
    field nondegenerate
  simpa only [generatedDensitizedContinuumMatterKineticDensity,
    withCoframe, vector, dual] using volumeSmooth.mul realPairingSmooth

/-- The repaired Yukawa vector is coframe-independent during a coframe-only
variation; its densitized coefficient changes only through the live volume. -/
theorem generatedDensitizedContinuumDiracDualYukawaDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        generatedDensitizedContinuumDiracDualYukawaDensity source 0 point
          (withCoframe field candidate)) field.coframe := by
  have volumeSmooth := generatedVolumeDensity_withCoframe_contDiffAt
    field nondegenerate
  have coefficientSmooth : ContDiffAt ℝ ∞
      (fun _ : LorentzianCoframe =>
        (matterDualFrameRelative source 0 point field.conjugateMatter
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (scalarFrameRelativeCoordinates source 0 point field.scalar))
            (matterFrameRelative source 0 point field.matter))).re)
      field.coframe := contDiffAt_const
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
    generatedContinuumDiracDualYukawaVector
  simpa only [withCoframe] using volumeSmooth.mul coefficientSmooth

/-- The scalar block keeps its existing kinetic and potential calculus under
the repaired action hash. -/
theorem generatedDensitizedContinuumScalarDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        generatedDensitizedContinuumScalarDensity source 0 point
          (withCoframe field candidate)) field.coframe := by
  unfold generatedDensitizedContinuumScalarDensity
  simpa only [withCoframe] using
    (generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).mul
      ((generatedScalarKineticDensity_withCoframe_contDiffAt
        source point field nondegenerate).sub contDiffAt_const)

/-- Complete repaired scalar plus Dirac-dual matter regularity. -/
theorem generatedDiracDualFormNativeMatterDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        generatedDiracDualFormNativeMatterDensity source 0 point
          (withCoframe field candidate)) field.coframe := by
  unfold generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  exact
    (generatedDensitizedContinuumScalarDensity_withCoframe_contDiffAt
      source point field nondegenerate).add
      ((generatedDensitizedContinuumMatterKineticDensity_withCoframe_contDiffAt
        source point field nondegenerate).add
        (generatedDensitizedContinuumDiracDualYukawaDensity_withCoframe_contDiffAt
          source point field nondegenerate))

/-! ## New-root local functions and Euler covectors -/

def diracDualFormNativeCoframeLocalDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
    (withCoframe field coframe)

def diracDualFormNativeCoframeCommonCoreDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    source (sourceGeneratedUnifiedCouplings source) 0 point
    (withCoframe field coframe)

def diracDualFormNativeCoframeGaugeDensity
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedFormNativeGaugeDensityAtBoundary
    (sourceGeneratedUnifiedCouplings source) (withCoframe field coframe)

def diracDualFormNativeCoframeMatterDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedDiracDualFormNativeMatterDensity source 0 point
    (withCoframe field coframe)

theorem diracDualFormNativeCoframeLocalDensity_eq_constraint_add_commonCore
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeLocalDensity source point field coframe =
      generatedFormNativeGravityConstraintDensity
          (withCoframe field coframe) +
        diracDualFormNativeCoframeCommonCoreDensity source point field
          coframe := by
  unfold diracDualFormNativeCoframeLocalDensity
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    diracDualFormNativeCoframeCommonCoreDensity
    generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
  ring

theorem diracDualFormNativeCoframeCommonCoreDensity_eq_gravity_add_gauge_add_matter
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeCommonCoreDensity source point field coframe =
      generatedFormNativeGravityBFDensity field +
        diracDualFormNativeCoframeGaugeDensity source field coframe +
        diracDualFormNativeCoframeMatterDensity source point field coframe := by
  unfold diracDualFormNativeCoframeCommonCoreDensity
    generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    diracDualFormNativeCoframeGaugeDensity
    diracDualFormNativeCoframeMatterDensity
  rfl

theorem diracDualFormNativeCoframeGaugeDensity_contDiffAt
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (diracDualFormNativeCoframeGaugeDensity source field)
      field.coframe := by
  exact generatedFormNativeGaugeDensityAtBoundary_withCoframe_contDiffAt
    (sourceGeneratedUnifiedCouplings source) field nondegenerate

theorem diracDualFormNativeCoframeMatterDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeCoframeMatterDensity source point field)
      field.coframe :=
  generatedDiracDualFormNativeMatterDensity_withCoframe_contDiffAt
    source point field nondegenerate

theorem diracDualFormNativeCoframeCommonCoreDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeCoframeCommonCoreDensity source point field)
      field.coframe := by
  rw [show diracDualFormNativeCoframeCommonCoreDensity source point field =
      fun coframe =>
        generatedFormNativeGravityBFDensity field +
          diracDualFormNativeCoframeGaugeDensity source field coframe +
          diracDualFormNativeCoframeMatterDensity source point field coframe by
    funext coframe
    exact
      diracDualFormNativeCoframeCommonCoreDensity_eq_gravity_add_gauge_add_matter
        source point field coframe]
  exact (contDiffAt_const.add
    (diracDualFormNativeCoframeGaugeDensity_contDiffAt
      source field nondegenerate)).add
    (diracDualFormNativeCoframeMatterDensity_contDiffAt
      source point field nondegenerate)

theorem diracDualFormNativeCoframeLocalDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (diracDualFormNativeCoframeLocalDensity source point field)
      field.coframe := by
  rw [show diracDualFormNativeCoframeLocalDensity source point field =
      fun coframe =>
        generatedFormNativeGravityConstraintDensity
            (withCoframe field coframe) +
          diracDualFormNativeCoframeCommonCoreDensity source point field
            coframe by
    funext coframe
    exact
      diracDualFormNativeCoframeLocalDensity_eq_constraint_add_commonCore
        source point field coframe]
  exact (generatedFormNativeGravityConstraintDensity_withCoframe_contDiffAt
    field).add (diracDualFormNativeCoframeCommonCoreDensity_contDiffAt
      source point field nondegenerate)

def diracDualFormNativeCoframeEulerCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (diracDualFormNativeCoframeLocalDensity source point field)
    field.coframe

def diracDualFormNativeCoframeCommonCoreEulerCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (diracDualFormNativeCoframeCommonCoreDensity source point field)
    field.coframe

def diracDualFormNativeCoframeGaugeEulerCovector
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (diracDualFormNativeCoframeGaugeDensity source field)
    field.coframe

def diracDualFormNativeCoframeMatterEulerCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (diracDualFormNativeCoframeMatterDensity source point field)
    field.coframe

theorem diracDualFormNativeCoframeLocalDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (diracDualFormNativeCoframeLocalDensity source point field)
      (diracDualFormNativeCoframeEulerCovector source point field)
      field.coframe :=
  ((diracDualFormNativeCoframeLocalDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem diracDualFormNativeCoframeCommonCoreDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt
      (diracDualFormNativeCoframeCommonCoreDensity source point field)
      (diracDualFormNativeCoframeCommonCoreEulerCovector source point field)
      field.coframe :=
  ((diracDualFormNativeCoframeCommonCoreDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (diracDualFormNativeCoframeGaugeDensity source field)
      (diracDualFormNativeCoframeGaugeEulerCovector source field)
      field.coframe :=
  ((diracDualFormNativeCoframeGaugeDensity_contDiffAt source field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem diracDualFormNativeCoframeMatterDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (diracDualFormNativeCoframeMatterDensity source point field)
      (diracDualFormNativeCoframeMatterEulerCovector source point field)
      field.coframe :=
  ((diracDualFormNativeCoframeMatterDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

/-- The repaired constraint-free derivative is the unchanged gauge response
plus the new-hash matter response. -/
theorem diracDualFormNativeCoframeCommonCoreEulerCovector_eq_gauge_add_matter
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    diracDualFormNativeCoframeCommonCoreEulerCovector source point field =
      diracDualFormNativeCoframeGaugeEulerCovector source field +
        diracDualFormNativeCoframeMatterEulerCovector source point field := by
  have gravityGaugeDerivative :=
    (diracDualFormNativeCoframeGaugeDensity_hasFDerivAt source field
      nondegenerate).const_add (generatedFormNativeGravityBFDensity field)
  have splitDerivative := gravityGaugeDerivative.add
    (diracDualFormNativeCoframeMatterDensity_hasFDerivAt
      source point field nondegenerate)
  have sameDerivative : HasFDerivAt
      (diracDualFormNativeCoframeCommonCoreDensity source point field)
      (diracDualFormNativeCoframeGaugeEulerCovector source field +
        diracDualFormNativeCoframeMatterEulerCovector source point field)
      field.coframe := by
    rw [show diracDualFormNativeCoframeCommonCoreDensity source point field =
      fun coframe =>
        generatedFormNativeGravityBFDensity field +
          diracDualFormNativeCoframeGaugeDensity source field coframe +
          diracDualFormNativeCoframeMatterDensity source point field coframe by
      funext coframe
      exact
        diracDualFormNativeCoframeCommonCoreDensity_eq_gravity_add_gauge_add_matter
          source point field coframe]
    change HasFDerivAt
      ((fun _ : LorentzianCoframe =>
          generatedFormNativeGravityBFDensity field) +
        diracDualFormNativeCoframeGaugeDensity source field +
        diracDualFormNativeCoframeMatterDensity source point field)
      (diracDualFormNativeCoframeGaugeEulerCovector source field +
        diracDualFormNativeCoframeMatterEulerCovector source point field)
      field.coframe
    exact splitDerivative
  exact (diracDualFormNativeCoframeCommonCoreDensity_hasFDerivAt
    source point field nondegenerate).unique sameDerivative

theorem diracDualFormNativeCoframeLocalDensity_path_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeLocalDensity source point field
          (field.coframe + parameter • variation))
      (diracDualFormNativeCoframeEulerCovector source point field variation)
      0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative := identityDerivative.smul_const variation
  have variationDerivativeValue : (1 : ℝ) • variation = variation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have pathDerivative := variationDerivativeAtZero.const_add field.coframe
  have pointEquality :
      field.coframe = field.coframe + (0 : ℝ) • variation := by
    simp
  exact (diracDualFormNativeCoframeLocalDensity_hasFDerivAt
    source point field nondegenerate).comp_hasDerivAt_of_eq 0
      pathDerivative pointEquality

theorem diracDualFormNativeCoframeCommonCoreDensity_path_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeCommonCoreDensity source point field
          (field.coframe + parameter • variation))
      (diracDualFormNativeCoframeCommonCoreEulerCovector
        source point field variation) 0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative := identityDerivative.smul_const variation
  have variationDerivativeValue : (1 : ℝ) • variation = variation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have pathDerivative := variationDerivativeAtZero.const_add field.coframe
  have pointEquality :
      field.coframe = field.coframe + (0 : ℝ) • variation := by
    simp
  exact (diracDualFormNativeCoframeCommonCoreDensity_hasFDerivAt
    source point field nondegenerate).comp_hasDerivAt_of_eq 0
      pathDerivative pointEquality

/-- Exact new-root coframe split.  The direct `II+` reaction is inherited
from the unchanged constraint block; the common-core covector is generated
from the repaired root itself. -/
theorem diracDualFormNativeCoframeEulerCovector_apply
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeEulerCovector source point field variation =
      diracDualFormNativeCoframeCommonCoreEulerCovector source point field
          variation -
        formNativeCoframeConstraintReaction field variation := by
  have totalDerivative := diracDualFormNativeCoframeLocalDensity_path_hasDerivAt
    source point field nondegenerate variation
  have constraintDerivative :=
    generatedFormNativeGravityConstraintDensity_coframe_path_hasDerivAt
      field variation
  have commonDerivative :=
    diracDualFormNativeCoframeCommonCoreDensity_path_hasDerivAt
      source point field nondegenerate variation
  have sameDerivative : HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeLocalDensity source point field
          (field.coframe + parameter • variation))
      (-formNativeCoframeConstraintReaction field variation +
        diracDualFormNativeCoframeCommonCoreEulerCovector source point field
          variation) 0 := by
    rw [show (fun parameter : ℝ =>
        diracDualFormNativeCoframeLocalDensity source point field
          (field.coframe + parameter • variation)) =
      fun parameter =>
        generatedFormNativeGravityConstraintDensity
            (withCoframe field
              (field.coframe + parameter • variation)) +
          diracDualFormNativeCoframeCommonCoreDensity source point field
            (field.coframe + parameter • variation) by
      funext parameter
      exact
        diracDualFormNativeCoframeLocalDensity_eq_constraint_add_commonCore
          source point field (field.coframe + parameter • variation)]
    exact constraintDerivative.add commonDerivative
  have derivativeEquality := totalDerivative.unique sameDerivative
  linarith

/-- Fully routed local coframe response of the repaired root. -/
theorem diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeEulerCovector source point field variation =
      diracDualFormNativeCoframeGaugeEulerCovector source field variation +
        diracDualFormNativeCoframeMatterEulerCovector source point field
          variation -
        formNativeCoframeConstraintReaction field variation := by
  rw [diracDualFormNativeCoframeEulerCovector_apply source point field
    nondegenerate variation,
    diracDualFormNativeCoframeCommonCoreEulerCovector_eq_gauge_add_matter
      source point field nondegenerate]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeLocalVariation
