import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.Dirac.GravitySpinCovariance

/-!
# Field-section Spin covariance of the Dirac-dual form-native root

The integrated root is defined on a continuum first-jet section.  This module
constructs its complete tensorial Spin transport: coframe, lowered gravity
curvature, auxiliary and multiplier use the forced Lorentz representations;
matter, its covariant derivative, and the independent dual use the Dirac
representation; gauge and Lorentz-scalar slots remain unchanged.

The repaired local density and its spacetime integral are invariant under an
arbitrary pointwise Spin field.  This closes action-level local covariance on
the actual first-jet carrier.  It does not yet assert that the independently
defined primitive inhomogeneous connection action computes exactly the same
transformed curvature jet; that holonomic compatibility is a separate
producer seam.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFieldSectionSpinCovariance

open DiracExteriorMatterAction
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineCoframeSpinRepresentation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracKineticSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravitySpinCovariance
open StageNineFormNativeMotherAction
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineMatterCovariantDerivativeAffine
open StageNinePhysicalBivectorSpinRepresentation
open StageNineScalarLocalSpinDensity
open StageNineSpinMatterBundle
open MeasureTheory
open scoped MatrixGroups

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Complete tensorial point-field transport -/

/-- Canonical Spin transport on every field slot consumed by the repaired
first-jet action.  The Weyl-dual Spin element is forced on the Lorentz vector
and bivector slots by the already proved Dirac/coframe intertwiner. -/
def transformDiracDualFormNativePointField
    (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) : StageNineContinuumPointField where
  coframe :=
    spinLorentzCoframeRepresentation (spinWeylDual groupElement) field.coframe
  gravityCurvature :=
    spinLorentzLoweredPhysicalBivector (spinWeylDual groupElement)
      field.gravityCurvature
  gravityAuxiliary :=
    spinLorentzPhysicalBivectorRepresentation (spinWeylDual groupElement)
      field.gravityAuxiliary
  gravitySimplicityMultiplier :=
    spinLorentzPhysicalBivectorRepresentation (spinWeylDual groupElement)
      field.gravitySimplicityMultiplier
  gaugeCurvature := field.gaugeCurvature
  gaugeAuxiliary := field.gaugeAuxiliary
  scalar := field.scalar
  scalarCovariantDerivative := field.scalarCovariantDerivative
  matter := spinDiracMatterRepresentation groupElement field.matter
  matterCovariantDerivative := fun direction =>
    spinDiracMatterRepresentation groupElement
      (field.matterCovariantDerivative direction)
  conjugateMatter := field.conjugateMatter.comp
    (spinDiracMatterRepresentation groupElement⁻¹)

@[simp] theorem transformDiracDualFormNativePointField_coframe
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    (transformDiracDualFormNativePointField groupElement field).coframe =
      spinLorentzCoframeRepresentation (spinWeylDual groupElement)
        field.coframe :=
  rfl

@[simp] theorem transformDiracDualFormNativePointField_matter
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    (transformDiracDualFormNativePointField groupElement field).matter =
      spinDiracMatterRepresentation groupElement field.matter :=
  rfl

@[simp] theorem transformDiracDualFormNativePointField_conjugateMatter
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    (transformDiracDualFormNativePointField groupElement field).conjugateMatter =
      field.conjugateMatter.comp
        (spinDiracMatterRepresentation groupElement⁻¹) :=
  rfl

/-! ## Gravity, gauge, scalar, and volume blocks -/

theorem generatedFormNativeGravityBFDensity_diracDualSpin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedFormNativeGravityBFDensity
        (transformDiracDualFormNativePointField groupElement field) =
      generatedFormNativeGravityBFDensity field := by
  change generatedFormNativeGravityBFDensity
      (transformFormNativeGravityPointField (spinWeylDual groupElement) field) =
    generatedFormNativeGravityBFDensity field
  exact generatedFormNativeGravityBFDensity_spin_invariant _ _

theorem generatedFormNativeGravityConstraintDensity_diracDualSpin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedFormNativeGravityConstraintDensity
        (transformDiracDualFormNativePointField groupElement field) =
      generatedFormNativeGravityConstraintDensity field := by
  change generatedFormNativeGravityConstraintDensity
      (transformFormNativeGravityPointField (spinWeylDual groupElement) field) =
    generatedFormNativeGravityConstraintDensity field
  exact generatedFormNativeGravityConstraintDensity_spin_invariant _ _

theorem generatedFormNativeGaugeDensityAtBoundary_diracDualSpin_invariant
    (groupElement : SpinPlus13)
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    generatedFormNativeGaugeDensityAtBoundary boundary
        (transformDiracDualFormNativePointField groupElement field) =
      generatedFormNativeGaugeDensityAtBoundary boundary field := by
  change generatedFormNativeGaugeDensityAtBoundary boundary
      (transformFormNativeGravityPointField (spinWeylDual groupElement) field) =
    generatedFormNativeGaugeDensityAtBoundary boundary field
  exact generatedFormNativeGaugeDensityAtBoundary_spin_invariant _ _ _
    nondegenerate

theorem generatedVolumeDensity_diracDualSpin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedVolumeDensity
        (transformDiracDualFormNativePointField groupElement field) =
      generatedVolumeDensity field := by
  change generatedVolumeDensity
      (transformFormNativeGravityPointField (spinWeylDual groupElement) field) =
    generatedVolumeDensity field
  exact generatedVolumeDensity_formNative_spin_invariant _ _

theorem generatedDensitizedContinuumScalarDensity_diracDualSpin_invariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumScalarDensity source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      generatedDensitizedContinuumScalarDensity source chart point field := by
  have metricEquality :
      lorentzianMetricOfCoframe
          (transformDiracDualFormNativePointField groupElement field).coframe =
        lorentzianMetricOfCoframe field.coframe :=
    lorentzianMetricOfCoframe_spinLorentzCoframeRepresentation
      (spinWeylDual groupElement) field.coframe
  unfold generatedDensitizedContinuumScalarDensity
    generatedScalarKineticDensity
  rw [generatedVolumeDensity_diracDualSpin_invariant, metricEquality]
  simp [transformDiracDualFormNativePointField]

/-! ## Dirac kinetic and repaired Yukawa blocks -/

theorem generatedContinuumMatterKineticVector_diracDualSpin_covariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedContinuumMatterKineticVector source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      spinDiracMatterRepresentation groupElement
        (generatedContinuumMatterKineticVector source chart point field) := by
  have frameDerivativeEquality :
      matterDerivativeFrameRelative source chart point
          (transformDiracDualFormNativePointField groupElement field).matterCovariantDerivative =
        fun direction =>
          spinDiracMatterRepresentation groupElement
            (matterDerivativeFrameRelative source chart point
              field.matterCovariantDerivative direction) := by
    exact matterDerivativeFrameRelative_spin_covariant source chart point
      groupElement field.matterCovariantDerivative
  have summandEquality (direction : LorentzianIndex) :
      diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe :=
                (transformDiracDualFormNativePointField groupElement field).coframe,
              derivative := 0 }
            direction)
          (matterDerivativeFrameRelative source chart point
            (transformDiracDualFormNativePointField groupElement field).matterCovariantDerivative
            direction) =
        spinDiracMatterRepresentation groupElement
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := field.coframe, derivative := 0 }
              direction)
            (matterDerivativeFrameRelative source chart point
              field.matterCovariantDerivative direction)) := by
    rw [transformDiracDualFormNativePointField_coframe,
      congrFun frameDerivativeEquality direction]
    exact
      inverseCoframeDiracGamma_matterAction_spinWeylDual_equivariant
        groupElement { coframe := field.coframe, derivative := 0 }
        direction
        (matterDerivativeFrameRelative source chart point
          field.matterCovariantDerivative direction)
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  have sumEquality :
      (∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe :=
                  (transformDiracDualFormNativePointField groupElement field).coframe,
                derivative := 0 }
              direction)
            (matterDerivativeFrameRelative source chart point
              (transformDiracDualFormNativePointField groupElement field).matterCovariantDerivative
              direction)) =
        ∑ direction : LorentzianIndex,
          spinDiracMatterRepresentation groupElement
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := field.coframe, derivative := 0 }
                direction)
              (matterDerivativeFrameRelative source chart point
                field.matterCovariantDerivative direction)) := by
    exact Finset.sum_congr rfl fun direction _ => summandEquality direction
  rw [sumEquality, ← map_sum, ← map_smul]

theorem generatedDensitizedContinuumMatterKineticDensity_diracDualSpin_invariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumMatterKineticDensity source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      generatedDensitizedContinuumMatterKineticDensity source chart point
        field := by
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [generatedVolumeDensity_diracDualSpin_invariant]
  rw [generatedContinuumMatterKineticVector_diracDualSpin_covariant]
  rw [transformDiracDualFormNativePointField_conjugateMatter]
  rw [matterDualFrameRelative_spin_evaluation_invariant]

theorem generatedContinuumDiracDualYukawaVector_diracDualSpin_covariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedContinuumDiracDualYukawaVector source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      spinDiracMatterRepresentation groupElement
        (generatedContinuumDiracDualYukawaVector source chart point field) := by
  have matterEquality :
      matterFrameRelative source chart point
          (transformDiracDualFormNativePointField groupElement field).matter =
        spinDiracMatterRepresentation groupElement
          (matterFrameRelative source chart point field.matter) := by
    change matterFrameRelative source chart point
        (spinDiracMatterRepresentation groupElement field.matter) = _
    exact matterFrameRelative_spin_covariant source chart point groupElement
      field.matter
  unfold generatedContinuumDiracDualYukawaVector
  rw [matterEquality]
  exact LinearMap.congr_fun
    (diracDualRightChiralYukawaAction_spin_equivariant groupElement
      (scalarCoordinateEquiv.symm
        (scalarFrameRelativeCoordinates source chart point field.scalar)))
    (matterFrameRelative source chart point field.matter)

theorem
    generatedDensitizedContinuumDiracDualYukawaDensity_diracDualSpin_invariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumDiracDualYukawaDensity source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      generatedDensitizedContinuumDiracDualYukawaDensity source chart point
        field := by
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [generatedVolumeDensity_diracDualSpin_invariant]
  rw [generatedContinuumDiracDualYukawaVector_diracDualSpin_covariant]
  rw [transformDiracDualFormNativePointField_conjugateMatter]
  rw [matterDualFrameRelative_spin_evaluation_invariant]

theorem generatedDiracDualFormNativeMatterDensity_spin_invariant
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField) :
    generatedDiracDualFormNativeMatterDensity source chart point
        (transformDiracDualFormNativePointField groupElement field) =
      generatedDiracDualFormNativeMatterDensity source chart point field := by
  unfold generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [generatedDensitizedContinuumScalarDensity_diracDualSpin_invariant,
    generatedDensitizedContinuumMatterKineticDensity_diracDualSpin_invariant,
    generatedDensitizedContinuumDiracDualYukawaDensity_diracDualSpin_invariant]

/-! ## Complete local and integrated action invariance -/

theorem generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_spin_invariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (groupElement : SpinPlus13)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (transformDiracDualFormNativePointField groupElement field) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point field := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGravityBFDensity_diracDualSpin_invariant,
    generatedFormNativeGravityConstraintDensity_diracDualSpin_invariant,
    generatedFormNativeGaugeDensityAtBoundary_diracDualSpin_invariant
      groupElement boundary field nondegenerate,
    generatedDiracDualFormNativeMatterDensity_spin_invariant]

/-- Pointwise Spin field action on the complete first-jet section. -/
def transformDiracDualFormNativeFieldSection
    (spinField : BasePoint → SpinPlus13)
    (field : StageNineContinuumFieldSection) :
    StageNineContinuumFieldSection := fun point =>
  transformDiracDualFormNativePointField (spinField point) (field point)

theorem integratedDiracDualFormNativeUnifiedActionAtBoundary_spin_invariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (field : StageNineContinuumFieldSection)
    (nondegenerate : ∀ point, Matrix.det (field point).coframe ≠ 0) :
    integratedDiracDualFormNativeUnifiedActionAtBoundary source boundary chart
        (transformDiracDualFormNativeFieldSection spinField field) =
      integratedDiracDualFormNativeUnifiedActionAtBoundary source boundary chart
        field := by
  apply integral_congr_ae
  filter_upwards with point
  exact
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_spin_invariant
      source boundary chart point (spinField point) (field point)
        (nondegenerate point)

theorem sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction_spin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (field : StageNineContinuumFieldSection)
    (nondegenerate : ∀ point, Matrix.det (field point).coframe ≠ 0) :
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction source chart
        (transformDiracDualFormNativeFieldSection spinField field) =
      sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction source chart
        field :=
  integratedDiracDualFormNativeUnifiedActionAtBoundary_spin_invariant source
    (sourceGeneratedUnifiedCouplings source) chart spinField field
      nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFieldSectionSpinCovariance
