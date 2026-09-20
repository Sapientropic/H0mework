import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.Geometry.FundamentalLemma
import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore

/-!
# S9-C3c0: conjugate matter variation and generated Dirac--Yukawa equation

The independent conjugate Dirac field is varied through natural coordinates
on the actual `matterCoordinateEquiv` basis.  The coordinate-to-dual lift is
proved surjective, so the primitive test family covers every complex-linear
matter dual rather than a selected receipt or Standard-Model table.

The actual holonomic covariant derivative and actual exterior-Yukawa map are
first proved continuous from the primitive smooth fields.  The common local
and integrated action are then exactly affine under every compactly supported
conjugate variation.  Stationarity gives the weak and pointwise directional
equations, and the real/imaginary coordinate directions finally force the
actual generated Dirac--Yukawa vector to vanish pointwise.

No mass matrix, Dirac equation, integrability, dual coverage, or residual
certificate is supplied at the theorem mouth.
-/

namespace SaturationMonoid.PhysicsCore.StageNineConjugateMatterVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterFullVariations
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def chiralYukawaCoordinateBilinear :
    ScalarCoordinateCarrier →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun scalar :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        simp only [map_add]
      map_smul' := by
        intro parameter matter
        simp only [map_smul, RingHom.id_apply] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (first + second))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter))
    rw [map_add, chiralExteriorYukawaAction_add, LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter scalar
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (parameter • scalar))
            (matterCoordinateEquiv.symm matter)) =
        parameter • matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
    rw [map_smul, chiralExteriorYukawaAction_smul,
      LinearMap.smul_apply, map_smul]

theorem chiralYukawaCoordinate_apply_continuous
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (matter : BasePoint → MatterCoordinateCarrier)
    (scalarContinuous : Continuous scalar)
    (matterContinuous : Continuous matter) :
    Continuous fun point =>
      chiralYukawaCoordinateBilinear (scalar point) (matter point) := by
  exact
    (chiralYukawaCoordinateBilinear.toContinuousBilinearMap.continuous.comp
      scalarContinuous).clm_apply matterContinuous

theorem holonomicGravitySpinLift_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      diracSpinConnectionLift (configuration.gravityConnection point)
        direction := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  have connectionContinuous : ∀
      (formDirection internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        configuration.gravityConnection point formDirection internalOut
          internalIn := fun formDirection internalOut internalIn =>
    (smooth.2.1 formDirection internalOut internalIn).continuous
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  fun_prop

set_option maxHeartbeats 1200000 in
theorem holonomicMatterCovariantDerivative_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterCovariantDerivative configuration point direction) := by
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have derivativeContinuous : Continuous fun point =>
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (configuration.matter candidate))
        point direction := by
    unfold fieldDirectionalDerivative
    exact (matterSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have matterContinuous := matterSmooth.continuous
  have spinContinuous := diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicGravitySpinLift_continuous configuration smooth direction)
    matterContinuous
  have gaugeCoordinateContinuous : Continuous fun point =>
      p286CoordinateEquiv (configuration.gaugeConnection point direction) :=
    (smooth.2.2.2.2.1 direction).continuous
  have gaugeContinuous := matterP286ActionCoordinate_apply_continuous
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point direction))
    (fun point => matterCoordinateEquiv (configuration.matter point))
    gaugeCoordinateContinuous matterContinuous
  unfold holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact (derivativeContinuous.add spinContinuous).add
    (gaugeContinuous.congr fun point => by
      change
        matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed
                (p286CoordinateEquiv.symm
                  (p286CoordinateEquiv
                    (configuration.gaugeConnection point direction))))
              (matterCoordinateEquiv.symm
                (matterCoordinateEquiv (configuration.matter point)))) = _
      rw [p286CoordinateEquiv.symm_apply_apply,
        matterCoordinateEquiv.symm_apply_apply])

theorem holonomicMatterKineticSummand_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            direction)
          (holonomicMatterCovariantDerivative configuration point direction)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate direction)
    (holonomicMatterCovariantDerivative_coordinate_continuous configuration
      smooth direction)

theorem holonomicMatterKineticSum_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterCovariantDerivative configuration point)) := by
  have sumContinuous : Continuous fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              direction)
            (holonomicMatterCovariantDerivative configuration point
              direction)) := by
    apply continuous_finsetSum
    intro direction _
    exact holonomicMatterKineticSummand_coordinate_continuous configuration
      smooth nondegenerate direction
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem holonomicMatterYukawaVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (configuration.matter point)) := by
  have actual := chiralYukawaCoordinate_apply_continuous configuration.scalar
    (fun point => matterCoordinateEquiv (configuration.matter point))
    smooth.2.2.2.2.2.2.1.continuous
    smooth.2.2.2.2.2.2.2.1.continuous
  exact actual.congr fun point => by
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicGeneratedContinuumMatterVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      matterCoordinateEquiv
        (generatedContinuumMatterVector source 0 point
          (toContinuumPointField configuration point)) := by
  have kineticContinuous := holonomicMatterKineticSum_coordinate_continuous
    source configuration smooth nondegenerate
  have kineticWithIContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterCovariantDerivative configuration point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  have yukawaContinuous :=
    holonomicMatterYukawaVector_coordinate_continuous configuration smooth
  have actual := kineticWithIContinuous.add yukawaContinuous
  unfold generatedContinuumMatterVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart,
      matterFrameRelative_zeroChart]
    change
      Complex.I • matterCoordinateEquiv
          (matterGaugeKineticSum source 0 point
            (toContinuumPointField configuration point)
            (holonomicMatterCovariantDerivative configuration point)) +
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            (configuration.matter point)) =
      matterCoordinateEquiv
        (Complex.I •
            matterGaugeKineticSum source 0 point
              (toContinuumPointField configuration point)
              (holonomicMatterCovariantDerivative configuration point) +
          chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            (configuration.matter point))
    rw [map_add, map_smul]

/-- Natural coordinates of an independent complex-linear conjugate matter
field, expressed on the actual `matterCoordinateEquiv` basis. -/
def matterCoordinateDualBasis (index : MatterCoordinateIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  (PiLp.projₗ 2 (fun _ : MatterCoordinateIndex => ℂ) index).comp
    matterCoordinateEquiv.toLinearMap

def matterDualOfCoordinates
    (coordinates : MatterCoordinateCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ index : MatterCoordinateIndex,
    coordinates index • matterCoordinateDualBasis index

@[simp] theorem matterDualOfCoordinates_zero :
    matterDualOfCoordinates (0 : MatterCoordinateCarrier) = 0 := by
  apply LinearMap.ext
  intro matter
  simp [matterDualOfCoordinates]

theorem matterDualOfCoordinates_apply
    (coordinates : MatterCoordinateCarrier)
    (matter : DiracExteriorMatterCarrier) :
    matterDualOfCoordinates coordinates matter =
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv matter index * coordinates index := by
  simp only [matterDualOfCoordinates, LinearMap.sum_apply,
    LinearMap.smul_apply, matterCoordinateDualBasis, LinearMap.comp_apply,
    PiLp.projₗ_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  change coordinates index * matterCoordinateEquiv matter index =
    matterCoordinateEquiv matter index * coordinates index
  ring

theorem matterDualOfCoordinates_basis_apply
    (coordinates : MatterCoordinateCarrier) (index : MatterCoordinateIndex) :
    matterDualOfCoordinates coordinates
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) =
      coordinates index := by
  simp [matterDualOfCoordinates, matterCoordinateDualBasis]

def matterDualCoordinates
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier :=
  WithLp.toLp 2 fun index =>
    dual (matterCoordinateEquiv.symm
      (EuclideanSpace.single index (1 : ℂ)))

/-- The coordinate lift covers every independent conjugate matter dual; it is
not a restricted test family. -/
theorem matterDualOfCoordinates_surjective
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualOfCoordinates (matterDualCoordinates dual) = dual := by
  apply LinearMap.ext
  intro matter
  rw [matterDualOfCoordinates_apply]
  change (∑ index : MatterCoordinateIndex,
    matterCoordinateEquiv matter index *
      dual (matterCoordinateEquiv.symm
        (EuclideanSpace.single index (1 : ℂ)))) = dual matter
  rw [← matterDual_coordinate_expansion dual
    (matterCoordinateEquiv matter)]
  rw [matterCoordinateEquiv.symm_apply_apply]

def varyConjugateMatterCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    conjugateMatter := fun point =>
      configuration.conjugateMatter point +
        parameter • matterDualOfCoordinates (variation point) }

@[simp] theorem varyConjugateMatterCoordinates_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier) :
    varyConjugateMatterCoordinates configuration variation 0 =
      configuration := by
  cases configuration
  simp [varyConjugateMatterCoordinates]

def withConjugateMatter
    (field : StageNineContinuumPointField)
    (conjugateMatter : Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineContinuumPointField :=
  { field with conjugateMatter := conjugateMatter }

theorem toContinuumPointField_varyConjugateMatterCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyConjugateMatterCoordinates configuration variation parameter)
        point =
      withConjugateMatter (toContinuumPointField configuration point)
        (configuration.conjugateMatter point +
          parameter • matterDualOfCoordinates (variation point)) := by
  rfl

def conjugateMatterFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (matterDualOfCoordinates (variation point)
      (generatedContinuumMatterVector source 0 point
        (toContinuumPointField configuration point))).re

theorem generatedContinuumMatterDensity_withConjugateMatter_affine
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : MatterCoordinateCarrier) (parameter : ℝ) :
    generatedContinuumMatterDensity source 0 point
        (withConjugateMatter field
          (field.conjugateMatter +
            parameter • matterDualOfCoordinates variation)) =
      generatedContinuumMatterDensity source 0 point field +
        parameter *
          (matterDualOfCoordinates variation
            (generatedContinuumMatterVector source 0 point field)).re := by
  unfold generatedContinuumMatterDensity withConjugateMatter
  simp only [matterDualFrameRelative_zeroChart, LinearMap.add_apply,
    LinearMap.smul_apply, Complex.add_re]
  change
    (field.conjugateMatter
          (generatedContinuumMatterVector source 0 point field)).re +
        ((parameter : ℂ) *
          matterDualOfCoordinates variation
            (generatedContinuumMatterVector source 0 point field)).re = _
  simp [Complex.mul_re]

theorem generatedUnifiedLocalDensity_withConjugateMatter_affine
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : MatterCoordinateCarrier) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withConjugateMatter field
          (field.conjugateMatter +
            parameter • matterDualOfCoordinates variation)) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point field +
        parameter *
          (generatedVolumeDensity field *
            (matterDualOfCoordinates variation
              (generatedContinuumMatterVector source 0 point field)).re) := by
  rw [generatedUnifiedLocalDensityAtBoundary,
    generatedUnifiedLocalDensityAtBoundary]
  unfold generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
  rw [generatedContinuumMatterDensity_withConjugateMatter_affine]
  simp only [withConjugateMatter, generatedVolumeDensity,
    generatedGravitySimplicityDensity, generatedGravitySimplicityResidual,
    generatedGravityBFDensity, generatedScalarKineticDensity]
  ring

theorem holonomicLocalDensity_conjugateMatter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyConjugateMatterCoordinates configuration variation parameter)
          point) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
      conjugateMatterFirstVariationDensity source configuration variation
            point := by
  rw [toContinuumPointField_varyConjugateMatterCoordinates]
  exact generatedUnifiedLocalDensity_withConjugateMatter_affine source point
    (toContinuumPointField configuration point) (variation point) parameter

theorem conjugateMatterFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Continuous
      (conjugateMatterFirstVariationDensity source configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have vectorContinuous :=
    holonomicGeneratedContinuumMatterVector_coordinate_continuous source
      configuration smooth nondegenerate
  have variationContinuous : Continuous
      (variation : BasePoint → MatterCoordinateCarrier) :=
    variation.smooth.continuous
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (generatedContinuumMatterVector source 0 point
              (toContinuumPointField configuration point)) index *
          variation point index := by
    apply continuous_finsetSum
    intro index _
    have vectorCoordinateContinuous : Continuous fun point =>
        matterCoordinateEquiv
          (generatedContinuumMatterVector source 0 point
            (toContinuumPointField configuration point)) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp vectorContinuous
    have variationCoordinateContinuous : Continuous fun point =>
        variation point index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          variationContinuous
    exact vectorCoordinateContinuous.mul variationCoordinateContinuous
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold conjugateMatterFirstVariationDensity
  simp_rw [matterDualOfCoordinates_apply]
  exact volumeContinuous.mul realPairingContinuous

theorem conjugateMatterFirstVariationDensity_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier) (point : BasePoint)
    (variationZero : variation point = 0) :
    conjugateMatterFirstVariationDensity source configuration variation point =
      0 := by
  simp [conjugateMatterFirstVariationDensity, variationZero]

theorem conjugateMatterFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasCompactSupport
      (conjugateMatterFirstVariationDensity source configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact conjugateMatterFirstVariationDensity_eq_zero source configuration
    variation point variationZero

theorem conjugateMatterFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Integrable
      (conjugateMatterFirstVariationDensity source configuration variation) :=
  (conjugateMatterFirstVariationDensity_continuous source configuration smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (conjugateMatterFirstVariationDensity_compact source configuration
        variation)

theorem holonomicIntegratedUnifiedAction_conjugateMatter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source 0
        (varyConjugateMatterCoordinates configuration variation parameter) =
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            conjugateMatterFirstVariationDensity source configuration
              variation point) := by
  unfold holonomicIntegratedUnifiedAction
    sourceGeneratedIntegratedUnifiedAction integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyConjugateMatterCoordinates configuration variation parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter * conjugateMatterFirstVariationDensity source configuration
          variation point := by
    funext point
    exact holonomicLocalDensity_conjugateMatter_affine source configuration
      variation parameter point
  rw [pointwise]
  have firstIntegrable := conjugateMatterFirstVariationDensity_integrable
    source configuration smooth nondegenerate variation
  rw [integral_add densityIntegrable
    (firstIntegrable.const_mul parameter), integral_const_mul]

theorem holonomicIntegratedUnifiedAction_conjugateMatter_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyConjugateMatterCoordinates configuration variation parameter))
      (∫ point : BasePoint,
        conjugateMatterFirstVariationDensity source configuration variation
          point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    conjugateMatterFirstVariationDensity source configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyConjugateMatterCoordinates configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_conjugateMatter_affine source
      configuration smooth nondegenerate densityIntegrable variation parameter
  rw [actionEquality]
  simpa using
    ((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicIntegratedUnifiedAction source 0 configuration)

def CanonicalConjugateMatterActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyConjugateMatterCoordinates configuration variation parameter))
      0 0

def CanonicalConjugateMatterWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    (∫ point : BasePoint,
      conjugateMatterFirstVariationDensity source configuration variation
        point) = 0

theorem canonicalConjugateMatterActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalConjugateMatterActionStationary source
      configuration) :
    CanonicalConjugateMatterWeakEquation source configuration := by
  intro variation
  have actual :=
    holonomicIntegratedUnifiedAction_conjugateMatter_hasDerivAt source
      configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

def scalarTimesConjugateMatterVariation
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation MatterCoordinateCarrier where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

theorem matterDualOfCoordinates_real_smul
    (parameter : ℝ) (coordinates : MatterCoordinateCarrier) :
    matterDualOfCoordinates (parameter • coordinates) =
      parameter • matterDualOfCoordinates coordinates := by
  apply LinearMap.ext
  intro matter
  change matterDualOfCoordinates (parameter • coordinates) matter =
    (parameter : ℂ) * matterDualOfCoordinates coordinates matter
  rw [matterDualOfCoordinates_apply, matterDualOfCoordinates_apply]
  simp only [PiLp.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change matterCoordinateEquiv matter index *
      ((parameter : ℂ) * coordinates index) =
    (parameter : ℂ) *
      (matterCoordinateEquiv matter index * coordinates index)
  ring

def conjugateMatterDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (matterDualOfCoordinates direction
      (generatedContinuumMatterVector source 0 point
        (toContinuumPointField configuration point))).re

theorem conjugateMatterFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    conjugateMatterFirstVariationDensity source configuration
        (scalarTimesConjugateMatterVariation direction variation) point =
      variation point *
        conjugateMatterDirectionalCoefficient source configuration direction
          point := by
  unfold conjugateMatterFirstVariationDensity
    scalarTimesConjugateMatterVariation
    conjugateMatterDirectionalCoefficient
  rw [matterDualOfCoordinates_real_smul, LinearMap.smul_apply]
  change _ * (((variation point : ℂ) * _).re) = _
  simp [Complex.mul_re]
  ring

theorem conjugateMatterDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (conjugateMatterDirectionalCoefficient source configuration direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have vectorContinuous :=
    holonomicGeneratedContinuumMatterVector_coordinate_continuous source
      configuration smooth nondegenerate
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (generatedContinuumMatterVector source 0 point
              (toContinuumPointField configuration point)) index *
          direction index := by
    apply continuous_finsetSum
    intro index _
    exact ((PiLp.continuous_apply 2
      (fun _ : MatterCoordinateIndex => ℂ) index).comp vectorContinuous).mul
        continuous_const
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold conjugateMatterDirectionalCoefficient
  simp_rw [matterDualOfCoordinates_apply]
  exact volumeContinuous.mul realPairingContinuous

theorem canonicalConjugateMatterWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (weakEquation : CanonicalConjugateMatterWeakEquation source configuration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        conjugateMatterDirectionalCoefficient source configuration direction
          point) = 0 := by
  have actual := weakEquation
    (scalarTimesConjugateMatterVariation direction variation)
  simpa only [conjugateMatterFirstVariationDensity_scalarTimes] using actual

def CanonicalConjugateMatterPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : MatterCoordinateCarrier,
    conjugateMatterDirectionalCoefficient source configuration direction = 0

theorem canonicalConjugateMatterWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalConjugateMatterWeakEquation source configuration) :
    CanonicalConjugateMatterPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (conjugateMatterDirectionalCoefficient source configuration direction)
    (conjugateMatterDirectionalCoefficient_continuous source configuration
      smooth nondegenerate direction)
  intro variation
  exact canonicalConjugateMatterWeakEquation_direction_integral source
    configuration weakEquation direction variation

theorem matterDualOfCoordinates_single_apply
    (index : MatterCoordinateIndex) (coefficient : ℂ)
    (matter : DiracExteriorMatterCarrier) :
    matterDualOfCoordinates
        (EuclideanSpace.single index coefficient) matter =
      matterCoordinateEquiv matter index * coefficient := by
  rw [matterDualOfCoordinates_apply]
  simp

def CanonicalGeneratedDiracYukawaEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    generatedContinuumMatterVector source 0 point
      (toContinuumPointField configuration point) = 0

theorem canonicalConjugateMatterPointwiseEquation_implies_diracYukawaEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (pointwise : CanonicalConjugateMatterPointwiseEquation source
      configuration) :
    CanonicalGeneratedDiracYukawaEquation source configuration := by
  intro point
  let vector := generatedContinuumMatterVector source 0 point
    (toContinuumPointField configuration point)
  have volumeNe :
      generatedVolumeDensity (toContinuumPointField configuration point) ≠
        0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr (nondegenerate point)
  apply matterCoordinateEquiv.injective
  apply PiLp.ext
  intro index
  let realDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index (1 : ℂ)
  let imaginaryDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index Complex.I
  have realEquation := congrFun (pointwise realDirection) point
  have imaginaryEquation := congrFun (pointwise imaginaryDirection) point
  simp only [Pi.zero_apply] at realEquation imaginaryEquation
  have realPartZero : (matterCoordinateEquiv vector index).re = 0 := by
    unfold conjugateMatterDirectionalCoefficient realDirection at realEquation
    rw [matterDualOfCoordinates_single_apply] at realEquation
    simp only [mul_one] at realEquation
    exact (mul_eq_zero.mp realEquation).resolve_left volumeNe
  have imaginaryPartZero : (matterCoordinateEquiv vector index).im = 0 := by
    unfold conjugateMatterDirectionalCoefficient imaginaryDirection at imaginaryEquation
    rw [matterDualOfCoordinates_single_apply] at imaginaryEquation
    have productReal :
        (matterCoordinateEquiv vector index * Complex.I).re =
          -(matterCoordinateEquiv vector index).im := by
      simp
    rw [productReal] at imaginaryEquation
    have negImaginaryZero :=
      (mul_eq_zero.mp imaginaryEquation).resolve_left volumeNe
    exact neg_eq_zero.mp negImaginaryZero
  have coordinateZero : matterCoordinateEquiv vector index = 0 :=
    Complex.ext realPartZero imaginaryPartZero
  simpa [vector] using coordinateZero

theorem canonicalConjugateMatterActionStationary_implies_diracYukawaEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalConjugateMatterActionStationary source
      configuration) :
    CanonicalGeneratedDiracYukawaEquation source configuration := by
  apply canonicalConjugateMatterPointwiseEquation_implies_diracYukawaEquation
    source configuration nondegenerate
  apply canonicalConjugateMatterWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact canonicalConjugateMatterActionStationary_implies_weakEquation source
    configuration smooth nondegenerate densityIntegrable stationary

end

end SaturationMonoid.PhysicsCore.StageNineConjugateMatterVariation
