import H0mework.Physics.Constitutive.BlockwiseConstitutive
import H0mework.Physics.Matter.SU7ExteriorMatterActionCore
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineBlockwiseConstitutive
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open PointwiseLorentzianCoframeJet
open EmpiricalReferenceScaleCouplingBoundary

noncomputable section

/-- One fiber of continuum first-jet data.  Curvatures and covariant
derivatives are tensorial jet coordinates, not stored field-equation or
invariance certificates.  S9-C will restrict global sections to holonomic,
compactly supported variations. -/
@[ext] structure StageNineContinuumPointField where
  /-- The tetrad is a dynamical field coordinate.  It is not frozen to the
  source coframe: S9-C must be able to vary this slot and derive its stress
  equation from the same action. -/
  coframe : LorentzianCoframe
  gravityCurvature : PhysicalBivector
  gravityAuxiliary : PhysicalBivector
  /-- Dynamical two-form multiplier for the tetrad--bivector `II+`
  constraint.  It is an action variable, not a supplied simplicity receipt. -/
  gravitySimplicityMultiplier : PhysicalBivector
  /-- One actual P286 Lie-valued curvature; strong, weak, and hypercharge are
  typed projections of this mother-relative field, not three scalar slots. -/
  gaugeCurvature : Fin 6 → P286LieBlockData
  gaugeAuxiliary : Fin 6 → P286LieBlockData
  scalar : ScalarCoordinateCarrier
  scalarCovariantDerivative : LorentzianIndex → ScalarCoordinateCarrier
  matter : DiracExteriorMatterCarrier
  matterCovariantDerivative : LorentzianIndex → DiracExteriorMatterCarrier
  conjugateMatter : Module.Dual ℂ DiracExteriorMatterCarrier

abbrev StageNineContinuumFieldSection :=
  BasePoint → StageNineContinuumPointField

/-- Signature of the induced Lorentz metric on the oriented two-form basis
`(01,02,03,23,31,12)`. -/
def lorentzianTwoFormSign (pair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst pair) *
    minkowskiInternalSign (pairSecond pair)

/-- Metric pairing on internal-bivector-valued spacetime two-forms.  Both the
internal and spacetime pair indices carry the induced Lorentz signature;
omitting the latter would make the fixed Hodge skew with respect to a raw
Euclidean coordinate dot and would destroy the gravity constitutive
variation. -/
def gravityCoordinatePairing
    (first second : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    ∑ spacetimePair : Fin 6,
      lorentzianTwoFormSign internalPair *
        lorentzianTwoFormSign spacetimePair *
        first internalPair spacetimePair * second internalPair spacetimePair

def coframeTwoFormLinear
    (coframe : LorentzianCoframe) : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm where
  toFun := fun form internalPair =>
    ∑ spacetimePair : Fin 6,
      coframeWedge coframe internalPair spacetimePair * form spacetimePair
  map_add' := by
    intro first second
    funext internalPair
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro spacetimePair _
    ring
  map_smul' := by
    intro scalar form
    funext internalPair
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro spacetimePair _
    ring

/-- Total raw inverse-frame operator.  `Matrix.inv` keeps the action defined
on the whole affine coframe carrier; S9-C selects the nondegenerate branch
before interpreting it as an equivalence. -/
def inverseCoframeTwoFormLinear
    (coframe : LorentzianCoframe) : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm :=
  coframeTwoFormLinear coframe⁻¹

/-- The spacetime Hodge used by the action is recomputed from the dynamical
coframe.  It is not the gravity internal bivector dual and it is not frozen to
the source background. -/
def coframeGaugeSpacetimeHodgeLinear
    (coframe : LorentzianCoframe) : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm :=
  (inverseCoframeTwoFormLinear coframe).comp
    (lorentzianCoframeHodgeEquiv.toLinearMap.comp
      (coframeTwoFormLinear coframe))

/-- Pull the fixed Lorentz two-form metric back along the same exterior-square
coframe used to generate the dynamical Hodge. -/
def coframeTwoFormMetricPairing
    (coframe : LorentzianCoframe) (first second : GaugeTwoForm) : ℝ :=
  ∑ pair : Fin 6,
    lorentzianTwoFormSign pair *
      coframeTwoFormLinear coframe first pair *
      coframeTwoFormLinear coframe second pair

/-- Metric pairing on internal-bivector-valued spacetime two-forms, generated
from the same dynamical coframe as the spacetime Hodge. -/
def gravityCoframePairing
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    lorentzianTwoFormSign internalPair *
      coframeTwoFormMetricPairing coframe
        (first internalPair) (second internalPair)

theorem canonicalPhysicalSourceCoframe_inv (point : BasePoint) :
    (canonicalPhysicalSource.coframeAt point)⁻¹ =
      Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
        (-point 2) := by
  apply Matrix.inv_eq_left_inv
  rw [canonicalPhysicalSource_coframeAt_eq_transvection]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_four]

theorem coframeTwoFormLinear_positiveSource (point : BasePoint) :
    coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point) =
      (positiveCoframeTwoFormFrame point).toLinearMap := by
  apply LinearMap.ext
  intro form
  funext pair
  exact positiveCoframeTwoFormFrame_eq_coframeWedge point form pair |>.symm

theorem inverseCoframeTwoFormLinear_positiveSource (point : BasePoint) :
    inverseCoframeTwoFormLinear (canonicalPhysicalSource.coframeAt point) =
      (positiveCoframeTwoFormFrame point).symm.toLinearMap := by
  apply LinearMap.ext
  intro form
  funext pair
  rw [inverseCoframeTwoFormLinear, canonicalPhysicalSourceCoframe_inv]
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge,
      positiveCoframeTwoFormFrame, pairFirst, pairSecond,
      Matrix.transvection, Matrix.single, Matrix.one_apply,
      Fin.sum_univ_six]
  all_goals ring

/-- At the generated background coframe, the dynamical action operator exact
recovers the typed source constitutive Hodge from S9-B2. -/
theorem coframeGaugeSpacetimeHodgeLinear_positiveSource
    (point : BasePoint) :
    coframeGaugeSpacetimeHodgeLinear
        (canonicalPhysicalSource.coframeAt point) =
      (positiveGaugeSpacetimeHodge point).toLinearMap := by
  rw [coframeGaugeSpacetimeHodgeLinear,
    coframeTwoFormLinear_positiveSource,
    inverseCoframeTwoFormLinear_positiveSource]
  rfl

def gravitySpacetimeHodge
    (coframe : LorentzianCoframe)
    (bivector : PhysicalBivector) : PhysicalBivector :=
  fun internalPair =>
    coframeGaugeSpacetimeHodgeLinear coframe (bivector internalPair)

def generatedGravityBFDensity
    (field : StageNineContinuumPointField) : ℝ :=
  gravityCoframePairing field.coframe field.gravityAuxiliary
      (gravitySpacetimeHodge field.coframe field.gravityCurvature) -
    (1 / 2 : ℝ) *
      gravityCoframePairing field.coframe field.gravityAuxiliary
        (gravitySpacetimeHodge field.coframe
          (gravityInternalDualEquiv field.gravityAuxiliary))

/-- Tetrad--bivector form of the selected Plebanski `II+` constraint.  The
residual is computed from dynamical fields; no simplicity Boolean enters the
action mouth. -/
def generatedGravitySimplicityResidual
    (field : StageNineContinuumPointField) : PhysicalBivector :=
  field.gravityAuxiliary - physicalIIPlusBivector field.coframe

/-- Componentwise squared Plebanski residual.  Squaring makes the selected
`II+` branch a genuine multiplier constraint while ensuring its contribution
to the `B` variation vanishes on the simplicity shell. -/
def gravitySimplicityMultiplierPairing
    (multiplier residual : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    ∑ spacetimePair : Fin 6,
      multiplier internalPair spacetimePair *
        residual internalPair spacetimePair ^ 2

/-- Genuine densitized multiplier channel in the common action.  Variation of
each multiplier coordinate probes the square of the corresponding Plebanski
residual; no supplied simplicity Boolean enters this term. -/
def generatedGravitySimplicityDensity
    (field : StageNineContinuumPointField) : ℝ :=
  gravitySimplicityMultiplierPairing field.gravitySimplicityMultiplier
    (generatedGravitySimplicityResidual field)

theorem generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero
    (field : StageNineContinuumPointField)
    (multiplierZero : field.gravitySimplicityMultiplier = 0) :
    generatedGravitySimplicityDensity field = 0 := by
  simp [generatedGravitySimplicityDensity,
    gravitySimplicityMultiplierPairing, multiplierZero]

def gaugeOperatorCoefficient
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (output input : Fin 6) : ℝ :=
  operator (fun candidate => if candidate = input then 1 else 0) output

/-- Extend a real spacetime two-form operator to any real module without
touching its internal Lie-algebra index. -/
def liftGaugeTwoFormOperator
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → V) : Fin 6 → V :=
  fun output =>
    ∑ input : Fin 6,
      gaugeOperatorCoefficient operator output input • form input

/-- Pull back the fixed Lorentz two-form metric for Lie-algebra-valued forms.
The internal pairing remains typed by the chosen gauge block. -/
def generatedGaugeTwoFormMetricPairing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V → V → ℝ)
    (coframe : LorentzianCoframe)
    (first second : Fin 6 → V) : ℝ :=
  ∑ pair : Fin 6,
    lorentzianTwoFormSign pair *
      pairing
        (liftGaugeTwoFormOperator
          (coframeTwoFormLinear coframe) first pair)
        (liftGaugeTwoFormOperator
          (coframeTwoFormLinear coframe) second pair)

def specialUnitaryLiePairing
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second : SpecialUnitaryLieMatrix n) : ℝ :=
  -(Matrix.trace
    ((first : Matrix n n ℂ) * (second : Matrix n n ℂ))).re

def hyperchargeLiePairing
    (first second : HyperchargeLieScalar) : ℝ :=
  -(first.1 * second.1).re

def generatedGaugeSectorBFDensity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V → V → ℝ)
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : Fin 6 → V) : ℝ :=
  generatedGaugeTwoFormMetricPairing pairing coframe auxiliary
      (liftGaugeTwoFormOperator spacetimeHodge curvature) -
    (1 / 2 : ℝ) *
      generatedGaugeTwoFormMetricPairing pairing coframe auxiliary
        (liftGaugeTwoFormOperator spacetimeHodge
          (liftGaugeTwoFormOperator operator auxiliary))

def scalarCoordinatePairingRe
    (first second : ScalarCoordinateCarrier) : ℝ :=
  ∑ index : ScalarBasisIndex,
    (star (first index) * second index).re

def scalarFrameRelativeCovariantDerivative
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint)
    (derivative : LorentzianIndex → ScalarCoordinateCarrier) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  fun direction =>
    scalarFrameRelativeCoordinates source chart point (derivative direction)

def generatedScalarKineticDensity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        ((lorentzianMetricOfCoframe field.coframe)⁻¹ first second) *
          scalarCoordinatePairingRe
            (scalarFrameRelativeCovariantDerivative source chart point
              field.scalarCovariantDerivative first)
            (scalarFrameRelativeCovariantDerivative source chart point
              field.scalarCovariantDerivative second)

def matterFrameRelative
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  diracExteriorMatterGaugeRepresentation
    (generatedScalarFrame source chart point)⁻¹ matter

def matterDerivativeFrameRelative
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint)
    (derivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun direction =>
    matterFrameRelative source chart point (derivative direction)

def matterDualFrameRelative
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  dual.comp
    (diracExteriorMatterGaugeRepresentation
      (generatedScalarFrame source chart point))

def generatedContinuumMatterVector
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := field.coframe, derivative := 0 } direction)
          (matterDerivativeFrameRelative source chart point
            field.matterCovariantDerivative direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm
        (scalarFrameRelativeCoordinates source chart point field.scalar))
      (matterFrameRelative source chart point field.matter)

def generatedContinuumMatterDensity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  (matterDualFrameRelative source chart point field.conjugateMatter
    (generatedContinuumMatterVector source chart point field)).re

/-- Stage 9 does not accept an empirical coupling table at its source mouth.
The common positive coupling is generated by the source keep/trace parameter;
the reference scale is generated from the continuous contact residual.  The
older empirical boundary remains available only to the explicitly named
`...AtBoundary` comparison functional below. -/
def sourceGeneratedUnifiedCouplings
    (source : SmoothUnifiedSource) : EmpiricalReferenceScaleCouplings where
  renormalizationScale := 1 + source.continuousContactResidual ^ 2
  scale_pos := by positivity
  strongCouplingSquared :=
    positiveUnit source.legacy.sigma source.legacy.sigma_pos
  weakCouplingSquared :=
    positiveUnit source.legacy.sigma source.legacy.sigma_pos
  hyperchargeCouplingSquared :=
    positiveUnit source.legacy.sigma source.legacy.sigma_pos
  strong_pos := by simp [positiveUnit, source.legacy.sigma_pos]
  weak_pos := by simp [positiveUnit, source.legacy.sigma_pos]
  hypercharge_pos := by simp [positiveUnit, source.legacy.sigma_pos]

def generatedVolumeDensity
    (field : StageNineContinuumPointField) : ℝ :=
  abs (Matrix.det field.coframe)

/-- Gauge, scalar, and matter terms independent of both gravity auxiliary
channels. -/
def generatedUnifiedLocalDensityNonGravityCoreAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  let spacetimeHodge := coframeGaugeSpacetimeHodgeLinear field.coframe
  generatedGaugeSectorBFDensity
      (@specialUnitaryLiePairing (Fin 3) _ _)
      field.coframe
      spacetimeHodge
      ((boundary.strongCouplingSquared : ℝ) • spacetimeHodge)
      (fun pair => (field.gaugeCurvature pair).1)
      (fun pair => (field.gaugeAuxiliary pair).1) +
    generatedGaugeSectorBFDensity
      (@specialUnitaryLiePairing (Fin 2) _ _)
      field.coframe
      spacetimeHodge
      ((boundary.weakCouplingSquared : ℝ) • spacetimeHodge)
      (fun pair => (field.gaugeCurvature pair).2.1)
      (fun pair => (field.gaugeAuxiliary pair).2.1) +
    generatedGaugeSectorBFDensity hyperchargeLiePairing
      field.coframe
      spacetimeHodge
      ((boundary.hyperchargeCouplingSquared : ℝ) • spacetimeHodge)
      (fun pair => (field.gaugeCurvature pair).2.2)
      (fun pair => (field.gaugeAuxiliary pair).2.2) +
    generatedScalarKineticDensity source chart point field -
    generatedScalarPotential source chart point field.scalar +
    generatedContinuumMatterDensity source chart point field

/-- The part of the continuum Lagrangian independent of the dynamical
Plebanski simplicity multiplier.  Keeping this block separate makes the
multiplier variation definitionally auditable. -/
def generatedUnifiedLocalDensityCoreAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedGravityBFDensity field +
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
      source boundary chart point field

/-- The genuine continuum local Lagrangian density.  It contains the
Plebanski multiplier/BF block, all three gauge constitutive blocks, scalar
kinetic and source-generated potential terms, and the continuum
Dirac--Yukawa term. -/
def generatedUnifiedLocalDensityAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (generatedGravitySimplicityDensity field +
      generatedUnifiedLocalDensityCoreAtBoundary
        source boundary chart point field)

def transportContinuumPointField
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    StageNineContinuumPointField where
  coframe := field.coframe
  gravityCurvature := field.gravityCurvature
  gravityAuxiliary := field.gravityAuxiliary
  gravitySimplicityMultiplier := field.gravitySimplicityMultiplier
  gaugeCurvature := field.gaugeCurvature
  gaugeAuxiliary := field.gaugeAuxiliary
  scalar := scalarCoordinateAction
    (generatedTransition source initial terminal point) field.scalar
  scalarCovariantDerivative := fun direction =>
    scalarCoordinateAction
      (generatedTransition source initial terminal point)
      (field.scalarCovariantDerivative direction)
  matter := diracExteriorMatterGaugeRepresentation
    (generatedTransition source initial terminal point) field.matter
  matterCovariantDerivative := fun direction =>
    diracExteriorMatterGaugeRepresentation
      (generatedTransition source initial terminal point)
      (field.matterCovariantDerivative direction)
  conjugateMatter := field.conjugateMatter.comp
    (diracExteriorMatterGaugeRepresentation
      (generatedTransition source initial terminal point)⁻¹)

theorem matterFrameRelative_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    matterFrameRelative source terminal point
        (diracExteriorMatterGaugeRepresentation
          (generatedTransition source initial terminal point) matter) =
      matterFrameRelative source initial point matter := by
  rw [matterFrameRelative, matterFrameRelative,
    generatedScalarFrame_overlap, mul_inv_rev]
  change
    (diracExteriorMatterGaugeRepresentation
      ((generatedScalarFrame source initial point)⁻¹ *
        (generatedTransition source initial terminal point)⁻¹))
      (diracExteriorMatterGaugeRepresentation
        (generatedTransition source initial terminal point) matter) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp

theorem matterDualFrameRelative_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualFrameRelative source terminal point
        (dual.comp (diracExteriorMatterGaugeRepresentation
          (generatedTransition source initial terminal point)⁻¹)) =
      matterDualFrameRelative source initial point dual := by
  apply LinearMap.ext
  intro matter
  simp only [matterDualFrameRelative, LinearMap.comp_apply]
  rw [generatedScalarFrame_overlap]
  change dual
    (diracExteriorMatterGaugeRepresentation
      (generatedTransition source initial terminal point)⁻¹
      (diracExteriorMatterGaugeRepresentation
        (generatedTransition source initial terminal point *
          generatedScalarFrame source initial point) matter)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp

theorem scalarFrameRelativeCovariantDerivative_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint)
    (derivative : LorentzianIndex → ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    scalarFrameRelativeCovariantDerivative source terminal point
        (fun index =>
          scalarCoordinateAction
            (generatedTransition source initial terminal point)
            (derivative index)) direction =
      scalarFrameRelativeCovariantDerivative source initial point
        derivative direction := by
  exact scalarFrameRelativeCoordinates_overlap
    source initial terminal point (derivative direction)

@[simp] theorem scalarFrameRelativeCovariantDerivative_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    scalarFrameRelativeCovariantDerivative source chart point 0 = 0 := by
  funext direction
  simp [scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates, scalarCoordinateAction]

theorem generatedScalarKineticDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedScalarKineticDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedScalarKineticDensity source initial point field := by
  have derivativeEquality :
      scalarFrameRelativeCovariantDerivative source terminal point
          (transportContinuumPointField source initial terminal point field).scalarCovariantDerivative =
        scalarFrameRelativeCovariantDerivative source initial point
          field.scalarCovariantDerivative := by
    funext direction
    exact scalarFrameRelativeCovariantDerivative_overlap
      source initial terminal point field.scalarCovariantDerivative direction
  unfold generatedScalarKineticDensity
  rw [derivativeEquality]
  rfl

theorem generatedContinuumMatterVector_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedContinuumMatterVector source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedContinuumMatterVector source initial point field := by
  have derivativeEquality :
      matterDerivativeFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point field).matterCovariantDerivative =
        matterDerivativeFrameRelative source initial point
          field.matterCovariantDerivative := by
    funext direction
    exact matterFrameRelative_overlap source initial terminal point
      (field.matterCovariantDerivative direction)
  have matterEquality :
      matterFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point field).matter =
        matterFrameRelative source initial point field.matter :=
    matterFrameRelative_overlap source initial terminal point field.matter
  have scalarEquality :
      scalarFrameRelativeCoordinates source terminal point
          (transportContinuumPointField source initial terminal point field).scalar =
        scalarFrameRelativeCoordinates source initial point field.scalar :=
    scalarFrameRelativeCoordinates_overlap
      source initial terminal point field.scalar
  unfold generatedContinuumMatterVector
  rw [derivativeEquality, matterEquality, scalarEquality]
  rfl

theorem generatedContinuumMatterDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedContinuumMatterDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedContinuumMatterDensity source initial point field := by
  have dualEquality :
      matterDualFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point field).conjugateMatter =
        matterDualFrameRelative source initial point field.conjugateMatter :=
    matterDualFrameRelative_overlap source initial terminal point
      field.conjugateMatter
  have vectorEquality := generatedContinuumMatterVector_overlap
    source initial terminal point field
  unfold generatedContinuumMatterDensity
  rw [dualEquality, vectorEquality]

theorem generatedUnifiedLocalDensity_overlap
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedUnifiedLocalDensityAtBoundary source boundary terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedUnifiedLocalDensityAtBoundary source boundary initial point field := by
  have scalarKineticEquality := generatedScalarKineticDensity_overlap
    source initial terminal point field
  have scalarPotentialEquality :
      generatedScalarPotential source terminal point
          (transportContinuumPointField source initial terminal point field).scalar =
        generatedScalarPotential source initial point field.scalar :=
    generatedScalarPotential_overlap_invariant
      source initial terminal point field.scalar
  have matterEquality := generatedContinuumMatterDensity_overlap
    source initial terminal point field
  unfold generatedUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
  rw [scalarKineticEquality, scalarPotentialEquality, matterEquality]
  rfl

def transportContinuumFieldSection
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    StageNineContinuumFieldSection :=
  fun point =>
    transportContinuumPointField source initial terminal point (field point)

/-- Actual four-dimensional Bochner integral over the smooth base carrier.
This is not a point evaluation or finite-link sum. -/
def integratedUnifiedActionAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    generatedUnifiedLocalDensityAtBoundary source boundary chart point (field point)

theorem integratedUnifiedActionAtBoundary_chartInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    integratedUnifiedActionAtBoundary source boundary terminal
        (transportContinuumFieldSection source initial terminal field) =
      integratedUnifiedActionAtBoundary source boundary initial field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  exact generatedUnifiedLocalDensity_overlap
    source boundary initial terminal point (field point)

/-- Root-facing Stage-9 action: the source generates its coupling block, so no
coupling table, action receipt, or invariance Boolean is supplied by callers.
-/
def sourceGeneratedIntegratedUnifiedAction
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  integratedUnifiedActionAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart field

theorem sourceGeneratedIntegratedUnifiedAction_chartInvariant
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedUnifiedAction source terminal
        (transportContinuumFieldSection source initial terminal field) =
      sourceGeneratedIntegratedUnifiedAction source initial field :=
  integratedUnifiedActionAtBoundary_chartInvariant source
    (sourceGeneratedUnifiedCouplings source) initial terminal field

def generatedVacuumPointField
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) : StageNineContinuumPointField where
  coframe := source.legacy.coframeAt point
  gravityCurvature := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeCurvature := 0
  gaugeAuxiliary := 0
  scalar := generatedLocalVacuumCoordinates source chart point
  scalarCovariantDerivative := 0
  matter := 0
  matterCovariantDerivative := 0
  conjugateMatter := 0

def generatedVacuumFieldSection
    (source : SmoothUnifiedSource) (chart : StageNineChart) :
    StageNineContinuumFieldSection :=
  generatedVacuumPointField source chart

theorem generatedVacuumPointField_density_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    generatedUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) chart point
      (generatedVacuumPointField source chart point) = 0 := by
  have simplicityDensityZero :
      generatedGravitySimplicityDensity
        (generatedVacuumPointField source chart point) = 0 :=
    generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero _ rfl
  rw [generatedUnifiedLocalDensityAtBoundary, simplicityDensityZero]
  simp [generatedVacuumPointField,
    generatedUnifiedLocalDensityCoreAtBoundary,
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary,
    generatedGravityBFDensity, gravityCoframePairing,
    coframeTwoFormMetricPairing, generatedGaugeSectorBFDensity,
    generatedGaugeTwoFormMetricPairing, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear,
    specialUnitaryLiePairing, hyperchargeLiePairing,
    generatedScalarKineticDensity, scalarCoordinatePairingRe,
    scalarFrameRelativeCovariantDerivative_zero,
    generatedContinuumMatterDensity, generatedContinuumMatterVector,
    matterDualFrameRelative]

theorem generatedVacuumFieldSection_integratedAction_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart) :
    sourceGeneratedIntegratedUnifiedAction source chart
      (generatedVacuumFieldSection source chart) = 0 := by
  simp [sourceGeneratedIntegratedUnifiedAction,
    integratedUnifiedActionAtBoundary,
    generatedVacuumFieldSection, generatedVacuumPointField_density_zero]

def coframeVariationProbePoint : BasePoint :=
  EuclideanSpace.single 2 1

def coframeVariationProbeForm : GaugeTwoForm :=
  fun pair => if pair = 5 then 1 else 0

/-- Negative regression for S9-C readiness: replacing the dynamical
coframe-generated gauge Hodge by the origin/source-background operator loses
an actual shear response. -/
theorem dynamicalCoframeGaugeHodge_cannotBeFrozen :
    coframeGaugeSpacetimeHodgeLinear
          (canonicalPhysicalSource.coframeAt coframeVariationProbePoint)
          coframeVariationProbeForm ≠
      coframeGaugeSpacetimeHodgeLinear
          (canonicalPhysicalSource.coframeAt 0)
          coframeVariationProbeForm := by
  rw [coframeGaugeSpacetimeHodgeLinear_positiveSource,
    coframeGaugeSpacetimeHodgeLinear_positiveSource]
  intro equality
  have componentEquality := congrFun equality 4
  norm_num [positiveGaugeSpacetimeHodge, positiveCoframeTwoFormFrame,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    coframeVariationProbePoint, coframeVariationProbeForm,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    Matrix.cons_val, Matrix.cons_val'] at componentEquality

def quarterTurnBasePoint : BasePoint :=
  EuclideanSpace.single 0 (1 / 2 : ℝ)

theorem positive_generatedTransition_quarterTurn :
    generatedTransition positiveSmoothUnifiedSource 0 1
        quarterTurnBasePoint = hyperchargeQuarterTurn := by
  unfold generatedTransition hyperchargeQuarterTurn quarterTurnBasePoint
  rw [positive_continuousContactRate]
  congr 1
  apply Subtype.ext
  simp only [quarterTurn, Circle.coe_exp, PiLp.single_apply, if_pos]
  norm_num [chartWeight]
  have argumentEquality :
      (Real.pi : ℂ) * (1 / 2 : ℂ) * Complex.I =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [argumentEquality]
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    Complex.exp_pi_div_two_mul_I

/-- Negative chart regression: the chart-zero vacuum cannot simply be copied
to chart one.  The nontrivial generated transition must transport it. -/
theorem untransportedVacuum_badChartGluing_rejected :
    generatedScalarPotential positiveSmoothUnifiedSource 1
      quarterTurnBasePoint
      (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0
        quarterTurnBasePoint) ≠ 0 := by
  intro potentialZero
  have equalsChartOneVacuum :=
    (generatedScalarPotential_eq_zero_iff
      positiveSmoothUnifiedSource 1 quarterTurnBasePoint
      (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0
        quarterTurnBasePoint)).mp potentialZero
  have chartZeroVacuum :
      generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0
          quarterTurnBasePoint =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    rw [generatedLocalVacuumCoordinates, generatedScalarFrame,
      generatedTransition_normalized, scalarCoordinateAction_one]
  have overlap := generatedLocalVacuumCoordinates_overlap
    positiveSmoothUnifiedSource 0 1 quarterTurnBasePoint
  rw [positive_generatedTransition_quarterTurn, chartZeroVacuum] at overlap
  rw [chartZeroVacuum] at equalsChartOneVacuum
  have coordinateFixed :
      scalarCoordinateAction hyperchargeQuarterTurn
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource :=
    (equalsChartOneVacuum.trans overlap).symm
  have baseFixed :
      exteriorBreakingScalarRepresentation hyperchargeQuarterTurn
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
    have pushed := congrArg scalarCoordinateEquiv.symm coordinateFixed
    simpa [scalarCoordinateAction, sourceGeneratedVacuumCoordinates] using pushed
  rw [positive_sourceGeneratedVacuumBase] at baseFixed
  exact finiteGenerationJointBreakingScalar_is_genuinely_broken baseFixed

end

end SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction
