import H0mework.Physics.Holonomic.HolonomicIdentityCoframeConjugateMatterActionResponse
import H0mework.Physics.MatterJets.MatterActionTemporalFirstGermResponse
import H0mework.Physics.Matter.MatterPointwiseEquation

/-!
# Identity-coframe adjoint action acceptance

This module is a downstream readout.  It proves that, on a smooth global
identity-coframe configuration, the holonomic dual action law is exactly the
pointwise adjoint Euler--Lagrange equation.

The action response is generated in
`StageNineHolonomicIdentityCoframeConjugateMatterActionResponse`; nothing in
this file constructs or repairs a field from an Euler--Lagrange residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Dependency-light directional transport -/

/-- If two scalar fields differ along one coordinate axis only by a scalar
factor whose value is one and whose first derivative vanishes at the origin,
then their directional derivatives agree there.  This is a calculus
transporter; it neither constructs a field nor assumes an Euler--Lagrange
receipt. -/
theorem fieldDirectionalDerivative_eq_of_axis_factor_at_origin
    (current comparison : BasePoint → ℝ)
    (direction : LorentzianIndex)
    (factor : ℝ → ℝ)
    (currentDifferentiable : DifferentiableAt ℝ current 0)
    (comparisonDifferentiable : DifferentiableAt ℝ comparison 0)
    (factorDerivative : HasDerivAt factor 0 0)
    (factorOrigin : factor 0 = 1)
    (axisEquality : ∀ parameter : ℝ,
      current (parameter • coordinateDirection direction) =
        factor parameter *
          comparison (parameter • coordinateDirection direction)) :
    fieldDirectionalDerivative current 0 direction =
      fieldDirectionalDerivative comparison 0 direction := by
  let line :=
    fun parameter : ℝ =>
      parameter • coordinateDirection direction
  have lineDerivative :
      HasDerivAt line (coordinateDirection direction) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection direction)
  have currentOuter :
      HasFDerivAt current (fderiv ℝ current 0) (line 0) := by
    simpa [line] using currentDifferentiable.hasFDerivAt
  have comparisonOuter :
      HasFDerivAt comparison (fderiv ℝ comparison 0) (line 0) := by
    simpa [line] using comparisonDifferentiable.hasFDerivAt
  have currentComposition :
      HasDerivAt (current ∘ line)
        ((fderiv ℝ current 0) (coordinateDirection direction)) 0 :=
    currentOuter.comp_hasDerivAt 0 lineDerivative
  have comparisonComposition :
      HasDerivAt (comparison ∘ line)
        ((fderiv ℝ comparison 0) (coordinateDirection direction)) 0 :=
    comparisonOuter.comp_hasDerivAt 0 lineDerivative
  have productDerivative := factorDerivative.mul comparisonComposition
  have productDerivative' :
      HasDerivAt
        (fun parameter =>
          factor parameter * (comparison ∘ line) parameter)
        ((fderiv ℝ comparison 0) (coordinateDirection direction)) 0 := by
    convert! productDerivative using 1
    all_goals simp [line, factorOrigin]
  have compositionEquality :
      current ∘ line =
        fun parameter =>
          factor parameter * (comparison ∘ line) parameter := by
    funext parameter
    simpa only [Function.comp_apply, line] using axisEquality parameter
  rw [compositionEquality] at currentComposition
  have derivativeEquality :=
    currentComposition.unique productDerivative'
  unfold fieldDirectionalDerivative
  exact derivativeEquality

/-! ## Proof-only identity-coframe comparison -/

/-- Replace only the coframe by the constant identity field.  This carrier is
used to read an already generated action law; it is never a physical output. -/
def identityCoframeComparison
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with coframe := fun _ => 1 }

@[simp] theorem identityCoframeComparison_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).coframe =
      fun _ => 1 :=
  rfl

@[simp] theorem identityCoframeComparison_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem identityCoframeComparison_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem identityCoframeComparison_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem identityCoframeComparison_matter
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).matter =
      configuration.matter :=
  rfl

@[simp] theorem identityCoframeComparison_conjugateMatter
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

theorem identityCoframeComparison_hasIdentityCoframe
    (configuration : StageNineHolonomicConfiguration) :
    HasIdentityCoframe (identityCoframeComparison configuration) := by
  funext point
  rfl

theorem identityCoframeComparison_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (identityCoframeComparison configuration).Smooth := by
  rcases smooth with
    ⟨_coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨fun _ _ => contDiff_const, gravityConnectionSmooth,
      gravityAuxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem identityCoframeComparison_nondegenerate
    (configuration : StageNineHolonomicConfiguration) :
    (identityCoframeComparison configuration).Nondegenerate := by
  intro point
  simp [identityCoframeComparison]

theorem identityCoframeComparison_inverseCoframeDiracGamma
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := (identityCoframeComparison configuration).coframe point
          derivative := 0 }
        direction =
      diracGamma direction := by
  change
    inverseCoframeDiracGamma identityCoframeMatterGeometry direction =
      diracGamma direction
  exact inverseCoframeDiracGamma_identity direction

theorem toContinuumPointField_identityCoframeComparison_eq_of_coframe_eq_one
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1) :
    toContinuumPointField configuration point =
      toContinuumPointField (identityCoframeComparison configuration) point := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  exact coframeOne

theorem identityCoframeComparison_timeActionLaw_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
          (identityCoframeComparison configuration) point timeDerivative ↔
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw
        configuration point timeDerivative :=
  Iff.rfl

def matterDualCoordinateEvaluation
    (matter : DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier →L[ℂ] ℂ :=
  ∑ index : MatterCoordinateIndex,
    (matterCoordinateEquiv matter index) •
      ((ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap)

@[simp] theorem matterDualCoordinateEvaluation_apply
    (matter : DiracExteriorMatterCarrier)
    (coordinates : MatterCoordinateCarrier) :
    matterDualCoordinateEvaluation matter coordinates =
      matterDualOfCoordinates coordinates matter := by
  simp [matterDualCoordinateEvaluation, matterDualOfCoordinates_apply]

theorem holonomicConjugateMatterDerivativeDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    holonomicConjugateMatterDerivativeDual configuration point direction
        matter =
      fieldDirectionalDerivative
        (fun candidate => configuration.conjugateMatter candidate matter)
        point direction := by
  have coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point :=
    (holonomicConjugateMatterCoordinates_contDiff configuration smooth)
      |>.differentiable (by simp) |>.differentiableAt
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => configuration.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation (holonomicConjugateMatterCoordinates configuration
            candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate matter =
      matterDualCoordinateEvaluation matter
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have derivative := evaluation.hasFDerivAt.comp point
    coordinateDifferentiable.hasFDerivAt
  rw [evaluationIdentity]
  unfold fieldDirectionalDerivative
  change
    holonomicConjugateMatterDerivativeDual configuration point direction
          matter =
      fderiv ℝ
          (evaluation ∘ holonomicConjugateMatterCoordinates configuration)
          point (coordinateDirection direction)
  rw [derivative.fderiv]
  change
    matterDualOfCoordinates
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction)) matter =
      matterDualCoordinateEvaluation matter
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction))
  rw [matterDualCoordinateEvaluation_apply]

/-- Point-local form of `holonomicConjugateMatterDerivativeDual_apply`.
Only differentiability of the adjoint coordinates at the occurrence is
needed for this readout; no unrelated field regularity is consumed. -/
theorem holonomicConjugateMatterDerivativeDual_apply_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point) :
    holonomicConjugateMatterDerivativeDual configuration point direction
        matter =
      fieldDirectionalDerivative
        (fun candidate => configuration.conjugateMatter candidate matter)
        point direction := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => configuration.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation
            (holonomicConjugateMatterCoordinates configuration candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate matter =
      matterDualCoordinateEvaluation matter
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have derivative := evaluation.hasFDerivAt.comp point
    coordinateDifferentiable.hasFDerivAt
  rw [evaluationIdentity]
  unfold fieldDirectionalDerivative
  change
    holonomicConjugateMatterDerivativeDual configuration point direction
          matter =
      fderiv ℝ
          (evaluation ∘ holonomicConjugateMatterCoordinates configuration)
          point (coordinateDirection direction)
  rw [derivative.fderiv]
  change
    matterDualOfCoordinates
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction)) matter =
      matterDualCoordinateEvaluation matter
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction))
  rw [matterDualCoordinateEvaluation_apply]

theorem holonomicConjugateMatterDerivativeDual_apply_re
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fieldDirectionalDerivative
        (fun candidate => (configuration.conjugateMatter candidate matter).re)
        point direction := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => configuration.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation (holonomicConjugateMatterCoordinates configuration
            candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate matter =
      matterDualCoordinateEvaluation matter
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have complexSmooth : ContDiff ℝ ∞ (fun candidate =>
      configuration.conjugateMatter candidate matter) := by
    rw [evaluationIdentity]
    exact evaluation.contDiff.comp
      (holonomicConjugateMatterCoordinates_contDiff configuration smooth)
  have complexDifferentiable : DifferentiableAt ℝ (fun candidate =>
      configuration.conjugateMatter candidate matter) point :=
    complexSmooth.differentiable (by simp) |>.differentiableAt
  have realDerivative := Complex.reCLM.hasFDerivAt.comp point
    complexDifferentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fderiv ℝ
          (Complex.reCLM ∘ fun candidate =>
            configuration.conjugateMatter candidate matter)
          point (coordinateDirection direction)
  rw [realDerivative.fderiv]
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
      matter).re =
      (fderiv ℝ (fun candidate =>
          configuration.conjugateMatter candidate matter) point
        (coordinateDirection direction)).re
  rw [holonomicConjugateMatterDerivativeDual_apply configuration smooth]
  rfl

/-- Point-local real-part form of the adjoint derivative readout. -/
theorem holonomicConjugateMatterDerivativeDual_apply_re_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point) :
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fieldDirectionalDerivative
        (fun candidate => (configuration.conjugateMatter candidate matter).re)
        point direction := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => configuration.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation
            (holonomicConjugateMatterCoordinates configuration candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate matter =
      matterDualCoordinateEvaluation matter
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have complexDifferentiable : DifferentiableAt ℝ
      (fun candidate => configuration.conjugateMatter candidate matter)
      point := by
    rw [evaluationIdentity]
    exact evaluation.differentiableAt.comp point coordinateDifferentiable
  have realDerivative := Complex.reCLM.hasFDerivAt.comp point
    complexDifferentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fderiv ℝ
          (Complex.reCLM ∘ fun candidate =>
            configuration.conjugateMatter candidate matter)
          point (coordinateDirection direction)
  rw [realDerivative.fderiv]
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
      matter).re =
      (fderiv ℝ (fun candidate =>
          configuration.conjugateMatter candidate matter) point
        (coordinateDirection direction)).re
  rw [holonomicConjugateMatterDerivativeDual_apply_of_differentiableAt
    configuration point direction matter coordinateDifferentiable]
  rfl

theorem holonomicIdentityCoframeMatterAlgebraicVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterAlgebraicVariationVector source configuration direction point =
      holonomicIdentityCoframeMatterAlgebraicOperator configuration point
        (matterCoordinateEquiv.symm direction) := by
  unfold matterAlgebraicVariationVector matterFieldVariationVector
    holonomicIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
    identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]
  unfold holonomicMatterVariationAlgebraicDirection
  rfl

theorem holonomicIdentityCoframeMatterAlgebraicCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterAlgebraicDirectionalCoefficient source configuration direction
        point =
      (configuration.conjugateMatter point
        (holonomicIdentityCoframeMatterAlgebraicOperator configuration point
          (matterCoordinateEquiv.symm direction))).re := by
  unfold matterAlgebraicDirectionalCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [Matrix.det_one, abs_one, one_mul,
    holonomicIdentityCoframeMatterAlgebraicVector source configuration
      identityCoframe]

theorem holonomicIdentityCoframeMatterDifferentialMomentum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source configuration direction
        derivativeDirection =
      fun point =>
        (configuration.conjugateMatter point
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
    identityCoframeMatterGeometry by rfl]
  rw [inverseCoframeDiracGamma_identity]
  simp [identityCoframeMatterPrincipal]

theorem holonomicIdentityCoframeMatterMomentumDivergence
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterDifferentialMomentumDivergence source configuration direction
        point =
      ∑ derivativeDirection : LorentzianIndex,
        (holonomicConjugateMatterDerivativeDual configuration point
          derivativeDirection
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [holonomicIdentityCoframeMatterDifferentialMomentum source configuration
    identityCoframe direction derivativeDirection]
  exact (holonomicConjugateMatterDerivativeDual_apply_re configuration smooth
    point derivativeDirection
    (identityCoframeMatterPrincipal derivativeDirection
      (matterCoordinateEquiv.symm direction))).symm

/-- The identity-coframe momentum-divergence formula is point-local in the
adjoint field.  This version is the exact calculus mouth used when a generated
actual is known only through its local first jet. -/
theorem
    holonomicIdentityCoframeMatterMomentumDivergence_of_differentiableAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source configuration direction
        point =
      ∑ derivativeDirection : LorentzianIndex,
        (holonomicConjugateMatterDerivativeDual configuration point
          derivativeDirection
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [holonomicIdentityCoframeMatterDifferentialMomentum source configuration
    identityCoframe direction derivativeDirection]
  exact
    (holonomicConjugateMatterDerivativeDual_apply_re_of_differentiableAt
      configuration point derivativeDirection
      (identityCoframeMatterPrincipal derivativeDirection
        (matterCoordinateEquiv.symm direction))
      coordinateDifferentiable).symm

def holonomicIdentityCoframeConjugateMatterActionResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicIdentityCoframeConjugateMatterKnownDual configuration point -
    (holonomicConjugateMatterDerivativeDual configuration point
      canonicalLorentzianTimeDirection).comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

theorem holonomicIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterEulerLagrangeDirectionalCoefficient source configuration direction
        point =
      (holonomicIdentityCoframeConjugateMatterActionResidual configuration
        point (matterCoordinateEquiv.symm direction)).re := by
  rw [show
    matterEulerLagrangeDirectionalCoefficient source configuration direction
        point =
      matterAlgebraicDirectionalCoefficient source configuration direction
          point -
        matterDifferentialMomentumDivergence source configuration direction
          point by rfl]
  rw [holonomicIdentityCoframeMatterAlgebraicCoefficient source configuration
      identityCoframe,
    holonomicIdentityCoframeMatterMomentumDivergence source configuration
      smooth identityCoframe]
  unfold holonomicIdentityCoframeConjugateMatterActionResidual
    holonomicIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    Complex.sub_re]
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [Complex.add_re, canonicalLorentzianTimeDirection]
  simp
  ring

theorem holonomicIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (point : BasePoint)
    (actionLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection))
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient source configuration direction
        point =
      0 := by
  rw [holonomicIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
    source configuration smooth identityCoframe]
  have residualZero :
      holonomicIdentityCoframeConjugateMatterActionResidual configuration
          point =
        0 := by
    apply LinearMap.ext
    intro matter
    have lawAt := LinearMap.congr_fun actionLaw matter
    unfold
      holonomicIdentityCoframeConjugateMatterActionResidual
      holonomicIdentityCoframeConjugateMatterKnownDual
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at lawAt
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [← lawAt]
    simp
  rw [residualZero]
  rfl

end
end
  SaturationMonoid.PhysicsCore.StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
