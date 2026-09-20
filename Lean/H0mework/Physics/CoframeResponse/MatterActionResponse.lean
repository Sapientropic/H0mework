import H0mework.Physics.CoframeJets.CoframeFirstJet
import H0mework.Physics.Coframe.CoframeLocalDifferentiability
import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponse
import H0mework.Physics.DualVariation.MatterVariation
import H0mework.Physics.Coframe.IdentityCoframeConjugateMatterTimeResponseActualLift

/-!
# Live-coframe Dirac-dual conjugate-matter action response

The repaired Dirac-dual matter action is first order in the independent
conjugate matter field.  Away from the identity coframe its adjoint temporal
law contains two pieces which the earlier identity-coframe response does not
see:

* the actual inverse-coframe Dirac principal;
* the derivative of the densitized principal `|det e| Pμ(e)`.

This module extracts both pieces from the current coframe first jet and the
authoritative right-chiral action.  The resulting response is source-free in
the same sense as the existing repaired primal response: after fixing the
canonical Stage-9 chart, every coefficient is already present in the current
actual.  No Euler residual, target derivative, branch witness, inverse
certificate, or adjustable normalization enters a constructor.

The temporal-principal and volume inverses are total formulas.  Actual
nondegeneracy and noncharacteristic hypotheses occur only in soundness and
uniqueness theorems.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

open scoped ContDiff Matrix

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Exact finite dual coordinates -/

/-- The coordinate reconstruction used by the existing conjugate-matter
installer is also injective.  Together with
`matterDualOfCoordinates_surjective`, this is the canonical finite dual
equivalence; no Riesz map or extra normalization is chosen. -/
@[simp] theorem matterDualCoordinates_matterDualOfCoordinates
    (coordinates : MatterCoordinateCarrier) :
    matterDualCoordinates (matterDualOfCoordinates coordinates) =
      coordinates := by
  apply PiLp.ext
  intro index
  exact matterDualOfCoordinates_basis_apply coordinates index

theorem matterDualCoordinates_injective :
    Function.Injective matterDualCoordinates := by
  intro first second coordinatesEqual
  calc
    first = matterDualOfCoordinates (matterDualCoordinates first) :=
      (matterDualOfCoordinates_surjective first).symm
    _ = matterDualOfCoordinates (matterDualCoordinates second) := by
      rw [coordinatesEqual]
    _ = second := matterDualOfCoordinates_surjective second

theorem matterDualCoordinates_add
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (first + second) =
      matterDualCoordinates first + matterDualCoordinates second := by
  apply PiLp.ext
  intro index
  rfl

theorem matterDualCoordinates_sub
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (first - second) =
      matterDualCoordinates first - matterDualCoordinates second := by
  apply PiLp.ext
  intro index
  rfl

theorem matterDualCoordinates_smul
    (coefficient : ℂ)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (coefficient • dual) =
      coefficient • matterDualCoordinates dual := by
  apply PiLp.ext
  intro index
  rfl

/-! ## Live principal and densitized momentum carrier -/

/-- The actual inverse-coframe Dirac principal in an arbitrary spacetime
direction. -/
def liveCoframeMatterPrincipal
    (coframe : LorentzianCoframe)
    (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction
    (inverseCoframeDiracGamma
      { coframe := coframe, derivative := 0 } direction)

@[simp] theorem liveCoframeMatterPrincipal_time
    (coframe : LorentzianCoframe) :
    liveCoframeMatterPrincipal coframe
        canonicalLorentzianTimeDirection =
      currentCoframeMatterTemporalPrincipal coframe :=
  rfl

@[simp] theorem liveCoframeMatterPrincipal_one
    (direction : LorentzianIndex) :
    liveCoframeMatterPrincipal (1 : LorentzianCoframe) direction =
      identityCoframeMatterPrincipal direction := by
  unfold liveCoframeMatterPrincipal identityCoframeMatterPrincipal
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by
    rfl]
  rw [inverseCoframeDiracGamma_identity]

/-- Finite coordinates of the complex densitized adjoint momentum
`|det e| λ ∘ Pμ(e)`.  Its two inputs are precisely the coframe and the
independent conjugate-matter coordinates. -/
def liveCoframeDensitizedAdjointMomentumCoordinates
    (direction : LorentzianIndex)
    (joint : LorentzianCoframe × MatterCoordinateCarrier) :
    MatterCoordinateCarrier :=
  matterDualCoordinates
    ((((abs (Matrix.det joint.1) : ℝ) : ℂ)) •
      (matterDualOfCoordinates joint.2).comp
        (liveCoframeMatterPrincipal joint.1 direction))

/-- The current coframe first jet, canonically integrated to the affine germ
owned by that same current. -/
def holonomicLiveCoframeAffineGerm
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint → LorentzianCoframe :=
  affineCoframeFieldOfJet
    (holonomicCoframeFirstJetAt configuration.coframe point)

/-- Contribution of the conjugate-matter spatial derivative to the
densitized adjoint momentum divergence. -/
def holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  ∑ direction : Fin 3,
    matterDualCoordinates
      (((generatedVolumeDensity
          (toContinuumPointField configuration point) : ℂ)) •
        (holonomicConjugateMatterDerivativeDual configuration point
          direction.succ).comp
          (liveCoframeMatterPrincipal
            (configuration.coframe point) direction.succ))

/-- Coframe/density part of one directional momentum derivative.  The
conjugate dual is frozen while the actual current coframe first jet is read
through its canonical affine germ. -/
def holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex) : MatterCoordinateCarrier :=
  fieldDirectionalDerivative
    (fun localPoint =>
      liveCoframeDensitizedAdjointMomentumCoordinates direction
        (holonomicLiveCoframeAffineGerm configuration point localPoint,
          holonomicConjugateMatterCoordinates configuration point))
    0 direction

/-- Sum of the three spatial coframe/density drift terms. -/
def holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  ∑ direction : Fin 3,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates configuration
      point direction.succ

/-- Temporal coframe/density drift.  This is the term absent from the old
identity-coframe adjoint response. -/
def holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  holonomicLiveCoframeDensitizedPrincipalDriftCoordinates configuration point
    canonicalLorentzianTimeDirection

/-! ## Right-chiral algebraic action and known dual -/

/-- General-coframe algebraic operator extracted from the authoritative
Dirac-dual matter variation. -/
def holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  (∑ direction : LorentzianIndex,
      (liveCoframeMatterPrincipal (configuration.coframe point) direction
        ).comp
        (holonomicIdentityCoframeMatterConnectionOperator configuration point
          direction)) +
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))

/-- Densitized algebraic dual `|det e| λ ∘ A(e,ω,A,φ)`. -/
def holonomicDiracDualLiveCoframeAlgebraicDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  ((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℂ)) •
    (configuration.conjugateMatter point).comp
      (holonomicDiracDualLiveCoframeMatterAlgebraicOperator configuration
        point)

/-- Every term in the densitized adjoint equation except the temporal
conjugate derivative. -/
def holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeAlgebraicDual configuration point -
    matterDualOfCoordinates
      (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        configuration point) -
    matterDualOfCoordinates
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates configuration
        point) -
    matterDualOfCoordinates
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates configuration
        point)

/-! ## Branch-free temporal action law -/

/-- Densitized live-coframe adjoint action law. -/
def HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  ((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℂ)) •
      timeDerivative.comp
        (currentCoframeMatterTemporalPrincipal
          (configuration.coframe point)) =
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        configuration point

/-- Exact finite-coordinate seam for the complex densitized adjoint balance.
This is a readout equivalence, not a second equation or a supplied receipt. -/
theorem
    holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff_coordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
          point timeDerivative ↔
      matterDualCoordinates
          (((generatedVolumeDensity
              (toContinuumPointField configuration point) : ℂ)) •
            timeDerivative.comp
              (currentCoframeMatterTemporalPrincipal
                (configuration.coframe point))) =
        matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
            configuration point) := by
  constructor
  · exact fun equality => congrArg matterDualCoordinates equality
  · exact fun equality => matterDualCoordinates_injective equality

/-- The action itself selects the unique live-coframe temporal dual. -/
def holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℂ)⁻¹) •
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
      configuration point).comp
    (currentCoframeMatterTemporalPrincipalInverse
      (configuration.coframe point))

/-- The live adjoint action velocity is determined by the complete local
coframe/connection/scalar/dual-matter first-jet data.  This is an extensional
readout of the action formula; it does not manufacture any of those fields. -/
theorem holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeJet :
      holonomicCoframeFirstJetAt first.coframe firstPoint =
        holonomicCoframeFirstJetAt second.coframe secondPoint)
    (connection :
      first.gravityConnection firstPoint =
        second.gravityConnection secondPoint)
    (gauge :
      first.gaugeConnection firstPoint =
        second.gaugeConnection secondPoint)
    (scalar : first.scalar firstPoint = second.scalar secondPoint)
    (conjugate :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint)
    (conjugateDerivative :
      ∀ direction : LorentzianIndex,
        holonomicConjugateMatterDerivativeDual first firstPoint direction =
          holonomicConjugateMatterDerivativeDual second secondPoint
            direction) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        first firstPoint =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        second secondPoint := by
  have coframe :
      first.coframe firstPoint = second.coframe secondPoint :=
    congrArg PointwiseLorentzianCoframeJet.coframe coframeJet
  have conjugateCoordinates :
      holonomicConjugateMatterCoordinates first firstPoint =
        holonomicConjugateMatterCoordinates second secondPoint := by
    unfold holonomicConjugateMatterCoordinates
    rw [conjugate]
  have volume :
      generatedVolumeDensity (toContinuumPointField first firstPoint) =
        generatedVolumeDensity
          (toContinuumPointField second secondPoint) := by
    unfold generatedVolumeDensity toContinuumPointField
    rw [coframe]
  unfold holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm
  rw [coframe, volume, connection, gauge, scalar, conjugate, coframeJet,
    conjugateCoordinates]
  simp_rw [conjugateDerivative]

theorem holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe point) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
      point
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration point) := by
  have volumeNeReal :
      generatedVolumeDensity
          (toContinuumPointField configuration point) ≠
        0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr nondegenerate
  have volumeNeComplex :
      (generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) ≠ 0 := by
    exact_mod_cast volumeNeReal
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
  apply LinearMap.ext
  intro matter
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [currentCoframeMatterTemporalPrincipalInverse_left
    (configuration.coframe point) noncharacteristic]
  simp [volumeNeComplex]

theorem holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe point) ≠ 0)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
        point first)
    (secondLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
        point second) :
    first = second := by
  have volumeNeReal :
      generatedVolumeDensity
          (toContinuumPointField configuration point) ≠
        0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr nondegenerate
  have volumeNeComplex :
      (generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) ≠ 0 := by
    exact_mod_cast volumeNeReal
  have composedEqual :
      first.comp
          (currentCoframeMatterTemporalPrincipal
            (configuration.coframe point)) =
        second.comp
          (currentCoframeMatterTemporalPrincipal
            (configuration.coframe point)) := by
    apply LinearMap.ext
    intro matter
    have equality := LinearMap.congr_fun (firstLaw.trans secondLaw.symm) matter
    simp only [LinearMap.smul_apply] at equality
    exact mul_left_cancel₀ volumeNeComplex equality
  apply LinearMap.ext
  intro matter
  calc
    first matter =
        first
          (currentCoframeMatterTemporalPrincipal
            (configuration.coframe point)
            (currentCoframeMatterTemporalPrincipalInverse
              (configuration.coframe point) matter)) := by
      rw [currentCoframeMatterTemporalPrincipalInverse_right
        (configuration.coframe point) noncharacteristic]
    _ = second
          (currentCoframeMatterTemporalPrincipal
            (configuration.coframe point)
            (currentCoframeMatterTemporalPrincipalInverse
              (configuration.coframe point) matter)) := by
      exact LinearMap.congr_fun composedEqual
        (currentCoframeMatterTemporalPrincipalInverse
          (configuration.coframe point) matter)
    _ = second matter := by
      rw [currentCoframeMatterTemporalPrincipalInverse_right
        (configuration.coframe point) noncharacteristic]

theorem holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe point) ≠ 0)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
          point candidate ↔
      candidate =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration point := by
  constructor
  · intro candidateLaw
    exact
      holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_unique
        configuration point nondegenerate noncharacteristic candidate
        (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration point)
        candidateLaw
        (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
          configuration point nondegenerate noncharacteristic)
  · rintro rfl
    exact
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
        configuration point nondegenerate noncharacteristic

/-! ## Source-free live-coframe actual lift -/

/-- Raw conjugate-matter first-jet write selected by the live-coframe action
at the canonical Stage-9 origin.  It is a difference of two actual reads,
not an inverted Euler residual. -/
def liveCoframeConjugateMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeConjugateMatterActionVelocity configuration 0 -
    holonomicConjugateMatterDerivativeDual configuration 0
      canonicalLorentzianTimeDirection

/-- Install the action-selected live-coframe temporal response on the same
current actual. -/
def actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installConjugateMatterLinearTimeResponse configuration
    (liveCoframeConjugateMatterTimeResponseWrite configuration)

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).coframe = configuration.coframe :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).gravityConnection = configuration.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).gravityAuxiliary = configuration.gravityAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).gravitySimplicityMultiplier =
        configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).gaugeConnection = configuration.gaugeConnection :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).gaugeAuxiliary = configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).scalar = configuration.scalar :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).matter = configuration.matter :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).conjugateMatter 0 =
        configuration.conjugateMatter 0 :=
  installConjugateMatterLinearTimeResponse_conjugateMatter_origin _ _

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin
    (configuration : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      toContinuumPointField configuration 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  exact
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
      configuration

theorem
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        configuration 0 := by
  unfold holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin,
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe]
  apply Finset.sum_congr rfl
  intro direction _
  unfold actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (liveCoframeConjugateMatterTimeResponseWrite configuration)
      direction.succ]
  have spatialNe :
      direction.succ ≠ canonicalLorentzianTimeDirection := by
    fin_cases direction <;> decide
  simp [spatialNe]

theorem
    holonomicConjugateMatterCoordinates_actionGeneratedDiracDualLiveCoframe_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicConjugateMatterCoordinates
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicConjugateMatterCoordinates configuration 0 := by
  unfold holonomicConjugateMatterCoordinates
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]

theorem
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 direction =
      holonomicLiveCoframeDensitizedPrincipalDriftCoordinates configuration 0
        direction := by
  unfold holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe,
    holonomicConjugateMatterCoordinates_actionGeneratedDiracDualLiveCoframe_origin]

theorem
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicLiveCoframeSpatialPrincipalDriftCoordinates configuration 0 := by
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  apply Finset.sum_congr rfl
  intro direction _
  exact
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_actionGenerated_origin
      configuration direction.succ

theorem
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicLiveCoframeTemporalPrincipalDriftCoordinates configuration 0 :=
  holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_actionGenerated_origin
    configuration canonicalLorentzianTimeDirection

theorem
    holonomicIdentityCoframeMatterConnectionOperator_actionGeneratedDiracDualLiveCoframe_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicIdentityCoframeMatterConnectionOperator
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeMatterConnectionOperator configuration 0 := by
  funext direction
  simp [holonomicIdentityCoframeMatterConnectionOperator]

theorem
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeMatterAlgebraicOperator configuration 0 := by
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe,
    holonomicIdentityCoframeMatterConnectionOperator_actionGeneratedDiracDualLiveCoframe_origin,
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_scalar]

theorem
    holonomicDiracDualLiveCoframeAlgebraicDual_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeAlgebraicDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeAlgebraicDual configuration 0 := by
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin,
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator_actionGenerated_origin]

theorem
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        configuration 0 := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
  rw [
    holonomicDiracDualLiveCoframeAlgebraicDual_actionGenerated_origin,
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates_actionGenerated_origin
      configuration smooth,
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates_actionGenerated_origin,
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates_actionGenerated_origin]

theorem
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_actionGenerated_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration 0 := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin,
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe,
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual_actionGenerated_origin
      configuration smooth]

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_timeDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration 0 := by
  unfold actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (liveCoframeConjugateMatterTimeResponseWrite configuration)
      canonicalLorentzianTimeDirection]
  simp [liveCoframeConjugateMatterTimeResponseWrite]

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_recomputes_timeDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 := by
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_timeDerivative
      configuration smooth,
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_actionGenerated_origin
      configuration smooth]

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : Matrix.det (configuration.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_recomputes_timeDerivative
      configuration smooth]
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
  · simpa using nondegenerate
  · simpa using noncharacteristic

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).Smooth :=
  installConjugateMatterLinearTimeResponse_smooth _ smooth _

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      configuration).Nondegenerate :=
  installConjugateMatterLinearTimeResponse_nondegenerate _ nondegenerate _

/-- Faithful zero fiber of the live action write.  The generated actual is
unchanged exactly when the current temporal first jet already equals the
unique action-selected one. -/
theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration =
        configuration ↔
      holonomicConjugateMatterDerivativeDual configuration 0
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration 0 := by
  rw [actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual,
    installConjugateMatterLinearTimeResponse_eq_iff]
  change
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity configuration
          0 -
          holonomicConjugateMatterDerivativeDual configuration 0
            canonicalLorentzianTimeDirection =
        0 ↔
      holonomicConjugateMatterDerivativeDual configuration 0
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration 0
  constructor
  · intro responseZero
    exact (sub_eq_zero.mp responseZero).symm
  · intro alreadyGenerated
    exact sub_eq_zero.mpr alreadyGenerated.symm

/-! ## Complete identity-first-jet compatibility normal form -/

/-- Right-chiral identity-coframe algebraic normal form.  It is stated in
terms of the canonical identity principal so the live principal specializes
without importing the repaired response operator that will consume this
module. -/
def holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  (∑ direction : LorentzianIndex,
      (identityCoframeMatterPrincipal direction).comp
        (holonomicIdentityCoframeMatterConnectionOperator configuration point
          direction)) +
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))

/-- Right-chiral identity-coframe known adjoint dual. -/
def holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (configuration.conjugateMatter point).comp
      (holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
        configuration point) -
    holonomicIdentityCoframeConjugateMatterSpatialTransport configuration point

/-- Right-chiral identity-coframe action velocity in the normal form consumed
by the repaired matter operator. -/
def holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
      configuration point).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

/-- The identity-first-jet adjoint velocity is determined by the connection,
scalar, adjoint value, and its three spatial derivatives.  The temporal
adjoint derivative is deliberately absent from this extensional mouth. -/
theorem
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity_eq_of_pointData
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (connection :
      first.gravityConnection firstPoint =
        second.gravityConnection secondPoint)
    (gauge :
      first.gaugeConnection firstPoint =
        second.gaugeConnection secondPoint)
    (scalar : first.scalar firstPoint = second.scalar secondPoint)
    (conjugate :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint)
    (spatialDerivative : ∀ direction : Fin 3,
      holonomicConjugateMatterDerivativeDual first firstPoint direction.succ =
        holonomicConjugateMatterDerivativeDual second secondPoint
          direction.succ) :
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        first firstPoint =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        second secondPoint := by
  unfold
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  rw [connection, gauge, scalar, conjugate]
  simp_rw [spatialDerivative]

def HolonomicDiracDualRightChiralIdentityCoframeConjugateMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  timeDerivative.comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) =
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
      configuration point

def diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
      configuration 0 -
    holonomicConjugateMatterDerivativeDual configuration 0
      canonicalLorentzianTimeDirection

def actionGeneratedDiracDualRightChiralIdentityCoframeConjugateMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installConjugateMatterLinearTimeResponse configuration
    (diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
      configuration)

theorem coframe_eq_one_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    configuration.coframe point = 1 := by
  have coframeEquality := congrArg
    (fun jet : PointwiseLorentzianCoframeJet => jet.coframe) firstJet
  simpa [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry] using
    coframeEquality

theorem generatedVolumeDensity_eq_one_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    generatedVolumeDensity (toContinuumPointField configuration point) =
      1 := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  simp [generatedVolumeDensity, toContinuumPointField, coframeOne]

theorem currentCoframeMatterTemporalPrincipal_one_eq_identity :
    currentCoframeMatterTemporalPrincipal (1 : LorentzianCoframe) =
      identityCoframeMatterPrincipal canonicalLorentzianTimeDirection := by
  apply LinearMap.ext
  intro matter
  rw [currentCoframeMatterTemporalPrincipal_one]
  rfl

theorem currentCoframeMatterTemporalPrincipalInverse_one_eq_identity :
    currentCoframeMatterTemporalPrincipalInverse (1 : LorentzianCoframe) =
      identityCoframeMatterPrincipal canonicalLorentzianTimeDirection := by
  apply LinearMap.ext
  intro matter
  rw [currentCoframeMatterTemporalPrincipalInverse_one]
  rfl

@[simp] theorem affineCoframeFieldOfJet_identityCoframeMatterGeometry
    (point : BasePoint) :
    affineCoframeFieldOfJet identityCoframeMatterGeometry point =
      (1 : LorentzianCoframe) := by
  ext internal coordinate
  simp [affineCoframeFieldOfJet, coframeJetAffineComponentLinear,
    identityCoframeMatterGeometry]

theorem
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates configuration point
        direction =
      0 := by
  unfold holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm
  rw [firstJet]
  simp only [affineCoframeFieldOfJet_identityCoframeMatterGeometry]
  simp [fieldDirectionalDerivative]

theorem
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates configuration point =
      0 := by
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  simp_rw [
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
      configuration point _ firstJet]
  simp

theorem
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates configuration point =
      0 := by
  exact
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
      configuration point canonicalLorentzianTimeDirection firstJet

theorem
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator configuration point =
      holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
        configuration point := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
  rw [coframeOne]
  simp_rw [liveCoframeMatterPrincipal_one]

theorem
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates_eq_identity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        configuration point =
      matterDualCoordinates
        (holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
          point) := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  have volumeOne :=
    generatedVolumeDensity_eq_one_of_identity_firstJet configuration point
      firstJet
  unfold holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  rw [coframeOne, volumeOne]
  apply PiLp.ext
  intro index
  simp [liveCoframeMatterPrincipal_one, matterDualCoordinates]

theorem
    holonomicDiracDualLiveCoframeAlgebraicDual_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicDiracDualLiveCoframeAlgebraicDual configuration point =
      (configuration.conjugateMatter point).comp
        (holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
          configuration point) := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  have volumeOne :=
    generatedVolumeDensity_eq_one_of_identity_firstJet configuration point
      firstJet
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
  rw [
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator_eq_rightChiralIdentity_of_firstJet
      configuration point firstJet,
    volumeOne]
  simp

theorem
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        configuration point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
        configuration point := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
  rw [
    holonomicDiracDualLiveCoframeAlgebraicDual_eq_rightChiralIdentity_of_firstJet
      configuration point firstJet,
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates_eq_identity_of_firstJet
      configuration point firstJet,
    matterDualOfCoordinates_surjective,
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
      configuration point firstJet,
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates_eq_zero_of_identity_firstJet
      configuration point firstJet]
  simp

theorem
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        configuration point := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  have volumeOne :=
    generatedVolumeDensity_eq_one_of_identity_firstJet configuration point
      firstJet
  unfold holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
  rw [
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual_eq_rightChiralIdentity_of_firstJet
      configuration point firstJet,
    coframeOne,
    volumeOne,
    currentCoframeMatterTemporalPrincipalInverse_one_eq_identity]
  simp

theorem
    holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
          point timeDerivative ↔
      HolonomicDiracDualRightChiralIdentityCoframeConjugateMatterTimeActionLaw
        configuration point timeDerivative := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  have volumeOne :=
    generatedVolumeDensity_eq_one_of_identity_firstJet configuration point
      firstJet
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    HolonomicDiracDualRightChiralIdentityCoframeConjugateMatterTimeActionLaw
  rw [
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual_eq_rightChiralIdentity_of_firstJet
      configuration point firstJet,
    coframeOne,
    volumeOne,
    currentCoframeMatterTemporalPrincipal_one_eq_identity]
  simp

theorem
    liveCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        identityCoframeMatterGeometry) :
    liveCoframeConjugateMatterTimeResponseWrite configuration =
      diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
        configuration := by
  unfold liveCoframeConjugateMatterTimeResponseWrite
    diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
  rw [
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
      configuration 0 firstJet]

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_rightChiralIdentity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        identityCoframeMatterGeometry) :
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
        configuration =
      actionGeneratedDiracDualRightChiralIdentityCoframeConjugateMatterTimeResponseActual
        configuration := by
  unfold actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    actionGeneratedDiracDualRightChiralIdentityCoframeConjugateMatterTimeResponseActual
  rw [
    liveCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity_of_firstJet
      configuration firstJet]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
