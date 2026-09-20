import H0mework.Physics.GravitySource.ResidualTransportIteration
import H0mework.Physics.Source.GeneratedPartialPrimitiveCarrier
import H0mework.Physics.Geometry.JointShellZeroFiber

/-!
# S9-C3h5: downstream gravity-coordinate lift of the residual orbit

C3h4 first constructs `r_(n+1)=K r_n` entirely on the existing residual
carrier.  This module stays downstream: the `n`-th already-derived curvature
obligation generates a normalized affine connection germ, and its actual
origin gravity residual is proved to be exactly `r_n`.  The explicit
commuting theorem is therefore `R_B(U_(n+1)) = K R_B(U_n)`; no configuration
delta defines `K`.

The indexed germs reuse the existing six-field partial-carrier type, recover
C3h1 at `n=1`, remain nonterminal at every finite step, and converge in the
ordinary componentwise/product topology to a unique canonical limit field.
That limit is an internally derived downstream realization, not a source
field, supplied target, full configuration producer, or stationarity receipt.

On extensions of the limit partial carrier, the three current algebraic
coordinates vanish at the origin.  The complete pointwise joint residual is
then exactly its six still-open Euler--Lagrange channels.  Away-from-origin
constraint propagation, full joint transport, current Spin/frame naturality,
global extension, finite action, and simultaneous stationarity all remain
open; Lorentz skewness and Bianchi do not replace those gates.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift

open Filter
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceGravityMouthSpinOrbitCarrier
open StageNinePositiveSourceGravityMouthTransportCurvature
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open SU7MotherGaugeTheory
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The target is named only after C3h4 proves it is the unique limit of the
existing curvature-obligation sequence. -/
def positiveSourceGravityMouthResidualLimitCurvature : PhysicalBivector :=
  positiveSourceGravityMouthConstitutiveCurvature

/-- No caller can choose a different limit branch. -/
theorem positiveSourceGravityMouthCurvatureObligation_tendsto_iff
    (candidate : PhysicalBivector) :
    Tendsto positiveSourceGravityMouthIteratedCurvatureObligation atTop
        (nhds candidate) ↔
      candidate = positiveSourceGravityMouthResidualLimitCurvature := by
  constructor
  · intro limitLaw
    exact positiveSourceGravityMouthIteratedCurvatureObligation_limit_unique
      candidate limitLaw
  · intro candidateEquality
    rw [candidateEquality]
    exact tendsto_positiveSourceGravityMouthIteratedCurvatureObligation

/-! ## Downstream gravity-coordinate lift of the whole residual orbit -/

/-- The `n`-th primitive connection germ is generated from the `n`-th
already-derived curvature obligation.  This is downstream of `K`; it neither
defines `K` nor accepts a target from a caller. -/
def positiveSourceGravityMouthIteratedConnectionField
    (n : ℕ) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    positiveSourceGravityMouthOriginConnectionValue
    (positiveSourceGravityMouthIteratedCurvatureObligation n)

@[simp] theorem positiveSourceGravityMouthIteratedConnectionField_origin
    (n : ℕ) :
    positiveSourceGravityMouthIteratedConnectionField n 0 =
      positiveSourceGravityMouthOriginConnectionValue :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem positiveSourceGravityMouthIteratedConnectionField_smooth
    (n : ℕ) :
    StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm.SmoothLorentzConnectionField
      (positiveSourceGravityMouthIteratedConnectionField n) :=
  normalizedAffineLorentzConnectionField_smooth _ _

theorem positiveSourceGravityMouthIteratedConnectionField_lorentzSkew
    (n : ℕ) (point : BasePoint) :
    LorentzSkew (positiveSourceGravityMouthIteratedConnectionField n point) := by
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (positive_generatedLorentzConnection_lorentzSkew 0) point

theorem positiveSourceGravityMouthIteratedConnectionField_origin_tetradCompatible
    (n : ℕ) :
    TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      (positiveSourceGravityMouthIteratedConnectionField n 0) := by
  rw [positiveSourceGravityMouthIteratedConnectionField_origin]
  exact positive_generatedLorentzConnection_tetradCompatible 0

/-- Indexed orbit in the existing six-field partial-carrier type.  No missing
multiplier, matter, or dual field is manufactured. -/
def positiveSourceGravityMouthIteratedPartialPrimitiveCarrier
    (n : ℕ) : StageNinePartialPrimitiveCarrier :=
  { positiveSourceStageNinePartialPrimitiveCarrier with
    gravityConnection := positiveSourceGravityMouthIteratedConnectionField n }

theorem positiveSourceGravityMouthIteratedPartialPrimitiveCarrier_preserves_otherFields
    (n : ℕ) :
    (positiveSourceGravityMouthIteratedPartialPrimitiveCarrier n).coframe =
        positiveSourceStageNinePartialPrimitiveCarrier.coframe ∧
      (positiveSourceGravityMouthIteratedPartialPrimitiveCarrier
        n).gravityAuxiliary =
          positiveSourceStageNinePartialPrimitiveCarrier.gravityAuxiliary ∧
      (positiveSourceGravityMouthIteratedPartialPrimitiveCarrier
        n).gaugeConnection =
          positiveSourceStageNinePartialPrimitiveCarrier.gaugeConnection ∧
      (positiveSourceGravityMouthIteratedPartialPrimitiveCarrier
        n).gaugeAuxiliary =
          positiveSourceStageNinePartialPrimitiveCarrier.gaugeAuxiliary ∧
      (positiveSourceGravityMouthIteratedPartialPrimitiveCarrier n).scalar =
        positiveSourceStageNinePartialPrimitiveCarrier.scalar := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def installPositiveSourceGravityMouthIteratedConnection
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection := positiveSourceGravityMouthIteratedConnectionField n }

/-- Actual curvature realizes every residual-orbit obligation, not only its
first or limiting member. -/
theorem installPositiveSourceGravityMouthIteratedConnection_curvature_origin
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (installPositiveSourceGravityMouthIteratedConnection n configuration) 0 =
      positiveSourceGravityMouthIteratedCurvatureObligation n := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        positiveSourceGravityMouthOriginConnectionValue
        (positiveSourceGravityMouthIteratedCurvatureObligation n)) 0 =
    positiveSourceGravityMouthIteratedCurvatureObligation n
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-- The first lifted germ is definitionally the already audited C3g7c germ. -/
theorem positiveSourceGravityMouthIteratedConnectionField_one :
    positiveSourceGravityMouthIteratedConnectionField 1 =
      positiveSourceGravityMouthNormalizedAffineConnectionField := by
  unfold positiveSourceGravityMouthIteratedConnectionField
    positiveSourceGravityMouthNormalizedAffineConnectionField
  rw [positiveSourceGravityMouthIteratedCurvatureObligation_one]

/-- The first finite member is exactly C3h1, so the indexed orbit extends the
existing checkpoint rather than replacing its lineage. -/
theorem positiveSourceGravityMouthIteratedPartialPrimitiveCarrier_one :
    positiveSourceGravityMouthIteratedPartialPrimitiveCarrier 1 =
      positiveSourceStageNinePartialPrimitiveCarrier := by
  unfold positiveSourceGravityMouthIteratedPartialPrimitiveCarrier
  rw [positiveSourceGravityMouthIteratedConnectionField_one,
    ← positive_partialGravityConnection_eq_existingProducer]

/-- Source admission stays separate from the orbit construction.  The orbit
uses the same P506/L0 source lineage and endpoint 11 as C3h1; no Factor
atomhood Boolean or certificate is inserted into a physical datum. -/
theorem positiveGravityMouthResidualOrbit_exactLineage_endpointAdmission :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 :=
  positive_partialPrimitiveProducer_exactLineage_endpointAdmission

/-- Actual gravity-auxiliary readout commutes with the residual transport
orbit.  This is deliberately one coordinate, not a claim that all nine joint
residual channels are transported by this one-field installer. -/
theorem installPositiveSourceGravityMouthIteratedConnection_gravityResidual_origin
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthIteratedConnection n configuration)
        0).gravityAuxiliary =
      (positiveSourceGravityMouthResidualIterate n : PhysicalBivector) := by
  rw [currentGravityAuxiliaryProjection_eq_gravityMouthResidual
    positiveSmoothUnifiedSource
    (installPositiveSourceGravityMouthIteratedConnection n configuration) 0
    (by simpa [installPositiveSourceGravityMouthIteratedConnection] using
      simplicityMouth)]
  unfold stageNineGravityMouthResidualAt
  rw [installPositiveSourceGravityMouthIteratedConnection_curvature_origin]
  unfold PreservesPositiveSourceCoframeAtOrigin at preservesCoframe
  change
    positiveSourceGravityMouthIteratedCurvatureObligation n -
        gravityInternalDualEquiv
          (physicalIIPlusBivector (configuration.coframe 0)) = _
  rw [preservesCoframe]
  rw [positiveSourceGravityMouthIteratedCurvatureObligation]
  unfold positiveSourceGravityMouthConstitutiveCurvature
  abel

/-- A genuine downstream lift cannot turn a finite residual step into exact
closure. -/
theorem installPositiveSourceGravityMouthIteratedConnection_gravityResidual_ne_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthIteratedConnection n configuration)
        0).gravityAuxiliary ≠ 0 := by
  rw [installPositiveSourceGravityMouthIteratedConnection_gravityResidual_origin
    n configuration preservesCoframe simplicityMouth]
  intro ambientZero
  apply positiveSourceGravityMouthResidualIterate_ne_zero n
  apply Subtype.ext
  exact ambientZero

/-- Explicit downstream commuting square for the actual gravity readout:
the connection-germ successor realizes exactly the same `K` step already
defined on residuals. -/
theorem installPositiveSourceGravityMouthIteratedConnection_gravityResidual_succ
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthIteratedConnection (n + 1)
          configuration) 0).gravityAuxiliary =
      StageNinePositiveSourceGravityMouthConnectionLiftNoGo.positiveSourceGravityMouthAmbientKeep
        ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (installPositiveSourceGravityMouthIteratedConnection n configuration)
          0).gravityAuxiliary) := by
  rw [installPositiveSourceGravityMouthIteratedConnection_gravityResidual_origin
      (n + 1) configuration preservesCoframe simplicityMouth,
    installPositiveSourceGravityMouthIteratedConnection_gravityResidual_origin
      n configuration preservesCoframe simplicityMouth,
    positiveSourceGravityMouthResidualIterate_succ]
  exact StageNinePositiveSourceGravityMouthConnectionLiftNoGo.positiveSourceGravityMouthSpinOrbitResponsibilityKeep_coe
    (positiveSourceGravityMouthResidualIterate n)

/-- Finite downstream lifts therefore remain outside even the origin
pointwise joint zero fiber. -/
theorem installPositiveSourceGravityMouthIteratedConnection_not_onJointZeroFiber_origin
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    ¬ OnCurrentPointwiseJointShellZeroFiber positiveSmoothUnifiedSource
      (installPositiveSourceGravityMouthIteratedConnection n configuration) 0 := by
  intro jointZero
  have residualZero := jointZero
  unfold OnCurrentPointwiseJointShellZeroFiber at residualZero
  have gravityZero := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.algebraic.gravityAuxiliary) residualZero
  apply
    (installPositiveSourceGravityMouthIteratedConnection_gravityResidual_ne_zero
      n configuration preservesCoframe simplicityMouth)
  simpa [currentPointwiseJointShellResidual] using gravityZero

/-- Primitive Lorentz connection generated from the existing source origin
value and the unique residual-limit curvature. -/
def positiveSourceGravityMouthResidualLimitConnectionField :
    LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    positiveSourceGravityMouthOriginConnectionValue
    positiveSourceGravityMouthResidualLimitCurvature

/-- With the ordinary product topology on component fields, the normalized
affine right inverse is continuous in its curvature target.  This does not
claim convergence in a derivative/jet norm. -/
theorem continuous_normalizedAffineLorentzConnectionField_target
    (omega0 : PointwiseLorentzSpinConnection) :
    Continuous
      (fun target : PhysicalBivector =>
        normalizedAffineLorentzConnectionField omega0 target) := by
  unfold normalizedAffineLorentzConnectionField
    normalizedAffineBivectorOneForm
    normalizedAffineBivectorComponentLinear
    normalizedDerivativeBivector
    originLorentzBracketCurvature
    lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  fun_prop

/-- The actual primitive connection-germ orbit, not merely its curvature
readout, converges to the canonical limit realization. -/
theorem tendsto_positiveSourceGravityMouthIteratedConnectionField :
    Tendsto positiveSourceGravityMouthIteratedConnectionField atTop
      (nhds positiveSourceGravityMouthResidualLimitConnectionField) := by
  have targetLimit :=
    (continuous_normalizedAffineLorentzConnectionField_target
      positiveSourceGravityMouthOriginConnectionValue).tendsto
        positiveSourceGravityMouthResidualLimitCurvature
  have composed := targetLimit.comp
    tendsto_positiveSourceGravityMouthIteratedCurvatureObligation
  change Tendsto
    (fun n : ℕ => normalizedAffineLorentzConnectionField
      positiveSourceGravityMouthOriginConnectionValue
      (positiveSourceGravityMouthIteratedCurvatureObligation n)) atTop
    (nhds (normalizedAffineLorentzConnectionField
      positiveSourceGravityMouthOriginConnectionValue
      positiveSourceGravityMouthConstitutiveCurvature))
  simpa [Function.comp_def,
    positiveSourceGravityMouthResidualLimitCurvature] using composed

/-- Product-topology uniqueness excludes a second connection-field limit
branch. -/
theorem positiveSourceGravityMouthIteratedConnectionField_limit_unique
    (candidate : LorentzConnectionField)
    (limitLaw :
      Tendsto positiveSourceGravityMouthIteratedConnectionField atTop
        (nhds candidate)) :
    candidate = positiveSourceGravityMouthResidualLimitConnectionField :=
  tendsto_nhds_unique limitLaw
    tendsto_positiveSourceGravityMouthIteratedConnectionField

@[simp] theorem positiveSourceGravityMouthResidualLimitConnectionField_origin :
    positiveSourceGravityMouthResidualLimitConnectionField 0 =
      positiveSourceGravityMouthOriginConnectionValue :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem positiveSourceGravityMouthResidualLimitConnectionField_smooth :
    SmoothLorentzConnectionField
      positiveSourceGravityMouthResidualLimitConnectionField :=
  normalizedAffineLorentzConnectionField_smooth _ _

theorem positiveSourceGravityMouthResidualLimitConnectionField_lorentzSkew
    (point : BasePoint) :
    LorentzSkew
      (positiveSourceGravityMouthResidualLimitConnectionField point) := by
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (positive_generatedLorentzConnection_lorentzSkew 0) point

theorem positiveSourceGravityMouthResidualLimitConnectionField_origin_tetradCompatible :
    TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      (positiveSourceGravityMouthResidualLimitConnectionField 0) := by
  rw [positiveSourceGravityMouthResidualLimitConnectionField_origin]
  exact positive_generatedLorentzConnection_tetradCompatible 0

/-- One-field installer.  It cannot select or erase any of the other eight
primitive fields. -/
def installPositiveSourceGravityMouthResidualLimitConnection
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection :=
      positiveSourceGravityMouthResidualLimitConnectionField }

theorem installPositiveSourceGravityMouthResidualLimitConnection_preserves_otherFields
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).coframe = configuration.coframe ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).gravityAuxiliary = configuration.gravityAuxiliary ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).gravitySimplicityMultiplier =
          configuration.gravitySimplicityMultiplier ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).gaugeConnection = configuration.gaugeConnection ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).gaugeAuxiliary = configuration.gaugeAuxiliary ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).scalar = configuration.scalar ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).matter = configuration.matter ∧
      (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem installPositiveSourceGravityMouthResidualLimitConnection_nondegenerate_iff
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthResidualLimitConnection
        configuration).Nondegenerate ↔ configuration.Nondegenerate :=
  Iff.rfl

theorem installPositiveSourceGravityMouthResidualLimitConnection_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (installPositiveSourceGravityMouthResidualLimitConnection
      configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      positiveSourceGravityMouthResidualLimitConnectionField_smooth,
      gravityAuxiliarySmooth, gravityMultiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

/-- The actual `dω+ω∧ω` curvature realizes the unique limit exactly. -/
theorem installPositiveSourceGravityMouthResidualLimitConnection_curvature_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (installPositiveSourceGravityMouthResidualLimitConnection
          configuration) 0 =
      positiveSourceGravityMouthResidualLimitCurvature := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        positiveSourceGravityMouthOriginConnectionValue
        positiveSourceGravityMouthResidualLimitCurvature) 0 =
    positiveSourceGravityMouthResidualLimitCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-- Primary Layer-3 checkpoint: the actual limit germ closes both triangular
gravity algebraic coordinates at the origin.  It says nothing about the gauge
coordinate or six Euler--Lagrange coordinates. -/
theorem installPositiveSourceGravityMouthResidualLimitConnection_gravityAlgebraicPair_origin
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthResidualLimitConnection
          configuration) 0).gravitySimplicity = 0 ∧
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthResidualLimitConnection
          configuration) 0).gravityAuxiliary = 0 := by
  constructor
  · change generatedGravitySimplicityResidual
      (toContinuumPointField
        (installPositiveSourceGravityMouthResidualLimitConnection
          configuration) 0) = 0
    apply (gravitySimplicityResidual_eq_zero_iff
      (installPositiveSourceGravityMouthResidualLimitConnection configuration)
      0).mpr
    simpa [installPositiveSourceGravityMouthResidualLimitConnection] using
      simplicityMouth
  · change holonomicGravityAuxiliaryEquationResidual
      (installPositiveSourceGravityMouthResidualLimitConnection configuration)
      0 = 0
    apply (gravityAuxiliaryResidual_eq_zero_iff
      (installPositiveSourceGravityMouthResidualLimitConnection configuration)
      0).mpr
    rw [installPositiveSourceGravityMouthResidualLimitConnection_curvature_origin]
    change positiveSourceGravityMouthResidualLimitCurvature =
      gravityInternalDualEquiv (configuration.gravityAuxiliary 0)
    rw [simplicityMouth]
    unfold PreservesPositiveSourceCoframeAtOrigin at preservesCoframe
    rw [preservesCoframe]
    rfl

/-- Smooth extensions inherit the actual off-shell gravity Bianchi identity;
this remains kinematic and is not stationarity. -/
theorem installPositiveSourceGravityMouthResidualLimitConnection_bianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthResidualLimitConnection
            configuration) point first second third +
        covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthResidualLimitConnection
            configuration) point second third first +
        covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthResidualLimitConnection
            configuration) point third first second = 0 := by
  exact holonomicGravityGL4Curvature_bianchi
    (installPositiveSourceGravityMouthResidualLimitConnection configuration)
    (installPositiveSourceGravityMouthResidualLimitConnection_smooth
      configuration smooth) point first second third

/-! ## Existing six-field partial carrier at the canonical limit -/

/-- Reuse the existing carrier type and its five unaffected generated fields;
only the gravity connection advances from `Kr` to the unique residual limit. -/
def positiveSourceResidualLimitStageNinePartialPrimitiveCarrier :
    StageNinePartialPrimitiveCarrier :=
  { positiveSourceStageNinePartialPrimitiveCarrier with
    gravityConnection :=
      positiveSourceGravityMouthResidualLimitConnectionField }

/-- Exact full-configuration reader class.  Missing multiplier, matter, and
dual remain arbitrary; this structure stores no shell or stationarity proof. -/
structure ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier
    (configuration : StageNineHolonomicConfiguration) : Prop where
  coframe : configuration.coframe =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.coframe
  gravityConnection : configuration.gravityConnection =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gravityConnection
  gravityAuxiliary : configuration.gravityAuxiliary =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gravityAuxiliary
  gaugeConnection : configuration.gaugeConnection =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gaugeConnection
  gaugeAuxiliary : configuration.gaugeAuxiliary =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gaugeAuxiliary
  scalar : configuration.scalar =
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.scalar

theorem residualLimitExtension_preserves_positiveSourceCoframeAtOrigin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    PreservesPositiveSourceCoframeAtOrigin configuration := by
  unfold PreservesPositiveSourceCoframeAtOrigin
  rw [extension.coframe]
  rfl

theorem residualLimitExtension_has_simplicityMouth
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0) := by
  rw [extension.gravityAuxiliary, extension.coframe]
  rfl

theorem residualLimitExtension_gravityCurvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    holonomicGravityCurvature configuration 0 =
      positiveSourceGravityMouthResidualLimitCurvature := by
  let installed :=
    installPositiveSourceGravityMouthResidualLimitConnection configuration
  have connectionEquality : configuration.gravityConnection =
      positiveSourceGravityMouthResidualLimitConnectionField := by
    rw [extension.gravityConnection]
    rfl
  have configurationEquality : installed = configuration := by
    apply StageNineHolonomicConfiguration.ext
    · rfl
    · exact connectionEquality.symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [← configurationEquality]
  exact
    installPositiveSourceGravityMouthResidualLimitConnection_curvature_origin
      configuration

theorem residualLimitExtension_gaugeCurvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    holonomicGaugeCurvature configuration 0 =
      sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy := by
  let installed := installSourceP286AffineConnection
    positiveSmoothUnifiedSource.legacy configuration
  have connectionEquality : configuration.gaugeConnection =
      sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy := by
    rw [extension.gaugeConnection]
    rfl
  have configurationEquality : installed = configuration := by
    apply StageNineHolonomicConfiguration.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · exact connectionEquality.symm
    · rfl
    · rfl
    · rfl
    · rfl
  rw [← configurationEquality]
  exact holonomicGaugeCurvature_installSourceP286AffineConnection_origin _ _

theorem residualLimitExtension_gravitySimplicityResidual_origin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        configuration 0).gravitySimplicity = 0 := by
  change generatedGravitySimplicityResidual
      (toContinuumPointField configuration 0) = 0
  exact (gravitySimplicityResidual_eq_zero_iff configuration 0).mpr
    (residualLimitExtension_has_simplicityMouth configuration extension)

theorem residualLimitExtension_gravityAuxiliaryResidual_origin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        configuration 0).gravityAuxiliary = 0 := by
  change holonomicGravityAuxiliaryEquationResidual configuration 0 = 0
  apply (gravityAuxiliaryResidual_eq_zero_iff configuration 0).mpr
  rw [residualLimitExtension_gravityCurvature_origin configuration extension,
    extension.gravityAuxiliary]
  rfl

theorem residualLimitExtension_p286GaugeAuxiliaryResidual_origin
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        configuration 0).p286GaugeAuxiliary = 0 := by
  change holonomicP286GaugeAuxiliaryEquationResidual
    positiveSmoothUnifiedSource configuration 0 = 0
  apply (p286GaugeAuxiliaryResidual_eq_zero_iff
    positiveSmoothUnifiedSource configuration 0).mpr
  rw [residualLimitExtension_gaugeCurvature_origin configuration extension]
  have coframeNondegenerate :
      Matrix.det (positiveSmoothUnifiedSource.legacy.coframeAt 0) ≠ 0 := by
    change Matrix.det (canonicalPhysicalSource.coframeAt 0) ≠ 0
    rw [canonicalPhysicalSource_coframeAt_det]
    norm_num
  have solved := (generatedP286GaugeConstitutiveAuxiliary_solves
    positiveSmoothUnifiedSource
    (positiveSmoothUnifiedSource.legacy.coframeAt 0)
    coframeNondegenerate
    (sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy)).symm
  rw [extension.coframe, extension.gaugeAuxiliary]
  simpa [positiveSourceResidualLimitStageNinePartialPrimitiveCarrier,
    positiveSourceStageNinePartialPrimitiveCarrier,
    sourceGeneratedStageNinePartialPrimitiveCarrier] using solved

/-- All three current strong algebraic coordinates are genuinely zero at the
origin.  The six Euler--Lagrange coordinates remain visible and unclaimed. -/
theorem residualLimitExtension_currentAlgebraicResidual_origin_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        configuration 0 = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · exact residualLimitExtension_gravitySimplicityResidual_origin
      configuration extension
  · exact residualLimitExtension_gravityAuxiliaryResidual_origin
      configuration extension
  · exact residualLimitExtension_p286GaugeAuxiliaryResidual_origin
      configuration extension

/-- Exact remaining responsibility after origin algebraic closure. -/
theorem residualLimitExtension_jointResidual_origin_eq_eulerLagrange_only
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        configuration 0 =
      { algebraic := 0
        eulerLagrange := currentPointwiseEulerLagrangeResidual
          positiveSmoothUnifiedSource configuration 0 } := by
  apply CurrentPointwiseJointShellResidualCarrier.ext
  · exact residualLimitExtension_currentAlgebraicResidual_origin_eq_zero
      configuration extension
  · rfl

/-- After the actual algebraic germ closes, pointwise joint closure is exactly
the still-open six-channel Euler--Lagrange problem. -/
theorem residualLimitExtension_onJointZeroFiber_iff_eulerLagrange
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    OnCurrentPointwiseJointShellZeroFiber positiveSmoothUnifiedSource
        configuration 0 ↔
      OnCurrentPointwiseEulerLagrangeZeroFiber positiveSmoothUnifiedSource
        configuration 0 := by
  unfold OnCurrentPointwiseJointShellZeroFiber
    OnCurrentPointwiseEulerLagrangeZeroFiber
  rw [residualLimitExtension_jointResidual_origin_eq_eulerLagrange_only
    configuration extension]
  constructor
  · intro jointZero
    simpa using
      congrArg CurrentPointwiseJointShellResidualCarrier.eulerLagrange
        jointZero
  · intro eulerZero
    apply CurrentPointwiseJointShellResidualCarrier.ext
    · rfl
    · exact eulerZero

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
