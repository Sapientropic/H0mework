import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# S9-C3h116: action-generated Cartan connection local actual lift

C3h107 already lets the primitive P506/L0 source generate a nonzero Dirac
spin covector.  This module does not decode that covector into a coframe
endpoint.  Instead it returns to the path-first/action-first construction:

```text
primitive source
→ actual Stage-8 matter link and target-dual action
→ complete Dirac spin covector
→ simple-B Cartan connection law derived from the Lorentz action
→ unique connection coordinates
→ C3h101 local actual path U
→ Lorentz Euler--Lagrange acceptance.
```

The displayed Cartan map is first proved equal to the actual gravity-BF
connection response at the identity simple-B mouth.  Its inverse is then
derived internally.  Thus the coefficients below are fixed by the existing
action normalization; none is a source knob, residual target, endpoint
coordinate, branch receipt, or supplied inverse.

The result is an interaction-sensitive identity-mouth local germ.  It is not
yet a generic nonidentity-coframe Cartan transport, a coframe evolution, a
nonlinear integral flow, or full joint stationarity.  In particular, the
Lorentz residual is read only after the actual connection germ has been
constructed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCartanConnectionLocalActualLift

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineConjugateMatterActionTimeVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Dependency-light finite coordinates -/

/-- Coordinate basis of the actual Lorentz-bivector one-form carrier. -/
def cartanLorentzCoordinateDirection
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    LorentzBivectorOneForm :=
  fun candidateForm candidatePair =>
    if candidateForm = formDirection ∧ candidatePair = internalPair then
      1
    else
      0

/-- All twenty-four matter-spin coordinates read from the actual
representation action. -/
def sourceActionGeneratedMatterSpinCoordinates
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    lorentzMatterSpinSourceCoefficient source configuration
      (cartanLorentzCoordinateDirection formDirection internalPair) point

/-! ## The action-native simple-B Cartan map -/

/-- Identity-coframe/simple-B carrier used only to expose the gravity-BF
connection response.  Every field not read by that response is retained from
the already source/action-generated C3h107 actual germ. -/
def identitySimpleBCartanConnectionCarrier
    (connectionCoordinates : LorentzBivectorOneForm) :
    StageNineHolonomicConfiguration :=
  { positiveSourceTargetMatterActual with
    gravityConnection := fun _ =>
      lorentzSkewConnectionOfBivectorOneForm connectionCoordinates }

/-- Actual action readout: a connection coordinate is sent to minus the
gravity-BF algebraic connection response on every coordinate direction.
The sign is the Cartan balance convention
`-gravityBF = matterSpin`. -/
def identitySimpleBCartanConnectionResponseCoordinates
    (connectionCoordinates : LorentzBivectorOneForm) :
    LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    -lorentzGravityBFAlgebraicCoefficient
      (identitySimpleBCartanConnectionCarrier connectionCoordinates)
      (cartanLorentzCoordinateDirection formDirection internalPair) 0

/-- Closed coordinate form of the action-native Cartan map. -/
def identitySimpleBCartanConnectionResponseNormalForm
    (q : LorentzBivectorOneForm) :
    LorentzBivectorOneForm :=
  ![
    ![
      -q 2 5 + q 3 4,
      q 1 5 - q 3 3,
      -q 1 4 + q 2 3,
      -q 2 2 + q 3 1,
      q 1 2 - q 3 0,
      -q 1 1 + q 2 0],
    ![
      -q 2 1 - q 3 2,
      -q 0 5 + q 2 0,
      q 0 4 + q 3 0,
      q 2 4 + q 3 5,
      -q 0 2 - q 2 3,
      q 0 1 - q 3 3],
    ![
      q 0 5 + q 1 1,
      -q 1 0 - q 3 2,
      -q 0 3 + q 3 1,
      q 0 2 - q 1 4,
      q 1 3 + q 3 5,
      -q 0 0 - q 3 4],
    ![
      -q 0 4 + q 1 2,
      q 0 3 + q 2 2,
      -q 1 0 - q 2 1,
      -q 0 1 - q 1 5,
      q 0 0 - q 2 5,
      q 1 3 + q 2 4]
  ]

/-- The displayed map is not an ansatz: every coordinate is the actual
gravity-BF connection response of the existing action. -/
theorem identitySimpleBCartanConnectionResponse_eq_normalForm
    (q : LorentzBivectorOneForm) :
    identitySimpleBCartanConnectionResponseCoordinates q =
      identitySimpleBCartanConnectionResponseNormalForm q := by
  funext formDirection internalPair
  have coframeOrigin :
      (identitySimpleBCartanConnectionCarrier q).coframe 0 =
        (1 : LorentzianCoframe) := by
    rfl
  have auxiliaryOrigin :
      (identitySimpleBCartanConnectionCarrier q).gravityAuxiliary 0 =
        physicalIIPlusBivector 1 := by
    rfl
  unfold identitySimpleBCartanConnectionResponseCoordinates
    lorentzGravityBFAlgebraicCoefficient
  simp only [toContinuumPointField]
  rw [coframeOrigin, auxiliaryOrigin]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold gravityBFCurvatureIncrementDensity
  rw [← gravityAuxiliaryHodgePairingPolynomial_eq
    (1 : LorentzianCoframe) (by simp)]
  unfold gravityAuxiliaryHodgePairingPolynomial
    lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [identitySimpleBCartanConnectionCarrier,
      cartanLorentzCoordinateDirection,
      identitySimpleBCartanConnectionResponseNormalForm,
      physicalIIPlusBivector, coframeWedge, coframeTwoFormLinear,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      Matrix.one_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;>
    ring

/-! ## Derived inverse and uniqueness -/

/-- The inverse forced by the actual Cartan response matrix.  It is a theorem
output of the action calculation above, not a caller-supplied preimage. -/
def identitySimpleBCartanConnectionCoordinates
    (spin : LorentzBivectorOneForm) :
    LorentzBivectorOneForm :=
  ![
    ![
      -(1 / 2 : ℝ) * spin 0 0 - (1 / 2 : ℝ) * spin 2 5 +
        (1 / 2 : ℝ) * spin 3 4,
      -(1 / 2 : ℝ) * spin 0 1 + (1 / 2 : ℝ) * spin 1 5 -
        (1 / 2 : ℝ) * spin 3 3,
      -(1 / 2 : ℝ) * spin 0 2 - (1 / 2 : ℝ) * spin 1 4 +
        (1 / 2 : ℝ) * spin 2 3,
      (1 / 2 : ℝ) * spin 0 3 - (1 / 2 : ℝ) * spin 2 2 +
        (1 / 2 : ℝ) * spin 3 1,
      (1 / 2 : ℝ) * spin 0 4 + (1 / 2 : ℝ) * spin 1 2 -
        (1 / 2 : ℝ) * spin 3 0,
      (1 / 2 : ℝ) * spin 0 5 - (1 / 2 : ℝ) * spin 1 1 +
        (1 / 2 : ℝ) * spin 2 0],
    ![
      (1 / 2 : ℝ) * spin 1 0 - (1 / 2 : ℝ) * spin 2 1 -
        (1 / 2 : ℝ) * spin 3 2,
      -(1 / 2 : ℝ) * spin 0 5 + (1 / 2 : ℝ) * spin 1 1 +
        (1 / 2 : ℝ) * spin 2 0,
      (1 / 2 : ℝ) * spin 0 4 + (1 / 2 : ℝ) * spin 1 2 +
        (1 / 2 : ℝ) * spin 3 0,
      -(1 / 2 : ℝ) * spin 1 3 + (1 / 2 : ℝ) * spin 2 4 +
        (1 / 2 : ℝ) * spin 3 5,
      -(1 / 2 : ℝ) * spin 0 2 - (1 / 2 : ℝ) * spin 1 4 -
        (1 / 2 : ℝ) * spin 2 3,
      (1 / 2 : ℝ) * spin 0 1 - (1 / 2 : ℝ) * spin 1 5 -
        (1 / 2 : ℝ) * spin 3 3],
    ![
      (1 / 2 : ℝ) * spin 0 5 + (1 / 2 : ℝ) * spin 1 1 +
        (1 / 2 : ℝ) * spin 2 0,
      -(1 / 2 : ℝ) * spin 1 0 + (1 / 2 : ℝ) * spin 2 1 -
        (1 / 2 : ℝ) * spin 3 2,
      -(1 / 2 : ℝ) * spin 0 3 + (1 / 2 : ℝ) * spin 2 2 +
        (1 / 2 : ℝ) * spin 3 1,
      (1 / 2 : ℝ) * spin 0 2 - (1 / 2 : ℝ) * spin 1 4 -
        (1 / 2 : ℝ) * spin 2 3,
      (1 / 2 : ℝ) * spin 1 3 - (1 / 2 : ℝ) * spin 2 4 +
        (1 / 2 : ℝ) * spin 3 5,
      -(1 / 2 : ℝ) * spin 0 0 - (1 / 2 : ℝ) * spin 2 5 -
        (1 / 2 : ℝ) * spin 3 4],
    ![
      -(1 / 2 : ℝ) * spin 0 4 + (1 / 2 : ℝ) * spin 1 2 +
        (1 / 2 : ℝ) * spin 3 0,
      (1 / 2 : ℝ) * spin 0 3 + (1 / 2 : ℝ) * spin 2 2 +
        (1 / 2 : ℝ) * spin 3 1,
      -(1 / 2 : ℝ) * spin 1 0 - (1 / 2 : ℝ) * spin 2 1 +
        (1 / 2 : ℝ) * spin 3 2,
      -(1 / 2 : ℝ) * spin 0 1 - (1 / 2 : ℝ) * spin 1 5 -
        (1 / 2 : ℝ) * spin 3 3,
      (1 / 2 : ℝ) * spin 0 0 - (1 / 2 : ℝ) * spin 2 5 -
        (1 / 2 : ℝ) * spin 3 4,
      (1 / 2 : ℝ) * spin 1 3 + (1 / 2 : ℝ) * spin 2 4 -
        (1 / 2 : ℝ) * spin 3 5]
  ]

theorem identitySimpleBCartanConnectionCoordinates_leftInverse
    (q : LorentzBivectorOneForm) :
    identitySimpleBCartanConnectionCoordinates
        (identitySimpleBCartanConnectionResponseNormalForm q) =
      q := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [identitySimpleBCartanConnectionCoordinates,
      identitySimpleBCartanConnectionResponseNormalForm] <;>
    ring

theorem identitySimpleBCartanConnectionCoordinates_rightInverse
    (spin : LorentzBivectorOneForm) :
    identitySimpleBCartanConnectionResponseNormalForm
        (identitySimpleBCartanConnectionCoordinates spin) =
      spin := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [identitySimpleBCartanConnectionCoordinates,
      identitySimpleBCartanConnectionResponseNormalForm] <;>
    ring

theorem identitySimpleBCartanConnectionResponse_bijective :
    Function.Bijective
      identitySimpleBCartanConnectionResponseCoordinates := by
  constructor
  · intro first second equality
    rw [identitySimpleBCartanConnectionResponse_eq_normalForm,
      identitySimpleBCartanConnectionResponse_eq_normalForm] at equality
    have lifted :=
      congrArg identitySimpleBCartanConnectionCoordinates equality
    simpa [identitySimpleBCartanConnectionCoordinates_leftInverse] using
      lifted
  · intro spin
    refine ⟨identitySimpleBCartanConnectionCoordinates spin, ?_⟩
    rw [identitySimpleBCartanConnectionResponse_eq_normalForm]
    exact identitySimpleBCartanConnectionCoordinates_rightInverse spin

theorem identitySimpleBCartanConnectionResponse_unique
    (spin first second : LorentzBivectorOneForm)
    (firstLaw :
      identitySimpleBCartanConnectionResponseCoordinates first = spin)
    (secondLaw :
      identitySimpleBCartanConnectionResponseCoordinates second = spin) :
    first = second :=
  identitySimpleBCartanConnectionResponse_bijective.1
    (firstLaw.trans secondLaw.symm)

/-! ## Positive source/action specialization -/

def positiveSourceMatterSpinCoordinatesNormalForm :
    LorentzBivectorOneForm :=
  ![
    ![0, 0, 0, 0, 0, -(1 / 2 : ℝ)],
    ![0, (1 / 2 : ℝ), 0, -(1 / 2 : ℝ), 0, 0],
    ![-(1 / 2 : ℝ), 0, 0, 0, -(1 / 2 : ℝ), 0],
    ![0, 0, 0, 0, 0, -(1 / 2 : ℝ)]
  ]

theorem positiveSourceMatterSpinCoordinates_eq_normalForm_of_origin
    (configuration : StageNineHolonomicConfiguration)
    (coframeOrigin : configuration.coframe 0 = 1)
    (matterOrigin :
      configuration.matter 0 = diracSpinTwoMatterProbe)
    (conjugateOrigin :
      configuration.conjugateMatter 0 = diracSpinZeroMatterCoordinate) :
    sourceActionGeneratedMatterSpinCoordinates
        positiveSmoothUnifiedSource configuration 0 =
      positiveSourceMatterSpinCoordinatesNormalForm := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [sourceActionGeneratedMatterSpinCoordinates,
      cartanLorentzCoordinateDirection,
      lorentzMatterSpinSourceCoefficient,
      positiveSourceMatterSpinCoordinatesNormalForm,
      coframeOrigin, matterOrigin, conjugateOrigin,
      matterGaugeConnectionFirstVariationDensity,
      matterGaugeConnectionVariationVector,
      matterGaugeKineticSum,
      holonomicMatterLorentzConnectionVariation,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      generatedVolumeDensity, toContinuumPointField,
      positiveSourceTargetMatterCauchyState_matter,
      positiveSourceTargetMatterCauchyState_conjugate,
      positiveSmoothUnifiedSource,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm,
      Fin.sum_univ_four, Fin.sum_univ_six,
      pairFirst, pairSecond, lorentzBivectorFirst,
      lorentzBivectorSecond, minkowskiInternalSign,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      inverseCoframeDiracGamma,
      inverseCoframeDiracGamma_identity,
      diracMatrixMatterAction,
      diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate_probe,
      Matrix.mul_apply]

theorem positiveSourceMatterSpinCoordinates_eq_normalForm :
    sourceActionGeneratedMatterSpinCoordinates
        positiveSmoothUnifiedSource positiveSourceTargetMatterActual 0 =
      positiveSourceMatterSpinCoordinatesNormalForm := by
  apply positiveSourceMatterSpinCoordinates_eq_normalForm_of_origin
  · rfl
  · change
      (sourceActionGeneratedMatterLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).matter 0 = diracSpinTwoMatterProbe
    rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
    exact positiveSourceTargetMatterCauchyState_matter
  · change
      (sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).conjugateMatter 0 = diracSpinZeroMatterCoordinate
    rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
    exact positiveSourceTargetMatterCauchyState_conjugate

/-- Connection coordinates generated by the positive source's actual spin
covector through the action-derived Cartan map. -/
def positiveSourceActionGeneratedCartanConnectionCoordinates :
    LorentzBivectorOneForm :=
  identitySimpleBCartanConnectionCoordinates
    (sourceActionGeneratedMatterSpinCoordinates
      positiveSmoothUnifiedSource positiveSourceTargetMatterActual 0)

def positiveSourceActionGeneratedCartanConnectionCoordinatesNormalForm :
    LorentzBivectorOneForm :=
  ![
    ![0, 0, 0, 0, 0, -(3 / 4 : ℝ)],
    ![0, (1 / 4 : ℝ), 0, -(1 / 4 : ℝ), 0, 0],
    ![-(1 / 4 : ℝ), 0, 0, 0, -(1 / 4 : ℝ), 0],
    ![0, 0, 0, 0, 0, -(1 / 4 : ℝ)]
  ]

theorem
    positiveSourceActionGeneratedCartanConnectionCoordinates_eq_normalForm :
    positiveSourceActionGeneratedCartanConnectionCoordinates =
      positiveSourceActionGeneratedCartanConnectionCoordinatesNormalForm := by
  rw [positiveSourceActionGeneratedCartanConnectionCoordinates,
    positiveSourceMatterSpinCoordinates_eq_normalForm]
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [identitySimpleBCartanConnectionCoordinates,
      positiveSourceMatterSpinCoordinatesNormalForm,
      positiveSourceActionGeneratedCartanConnectionCoordinatesNormalForm] <;>
    ring

theorem positiveSourceActionGeneratedCartanConnection_satisfies_actionLaw :
    identitySimpleBCartanConnectionResponseCoordinates
        positiveSourceActionGeneratedCartanConnectionCoordinates =
      sourceActionGeneratedMatterSpinCoordinates
        positiveSmoothUnifiedSource positiveSourceTargetMatterActual 0 := by
  rw [identitySimpleBCartanConnectionResponse_eq_normalForm]
  exact identitySimpleBCartanConnectionCoordinates_rightInverse _

theorem positiveSourceActionGeneratedCartanConnection_nonzero :
    positiveSourceActionGeneratedCartanConnectionCoordinates ≠ 0 := by
  intro zero
  have coordinate := congrFun
    (congrFun zero (0 : LorentzianIndex)) (5 : Fin 6)
  rw [
    positiveSourceActionGeneratedCartanConnectionCoordinates_eq_normalForm]
    at coordinate
  simp [positiveSourceActionGeneratedCartanConnectionCoordinatesNormalForm]
    at coordinate

/-! ## Source/action-generated Cauchy seed and local actual U -/

/-- Install only the action-generated Cartan connection into the C3h107
source-matter Cauchy seed.  No coframe, auxiliary, residual, or endpoint is
decoded from the spin covector. -/
def positiveSourceActionGeneratedCartanConnectionCauchyState :
    StageNineCauchyState :=
  { positiveSourceTargetMatterCauchyState with
    gravityConnection := fun _ =>
      lorentzSkewConnectionOfBivectorOneForm
        positiveSourceActionGeneratedCartanConnectionCoordinates }

/-- Actual local path generated by the existing C3h101 dynamics from the
source/action-selected Cartan Cauchy seed. -/
def positiveSourceActionGeneratedCartanConnectionLocalActualLift :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedJointLocalActualLift
    positiveSmoothUnifiedSource
    positiveSourceActionGeneratedCartanConnectionCauchyState 0

@[simp] theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe
    (point : BasePoint) :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.coframe
        point =
      1 := by
  rfl

@[simp] theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_auxiliary
    (point : BasePoint) :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.gravityAuxiliary
        point =
      physicalIIPlusBivector 1 := by
  rfl

@[simp] theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_connection_origin :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveSourceActionGeneratedCartanConnectionCoordinates := by
  exact sourceActionGeneratedJointLocalActualLift_initialGravityConnection
    positiveSmoothUnifiedSource
    positiveSourceActionGeneratedCartanConnectionCauchyState 0

@[simp] theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_matter_origin :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.matter 0 =
      diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedMatterLocalActualLift
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedCartanConnectionCauchyState 0).matter 0 =
        diracSpinTwoMatterProbe
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  exact positiveSourceTargetMatterCauchyState_matter

@[simp] theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_conjugate_origin :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.conjugateMatter
        0 =
      diracSpinZeroMatterCoordinate := by
  change
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedCartanConnectionCauchyState
      0).conjugateMatter 0 =
        diracSpinZeroMatterCoordinate
  rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
  exact positiveSourceTargetMatterCauchyState_conjugate

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_smooth :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.Smooth :=
  sourceActionGeneratedJointLocalActualLift_smooth
    positiveSmoothUnifiedSource
    positiveSourceActionGeneratedCartanConnectionCauchyState 0

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_nondegenerate :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.Nondegenerate := by
  apply sourceActionGeneratedJointLocalActualLift_nondegenerate
  simp [positiveSourceActionGeneratedCartanConnectionCauchyState,
    positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_simplicity :
    StageNinePlebanskiMultiplierVariation.GravitySimplicityEquation
      positiveSourceActionGeneratedCartanConnectionLocalActualLift := by
  intro point
  rw [
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_auxiliary,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe]

/-! ## Downstream Lorentz-action acceptance -/

theorem cartanLorentzCoordinateExpansion
    (direction : LorentzBivectorOneForm) :
    (∑ formDirection : LorentzianIndex,
      ∑ internalPair : Fin 6,
        direction formDirection internalPair •
          cartanLorentzCoordinateDirection formDirection internalPair) =
      direction := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [cartanLorentzCoordinateDirection, Fin.sum_univ_six]

theorem cartanLorentzAlgebraicCurvatureDirection_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionAlgebraicCurvatureDirection configuration
        (first + second) point =
      lorentzConnectionAlgebraicCurvatureDirection configuration first
          point +
        lorentzConnectionAlgebraicCurvatureDirection configuration second
          point := by
  funext internalPair spacetimePair
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  rw [lorentzSkewConnectionOfBivectorOneForm_add]
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg
  apply Finset.sum_congr rfl
  intro middle _
  ring

theorem cartanLorentzAlgebraicCurvatureDirection_smul
    (configuration : StageNineHolonomicConfiguration)
    (scalar : ℝ)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionAlgebraicCurvatureDirection configuration
        (scalar • direction) point =
      scalar •
        lorentzConnectionAlgebraicCurvatureDirection configuration
          direction point := by
  funext internalPair spacetimePair
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  rw [lorentzSkewConnectionOfBivectorOneForm_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro middle _
  ring

theorem cartanLorentzGravityBFAlgebraicCoefficient_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzGravityBFAlgebraicCoefficient configuration
        (first + second) point =
      lorentzGravityBFAlgebraicCoefficient configuration first point +
        lorentzGravityBFAlgebraicCoefficient configuration second point := by
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [cartanLorentzAlgebraicCurvatureDirection_add,
    gravityBFCurvatureIncrementDensity_add]
  ring

theorem cartanLorentzGravityBFAlgebraicCoefficient_smul
    (configuration : StageNineHolonomicConfiguration)
    (scalar : ℝ)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzGravityBFAlgebraicCoefficient configuration
        (scalar • direction) point =
      scalar *
        lorentzGravityBFAlgebraicCoefficient configuration direction point := by
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [cartanLorentzAlgebraicCurvatureDirection_smul,
    gravityBFCurvatureIncrementDensity_smul]
  ring

theorem cartanHolonomicMatterLorentzVariation_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : LorentzBivectorOneForm)
    (point : BasePoint) :
    holonomicMatterLorentzConnectionVariation configuration
        (fun _ => first + second) point =
      holonomicMatterLorentzConnectionVariation configuration
          (fun _ => first) point +
        holonomicMatterLorentzConnectionVariation configuration
          (fun _ => second) point := by
  funext formDirection
  unfold holonomicMatterLorentzConnectionVariation
  rw [lorentzSkewConnectionOfBivectorOneForm_add,
    diracSpinConnectionLift_add,
    diracMatrixMatterAction_add_matrix_local]
  rfl

theorem cartanHolonomicMatterLorentzVariation_smul
    (configuration : StageNineHolonomicConfiguration)
    (scalar : ℝ)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    holonomicMatterLorentzConnectionVariation configuration
        (fun _ => scalar • direction) point =
      scalar •
        holonomicMatterLorentzConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicMatterLorentzConnectionVariation
  rw [lorentzSkewConnectionOfBivectorOneForm_smul,
    diracSpinConnectionLift_real_smul,
    diracMatrixMatterAction_real_smul_matrix_local]
  rfl

theorem cartanLorentzMatterSpinSourceCoefficient_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzMatterSpinSourceCoefficient source configuration
        (first + second) point =
      lorentzMatterSpinSourceCoefficient source configuration first point +
        lorentzMatterSpinSourceCoefficient source configuration second
          point := by
  unfold lorentzMatterSpinSourceCoefficient
  rw [cartanHolonomicMatterLorentzVariation_add]
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_add, smul_add, map_add, Complex.add_re]
  ring

theorem cartanLorentzMatterSpinSourceCoefficient_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (scalar : ℝ)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzMatterSpinSourceCoefficient source configuration
        (scalar • direction) point =
      scalar *
        lorentzMatterSpinSourceCoefficient source configuration direction
          point := by
  unfold lorentzMatterSpinSourceCoefficient
  rw [cartanHolonomicMatterLorentzVariation_smul,
    matterGaugeConnectionFirstVariationDensity_real_smul_local]
  ring

/-- Gravity-BF algebraic action response as the finite dual of the Lorentz
connection carrier. -/
def cartanLorentzGravityBFActionDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    Module.Dual ℝ LorentzBivectorOneForm where
  toFun := fun direction =>
    lorentzGravityBFAlgebraicCoefficient configuration direction point
  map_add' := fun first second =>
    cartanLorentzGravityBFAlgebraicCoefficient_add configuration
      first second point
  map_smul' := by
    intro scalar direction
    simpa [smul_eq_mul] using
      cartanLorentzGravityBFAlgebraicCoefficient_smul configuration
        scalar direction point

/-- Dirac matter-spin action response as the same finite dual. -/
def cartanLorentzMatterSpinActionDual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    Module.Dual ℝ LorentzBivectorOneForm where
  toFun := fun direction =>
    lorentzMatterSpinSourceCoefficient source configuration direction point
  map_add' := fun first second =>
    cartanLorentzMatterSpinSourceCoefficient_add source configuration
      first second point
  map_smul' := by
    intro scalar direction
    simpa [smul_eq_mul] using
      cartanLorentzMatterSpinSourceCoefficient_smul source configuration
        scalar direction point

theorem cartanLorentzDual_eq_of_coordinate_eq
    (first second : Module.Dual ℝ LorentzBivectorOneForm)
    (coordinateEquality :
      ∀ formDirection internalPair,
        first (cartanLorentzCoordinateDirection formDirection internalPair) =
          second
            (cartanLorentzCoordinateDirection formDirection internalPair)) :
    first = second := by
  apply LinearMap.ext
  intro direction
  rw [← cartanLorentzCoordinateExpansion direction]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro formDirection _
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [coordinateEquality]

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_spinCoordinates :
    sourceActionGeneratedMatterSpinCoordinates positiveSmoothUnifiedSource
        positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 =
      positiveSourceMatterSpinCoordinatesNormalForm := by
  apply positiveSourceMatterSpinCoordinates_eq_normalForm_of_origin
  · exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0
  · exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_matter_origin
  · exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_conjugate_origin

theorem identitySimpleBCartanConnectionResponse_eq_of_origin
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm)
    (coframeOrigin : configuration.coframe 0 = 1)
    (auxiliaryOrigin :
      configuration.gravityAuxiliary 0 = physicalIIPlusBivector 1)
    (connectionOrigin :
      configuration.gravityConnection 0 =
        lorentzSkewConnectionOfBivectorOneForm q)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    identitySimpleBCartanConnectionResponseCoordinates q
        formDirection internalPair =
      -lorentzGravityBFAlgebraicCoefficient configuration
        (cartanLorentzCoordinateDirection formDirection internalPair) 0 := by
  have carrierCoframe :
      (identitySimpleBCartanConnectionCarrier q).coframe 0 = 1 := by
    rfl
  have carrierAuxiliary :
      (identitySimpleBCartanConnectionCarrier q).gravityAuxiliary 0 =
        physicalIIPlusBivector 1 := by
    rfl
  have algebraicCurvatureEquality :
      lorentzConnectionAlgebraicCurvatureDirection
          (identitySimpleBCartanConnectionCarrier q)
          (cartanLorentzCoordinateDirection formDirection internalPair) 0 =
        lorentzConnectionAlgebraicCurvatureDirection configuration
          (cartanLorentzCoordinateDirection formDirection internalPair) 0 := by
    funext candidateInternalPair candidateSpacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [connectionOrigin]
    rfl
  unfold identitySimpleBCartanConnectionResponseCoordinates
    lorentzGravityBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [carrierCoframe, carrierAuxiliary, coframeOrigin, auxiliaryOrigin,
    algebraicCurvatureEquality]

theorem
    positiveSourceActionGeneratedCartanConnection_basisBalance
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    lorentzGravityBFAlgebraicCoefficient
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          (cartanLorentzCoordinateDirection formDirection internalPair) 0 +
        lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          (cartanLorentzCoordinateDirection formDirection internalPair) 0 =
      0 := by
  have gravityResponse :=
    identitySimpleBCartanConnectionResponse_eq_of_origin
      positiveSourceActionGeneratedCartanConnectionLocalActualLift
      positiveSourceActionGeneratedCartanConnectionCoordinates
      (positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0)
      (positiveSourceActionGeneratedCartanConnectionLocalActualLift_auxiliary
        0)
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_connection_origin
      formDirection internalPair
  have generatedResponse := congrFun
    (congrFun
      positiveSourceActionGeneratedCartanConnection_satisfies_actionLaw
      formDirection)
    internalPair
  have targetSpinNormal := congrFun
    (congrFun positiveSourceMatterSpinCoordinates_eq_normalForm
      formDirection)
    internalPair
  have actualSpinNormal := congrFun
    (congrFun
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_spinCoordinates
      formDirection)
    internalPair
  unfold sourceActionGeneratedMatterSpinCoordinates at generatedResponse
  unfold sourceActionGeneratedMatterSpinCoordinates at targetSpinNormal
  unfold sourceActionGeneratedMatterSpinCoordinates at actualSpinNormal
  linarith

theorem
    positiveSourceActionGeneratedCartanConnection_algebraicBalance
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          direction 0 +
        lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          direction 0 =
      0 := by
  have dualEquality :
      -cartanLorentzGravityBFActionDual
          positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 =
        cartanLorentzMatterSpinActionDual positiveSmoothUnifiedSource
          positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 := by
    apply cartanLorentzDual_eq_of_coordinate_eq
    intro formDirection internalPair
    change
      -lorentzGravityBFAlgebraicCoefficient
            positiveSourceActionGeneratedCartanConnectionLocalActualLift
            (cartanLorentzCoordinateDirection formDirection internalPair) 0 =
        lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          (cartanLorentzCoordinateDirection formDirection internalPair) 0
    have basisBalance :=
      positiveSourceActionGeneratedCartanConnection_basisBalance
        formDirection internalPair
    linarith
  have evaluated := congrArg
    (fun response : Module.Dual ℝ LorentzBivectorOneForm =>
      response direction)
    dualEquality
  change
    -lorentzGravityBFAlgebraicCoefficient
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          direction 0 =
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        positiveSourceActionGeneratedCartanConnectionLocalActualLift
        direction 0 at evaluated
  linarith

theorem
    positiveSourceActionGeneratedCartanConnection_differentialMomentum_constant
    (direction : PhysicalBivector) :
    lorentzConnectionBFDifferentialMomentum
        positiveSourceActionGeneratedCartanConnectionLocalActualLift
        direction =
      fun _ =>
        lorentzConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          direction 0 := by
  funext point
  unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
    toContinuumPointField
  rw [
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe point,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_auxiliary
      point,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_auxiliary 0]

theorem
    positiveSourceActionGeneratedCartanConnection_divergence_zero
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveSourceActionGeneratedCartanConnectionLocalActualLift
        direction 0 =
      0 := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  rw [
    positiveSourceActionGeneratedCartanConnection_differentialMomentum_constant]
  simp [fieldDirectionalDerivative]

/-- Residual/action acceptance comes last: the already generated local actual
`U` satisfies the complete Lorentz connection Euler--Lagrange coefficient at
the origin for every bivector one-form direction. -/
theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_lorentzEulerLagrange_origin
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveSourceActionGeneratedCartanConnectionLocalActualLift
        direction 0 =
      0 := by
  rw [lorentzConnectionEulerLagrangeCoefficient,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    positiveSourceActionGeneratedCartanConnection_divergence_zero]
  simpa only [sub_zero] using
    positiveSourceActionGeneratedCartanConnection_algebraicBalance direction

/-- The C3h116 Cartan update does not alter the source-generated P286
connection path.  The relevant Cauchy-state projection is definitionally the
same as the primitive phase state, so the earlier zero-connection action
calculation transports without comparing whole configurations. -/
theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_gaugeConnection_eq_zero :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.gaugeConnection =
      0 := by
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveSourceActionGeneratedCartanConnectionCauchyState 0 =
      0
  rw [show
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveSourceActionGeneratedCartanConnectionCauchyState 0 =
      sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positivePhaseProbeCauchyState 0 by
    rfl]
  change positivePathFirstJointLocalActualLift.gaugeConnection = 0
  exact positivePathFirstJointLocalActualLift_gaugeConnection

/-- The scalar path is likewise inherited from the same primitive phase
state; only the Cartan connection coordinate was updated. -/
theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_scalar_eq_sourceVacuum :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField
        positiveSourceActionGeneratedCartanConnectionCauchyState 0 =
      _
  rw [show
    actionGeneratedScalarLocalField
        positiveSourceActionGeneratedCartanConnectionCauchyState 0 =
      actionGeneratedScalarLocalField positivePhaseProbeCauchyState 0 by
    rfl]
  change positivePathFirstJointLocalActualLift.scalar = _
  exact positivePathFirstJointLocalActualLift_scalar

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_scalarCovariantDerivative_eq_zero :
    holonomicScalarCovariantDerivative
        positiveSourceActionGeneratedCartanConnectionLocalActualLift =
      0 := by
  funext point direction
  rw [holonomicScalarCovariantDerivative,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_gaugeConnection_eq_zero,
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_scalar_eq_sourceVacuum]
  simp [fieldDirectionalDerivative]

/-- The same generated C3h116 actual also retains the primal
Dirac--Yukawa action law.  The comparison is made at the common source
contact with the matter-dual actual generated from the same Cauchy state;
no historical coframe-response endpoint is used. -/
theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_diracYukawa_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveSourceActionGeneratedCartanConnectionLocalActualLift 0) =
      0 := by
  let actual :=
    positiveSourceActionGeneratedCartanConnectionLocalActualLift
  let state :=
    positiveSourceActionGeneratedCartanConnectionCauchyState
  let matterBase :=
    sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource state 0
  have matterEqual : actual.matter = matterBase.matter := by
    rfl
  have actualScalarOrigin :
      actual.scalar 0 = state.scalar 0 := by
    change
      (sourceActionGeneratedMatterDualScalarLocalActualLift
        positiveSmoothUnifiedSource state 0).scalar 0 =
        state.scalar 0
    exact
      sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
        positiveSmoothUnifiedSource state 0
  have matterBaseScalarOrigin :
      matterBase.scalar 0 = state.scalar 0 := by
    change
      (sourceGeneratedP286ActionLocalActualLift
        positiveSmoothUnifiedSource state 0).scalar 0 =
        state.scalar 0
    exact
      sourceGeneratedP286ActionLocalActualLift_scalar_origin
        positiveSmoothUnifiedSource state 0
  have scalarOriginEqual :
      actual.scalar 0 = matterBase.scalar 0 :=
    actualScalarOrigin.trans matterBaseScalarOrigin.symm
  have gaugeConnectionEqual :
      actual.gaugeConnection = matterBase.gaugeConnection := by
    rfl
  have actualGravityConnectionOrigin :
      actual.gravityConnection 0 = state.gravityConnection 0 := by
    change
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource state 0).gravityConnection 0 =
        state.gravityConnection 0
    exact
      sourceActionGeneratedJointLocalActualLift_initialGravityConnection
        positiveSmoothUnifiedSource state 0
  have matterBaseGravityConnectionOrigin :
      matterBase.gravityConnection 0 = state.gravityConnection 0 := by
    change
      (sourceActionGeneratedGravityGaugeLocalActualLift
        positiveSmoothUnifiedSource state 0).gravityConnection 0 =
        state.gravityConnection 0
    exact
      sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
        positiveSmoothUnifiedSource state 0
  have gravityConnectionOriginEqual :
      actual.gravityConnection 0 = matterBase.gravityConnection 0 :=
    actualGravityConnectionOrigin.trans
      matterBaseGravityConnectionOrigin.symm
  have matterCovariantDerivativeEqual :
      holonomicMatterCovariantDerivative actual 0 =
        holonomicMatterCovariantDerivative matterBase 0 := by
    funext direction
    unfold holonomicMatterCovariantDerivative
    rw [matterEqual, gravityConnectionOriginEqual, gaugeConnectionEqual]
  have generatedVectorEqual :
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField actual 0) =
        generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField matterBase 0) := by
    unfold generatedContinuumMatterVector toContinuumPointField
    rw [show actual.coframe 0 = 1 by
      exact
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe
          0]
    rw [show matterBase.coframe 0 = 1 by rfl]
    rw [matterEqual, scalarOriginEqual, matterCovariantDerivativeEqual]
  have baseEquation :=
    sourceActionGeneratedMatterDualLocalActualLift_diracYukawa_origin
      positiveSmoothUnifiedSource state 0 (by rfl)
  change
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField actual 0) =
      0
  rw [generatedVectorEqual]
  exact baseEquation

/-- The positive frontier packages producer provenance before acceptance.
No equation witness is stored in the Cauchy source or actual constructor. -/
structure PositiveSourceActionGeneratedCartanConnectionLocalActualLaw :
    Prop where
  actionGeneratedConnection :
    identitySimpleBCartanConnectionResponseCoordinates
        positiveSourceActionGeneratedCartanConnectionCoordinates =
      sourceActionGeneratedMatterSpinCoordinates positiveSmoothUnifiedSource
        positiveSourceTargetMatterActual 0
  nonzeroConnection :
    positiveSourceActionGeneratedCartanConnectionCoordinates ≠ 0
  actualSmooth :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.Smooth
  actualNondegenerate :
    positiveSourceActionGeneratedCartanConnectionLocalActualLift.Nondegenerate
  actualSimplicity :
    StageNinePlebanskiMultiplierVariation.GravitySimplicityEquation
      positiveSourceActionGeneratedCartanConnectionLocalActualLift
  lorentzAcceptance :
    ∀ direction : LorentzBivectorOneForm,
      lorentzConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedCartanConnectionLocalActualLift
          direction 0 =
        0
  primalMatterAcceptance :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveSourceActionGeneratedCartanConnectionLocalActualLift 0) =
      0

theorem
    positiveSourceActionGeneratedCartanConnectionLocalActualLift_realizes_C3h116 :
    PositiveSourceActionGeneratedCartanConnectionLocalActualLaw := by
  exact
    { actionGeneratedConnection :=
        positiveSourceActionGeneratedCartanConnection_satisfies_actionLaw
      nonzeroConnection :=
        positiveSourceActionGeneratedCartanConnection_nonzero
      actualSmooth :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_smooth
      actualNondegenerate :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_nondegenerate
      actualSimplicity :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_simplicity
      lorentzAcceptance :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_lorentzEulerLagrange_origin
      primalMatterAcceptance :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_diracYukawa_origin }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCartanConnectionLocalActualLift
