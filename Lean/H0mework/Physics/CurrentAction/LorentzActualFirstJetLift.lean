import H0mework.Physics.Coframe.CoframeTwoFormPairing
import H0mework.Physics.CurrentAction.LorentzDualResponse
import H0mework.Physics.GaugeAction.P286ActionVelocityLocalActualLift

/-!
# Stage-9 current canonical Lorentz actual first-jet lift

This checkpoint realizes the complete C3h188 Lorentz canonical response by a
family of honest local holonomic configurations.  The existing
linear-Plebanski connection germ supplies the connection leg.  The momentum
leg is installed by the canonical identity-coframe BF Legendre section on the
18 spatial Cauchy coordinates:

```text
(source, current, contact)
-> C3h188 action-owned finite Lorentz dual
-> fixed-sign minimal spatial auxiliary jet
-> one local holonomic actual at that same contact.
```

The section has no coefficient, branch, residual, preimage witness, equation
receipt, endpoint, event, or scheduler input.  It changes the time first jet
of the already existing gravity auxiliary field; it does not add a new field
or a source slot.  The result is a holonomic first-jet lift.  Tangent
simplicity and the temporal Lorentz Gauss equation remain independent
downstream constraints and are not claimed here.

The local coordinate called `time` below is only the fixed Cauchy chart
parameter.  Nothing in this module defines an event tick, restart law,
semigroup, branch selection, or global source-time evolution.  Future
source-owned event provenance may wrap the operator opaquely but may not be
read by it.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeTwoFormPairing
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Identity-coframe spatial BF Legendre section -/

/-- The last three two-form slots are canonically `(23, 31, 12)`. -/
def spatialSpatialPair (direction : Fin 3) : Fin 6 :=
  ⟨direction.val + 3, by omega⟩

@[simp] private theorem canonicalLorentzSpatialBivectorOneForm_one
    (direction : LorentzSpatialBivectorDirection) :
    canonicalLorentzSpatialBivectorOneForm direction 1 = direction 0 :=
  canonicalLorentzSpatialBivectorOneForm_spatial direction 0

@[simp] private theorem canonicalLorentzSpatialBivectorOneForm_two
    (direction : LorentzSpatialBivectorDirection) :
    canonicalLorentzSpatialBivectorOneForm direction 2 = direction 1 :=
  canonicalLorentzSpatialBivectorOneForm_spatial direction 1

@[simp] private theorem canonicalLorentzSpatialBivectorOneForm_three
    (direction : LorentzSpatialBivectorDirection) :
    canonicalLorentzSpatialBivectorOneForm direction 3 = direction 2 :=
  canonicalLorentzSpatialBivectorOneForm_spatial direction 2

/-- The temporal exterior derivative of a spatial Lorentz one-form occupies
exactly the `(01, 02, 03)` spacetime two-form coordinates. -/
theorem lorentzTimeExteriorSpatialDirection_normalForm
    (direction : LorentzSpatialBivectorDirection) :
    lorentzConnectionExteriorDerivativeDirection
        canonicalLorentzianTimeDirection
        (canonicalLorentzSpatialBivectorOneForm direction) =
      fun internalPair =>
        ![direction 0 internalPair, direction 1 internalPair,
          direction 2 internalPair, 0, 0, 0] := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [lorentzConnectionExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      minkowskiInternalSign, pairFirst, pairSecond,
      Fin.sum_univ_six]

/-- Explicit identity-coframe normal form of the temporal spatial BF
Legendre pairing. -/
theorem identityLorentzSpatialBFLegendre_normalForm
    (auxiliary : PhysicalBivector)
    (direction : LorentzSpatialBivectorDirection) :
    gravityAuxiliaryHodgePairingPolynomial 1 auxiliary
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      -(∑ spatial : Fin 3,
        ∑ internalPair : Fin 6,
          lorentzianTwoFormSign internalPair *
            auxiliary internalPair (spatialSpatialPair spatial) *
            direction spatial internalPair) := by
  unfold gravityAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  rw [lorentzTimeExteriorSpatialDirection_normalForm]
  rw [Fin.sum_univ_six, Fin.sum_univ_three]
  simp [spatialSpatialPair,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    Fin.sum_univ_six]
  ring

/-- Canonical minimal-support inverse of the identity-coframe Lorentz BF
Legendre map on the 18 spatial Cauchy coordinates. -/
def lorentzSpatialAuxiliaryVelocityEmbedding
    (velocity : LorentzSpatialBivectorDirection) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    ![0, 0, 0,
      -lorentzianTwoFormSign internalPair * velocity 0 internalPair,
      -lorentzianTwoFormSign internalPair * velocity 1 internalPair,
      -lorentzianTwoFormSign internalPair * velocity 2 internalPair]
      spacetimePair

/-- The fixed-sign embedding is a right inverse of the complete temporal
spatial BF pairing, on every test direction at once. -/
theorem identityLorentzSpatialBFLegendre_embedding
    (velocity direction : LorentzSpatialBivectorDirection) :
    gravityAuxiliaryHodgePairingPolynomial 1
        (lorentzSpatialAuxiliaryVelocityEmbedding velocity)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      ∑ spatial : Fin 3,
        ∑ internalPair : Fin 6,
          velocity spatial internalPair * direction spatial internalPair := by
  rw [identityLorentzSpatialBFLegendre_normalForm]
  simp_rw [Fin.sum_univ_three, Fin.sum_univ_six]
  simp [lorentzSpatialAuxiliaryVelocityEmbedding, spatialSpatialPair,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]
  ring

/-- No auxiliary velocity coordinate is erased by the canonical embedding. -/
theorem lorentzSpatialAuxiliaryVelocityEmbedding_injective :
    Function.Injective lorentzSpatialAuxiliaryVelocityEmbedding := by
  intro first second equality
  funext spatial internalPair
  have coordinate := congrFun (congrFun equality internalPair)
    (spatialSpatialPair spatial)
  fin_cases spatial <;> fin_cases internalPair <;>
    simpa [lorentzSpatialAuxiliaryVelocityEmbedding, spatialSpatialPair,
      lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]
      using coordinate

/-! ## Source/action-generated local actual family -/

/-- The unique 18 auxiliary coordinates selected by the C3h188 finite dual
at one contact. -/
def currentCanonicalFullActionLorentzAuxiliaryVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : PhysicalBivector :=
  lorentzSpatialAuxiliaryVelocityEmbedding
    (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
      source current space)

/-- Install the action-owned Lorentz momentum first jet on the same fresh
actual that already carries the linear-Plebanski connection germ. -/
def currentCanonicalFullActionLorentzActualFirstJetLift
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  { currentCanonicalGravityPreservingActual source current space with
    gravityAuxiliary := fun point =>
      (currentCanonicalGravityPreservingActual source current
          space).gravityAuxiliary point +
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          currentCanonicalFullActionLorentzAuxiliaryVelocity source current
            space }

/-- The installer changes only the existing gravity-auxiliary field. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_retainsPrimitiveFields
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).coframe =
        (currentCanonicalGravityPreservingActual source current space).coframe ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravityConnection =
        (currentCanonicalGravityPreservingActual source current
          space).gravityConnection ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravitySimplicityMultiplier =
        (currentCanonicalGravityPreservingActual source current
          space).gravitySimplicityMultiplier ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gaugeConnection =
        (currentCanonicalGravityPreservingActual source current
          space).gaugeConnection ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gaugeAuxiliary =
        (currentCanonicalGravityPreservingActual source current
          space).gaugeAuxiliary ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).scalar =
        (currentCanonicalGravityPreservingActual source current space).scalar ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).matter =
        (currentCanonicalGravityPreservingActual source current space).matter ∧
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).conjugateMatter =
        (currentCanonicalGravityPreservingActual source current
          space).conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_gravityAuxiliary_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravityAuxiliary 0 =
      (currentCanonicalGravityPreservingActual source current
        space).gravityAuxiliary 0 := by
  simp [currentCanonicalFullActionLorentzActualFirstJetLift,
    localBaseCoordinate_apply]

/-- The fresh C3h188 base actual is smooth for every primitive current. -/
theorem currentCanonicalGravityPreservingActual_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current space).Smooth := by
  apply actionGeneratedMatterCompleteFirstGermActual_smooth
  apply actionGeneratedMatterTemporalFirstGermActual_smooth
  apply currentP286CompleteActionResponseOperator_smooth
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
    source current space

/-- The local first-jet installer is smooth; no regularity receipt is carried
by the source or supplied to the constructor. -/
theorem currentCanonicalFullActionLorentzActualFirstJetLift_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Smooth := by
  have baseSmooth :=
    currentCanonicalGravityPreservingActual_smooth source current space
  rcases baseSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateSmooth⟩
  refine ⟨coframeSmooth, connectionSmooth, ?_, multiplierSmooth,
    gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateSmooth⟩
  intro internalPair spacetimePair
  simpa only [currentCanonicalFullActionLorentzActualFirstJetLift,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    (auxiliarySmooth internalPair spacetimePair).add
      ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff.mul
        contDiff_const)

/-- Under the identity-coframe sector selected by the exact P506/L0 current,
the whole installed actual has the same identity coframe. -/
theorem currentCanonicalFullActionLorentzActualFirstJetLift_coframe_one
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (point : BasePoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).coframe point = 1 := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift source current
      space).coframe point =
      1
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    identityCoframe]

/-- Identity coframe also discharges nondegeneracy for the full local actual. -/
theorem currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Nondegenerate := by
  intro point
  rw [currentCanonicalFullActionLorentzActualFirstJetLift_coframe_one
    source current space identityCoframe point]
  simp

/-- The gravity auxiliary of the C3h188 base actual is contact-generated and
constant on its local spacetime germ. -/
theorem currentCanonicalGravityPreservingActual_gravityAuxiliary_point
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (currentCanonicalGravityPreservingActual source current
        space).gravityAuxiliary point =
      actionGeneratedGravityAuxiliary current space := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift source current
      space).gravityAuxiliary point =
      actionGeneratedGravityAuxiliary current space
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary
    source current space point

/-- Along the canonical local time axis, the installed auxiliary field is
exactly the base value plus the action-owned first jet. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_gravityAuxiliary_timeAxis
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : Real) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravityAuxiliary (canonicalCauchySlicePoint time 0) =
      actionGeneratedGravityAuxiliary current space +
        time • currentCanonicalFullActionLorentzAuxiliaryVelocity source
          current space := by
  change
    (currentCanonicalGravityPreservingActual source current
        space).gravityAuxiliary (canonicalCauchySlicePoint time 0) +
      localBaseCoordinate canonicalLorentzianTimeDirection
          (canonicalCauchySlicePoint time 0) •
        currentCanonicalFullActionLorentzAuxiliaryVelocity source current
          space =
      _
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary_point]
  simp [localBaseCoordinate_apply]

/-- Polynomial BF pairing is affine in its auxiliary input. -/
theorem gravityAuxiliaryHodgePairingPolynomial_add_smul_left
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (base velocity direction : PhysicalBivector)
    (scalar : Real) :
    gravityAuxiliaryHodgePairingPolynomial coframe
        (base + scalar • velocity) direction =
      gravityAuxiliaryHodgePairingPolynomial coframe base direction +
        scalar *
          gravityAuxiliaryHodgePairingPolynomial coframe velocity direction := by
  rw [gravityAuxiliaryHodgePairingPolynomial_eq coframe nondegenerate,
    gravityAuxiliaryHodgePairingPolynomial_eq coframe nondegenerate,
    gravityAuxiliaryHodgePairingPolynomial_eq coframe nondegenerate,
    gravityCoframePairing_add_left,
    gravityCoframePairing_smul_left]

/-- At identity coframe, the complete C3h188 dual is exactly the BF pairing
with the canonically embedded auxiliary velocity. -/
theorem currentCanonicalFullActionLorentzAuxiliaryVelocity_pairing
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    gravityAuxiliaryHodgePairingPolynomial 1
        (currentCanonicalFullActionLorentzAuxiliaryVelocity source current
          space)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source current
        space direction := by
  unfold currentCanonicalFullActionLorentzAuxiliaryVelocity
  rw [identityLorentzSpatialBFLegendre_embedding]
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumVelocity
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocityDual
    lorentzSpatialBivectorLinearExtension
  change
    (∑ spatial : Fin 3,
      ∑ internalPair : Fin 6,
        currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
            source current space spatial internalPair *
          direction spatial internalPair) =
      ∑ spatial : Fin 3,
        ∑ internalPair : Fin 6,
          direction spatial internalPair *
            currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
              source current space spatial internalPair
  apply Finset.sum_congr rfl
  intro spatial _
  apply Finset.sum_congr rfl
  intro internalPair _
  ring

/-- In the identity-coframe sector, the initial C3h188 momentum readout has
the corresponding polynomial normal form. -/
theorem
    currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation_identity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation source current
        space direction =
      gravityAuxiliaryHodgePairingPolynomial 1
        (actionGeneratedGravityAuxiliary current space)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) := by
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation
    currentCanonicalFullActionLorentzBFMomentumEvaluation
    lorentzConnectionBFDifferentialMomentum
  dsimp only
  have baseCoframe :
      (currentCanonicalGravityPreservingActual source current space).coframe
          0 =
        1 := by
    change
      (sourceActionGeneratedLinearPlebanskiJointLocalActualLift source current
        space).coframe 0 =
        1
    rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
      identityCoframe]
  change
    |Matrix.det
        ((currentCanonicalGravityPreservingActual source current space).coframe
          0)| *
        gravityAuxiliaryHodgePairingPolynomial
          ((currentCanonicalGravityPreservingActual source current
            space).coframe 0)
          ((currentCanonicalGravityPreservingActual source current
            space).gravityAuxiliary 0)
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)) =
      gravityAuxiliaryHodgePairingPolynomial 1
        (actionGeneratedGravityAuxiliary current space)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
  rw [baseCoframe,
    currentCanonicalGravityPreservingActual_gravityAuxiliary_point]
  simp

/-- The same local actual realizes the complete affine BF-momentum response
on every spatial Lorentz test direction, not merely on basis probes. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_BFMomentum_timeAxis
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (time : Real)
    (direction : LorentzSpatialBivectorDirection) :
    lorentzConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
        (canonicalCauchySlicePoint time 0) =
      currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation source
          current space direction +
        time *
          currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
            current space direction := by
  have liftCoframe :
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space).coframe (canonicalCauchySlicePoint time 0) =
        1 :=
    currentCanonicalFullActionLorentzActualFirstJetLift_coframe_one
      source current space identityCoframe _
  unfold lorentzConnectionBFDifferentialMomentum
  change
    |Matrix.det
        ((currentCanonicalFullActionLorentzActualFirstJetLift source current
          space).coframe (canonicalCauchySlicePoint time 0))| *
        gravityAuxiliaryHodgePairingPolynomial
          ((currentCanonicalFullActionLorentzActualFirstJetLift source current
            space).coframe (canonicalCauchySlicePoint time 0))
          ((currentCanonicalFullActionLorentzActualFirstJetLift source current
            space).gravityAuxiliary (canonicalCauchySlicePoint time 0))
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)) =
      _
  rw [liftCoframe]
  rw [
    currentCanonicalFullActionLorentzActualFirstJetLift_gravityAuxiliary_timeAxis]
  simp only [Matrix.det_one, abs_one, one_mul]
  rw [gravityAuxiliaryHodgePairingPolynomial_add_smul_left
      (1 : LorentzianCoframe) (by simp),
    currentCanonicalFullActionLorentzAuxiliaryVelocity_pairing,
    ← currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation_identity
      source current space identityCoframe direction]

/-- The retained linear-Plebanski connection germ realizes the complete
affine connection half of C3h188 along the same local time axis. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_connection_timeAxis
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : Real)
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((currentCanonicalFullActionLorentzActualFirstJetLift source current
          space).gravityConnection (canonicalCauchySlicePoint time 0))
        spatialDirection.succ internalPair =
      sourceActionGeneratedLorentzSpatialConnectionCoordinate current space
          spatialDirection internalPair +
        time *
          linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity
            current space spatialDirection internalPair := by
  change
    loweredLorentzConnectionCoefficient
        (linearPlebanskiActionGeneratedLorentzLocalConnection current space
          (canonicalCauchySlicePoint time 0))
        spatialDirection.succ internalPair =
      _
  rw [linearPlebanskiActionGeneratedLorentzLocalConnection_loweredCoordinate]
  unfold linearPlebanskiActionGeneratedLorentzLocalConnectionCoordinate
    sourceActionGeneratedLorentzSpatialConnectionCoordinate
    loweredLorentzConnectionCoefficient
  congr 1
  fin_cases spatialDirection <;>
    simp [linearPlebanskiActionGeneratedLorentzLocalIncrement,
      linearPlebanskiActionGeneratedLorentzLocalConnectionJet,
      localBaseCoordinate, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection,
      Fin.sum_univ_four, Fin.sum_univ_three]

/-! ## Complete same-actual phase readout -/

/-- Read both Lorentz canonical legs from the same generated family of local
holonomic actuals at the same time-axis point of every contact. -/
def currentCanonicalFullActionLorentzActualFirstJetPhaseReadout
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real) : StageNineLorentzCanonicalPhaseState where
  spatialConnection := fun space spatialDirection internalPair =>
    loweredLorentzConnectionCoefficient
      ((currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravityConnection (canonicalCauchySlicePoint time 0))
      spatialDirection.succ internalPair
  spatialBFMomentumEvaluation := fun space direction =>
    lorentzConnectionBFDifferentialMomentum
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space)
      (lorentzConnectionExteriorDerivativeDirection
        canonicalLorentzianTimeDirection
        (canonicalLorentzSpatialBivectorOneForm direction))
      (canonicalCauchySlicePoint time 0)

/-- Positive reachability theorem for the complete synchronized Lorentz
response: under the identity coframe generated by the exact current sector,
one and the same actual family realizes both C3h188 canonical legs for every
contact, time parameter, and test direction. -/
theorem currentCanonicalFullActionLorentzActualFirstJetPhaseReadout_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (identityCoframe : ∀ space, current.coframe space = 1)
    (time : Real) :
    currentCanonicalFullActionLorentzActualFirstJetPhaseReadout source current
        time =
      currentCanonicalFullActionLorentzCanonicalPhaseUpdate source current
        time := by
  apply StageNineLorentzCanonicalPhaseState.ext
  · funext space spatialDirection internalPair
    change
      loweredLorentzConnectionCoefficient
          ((currentCanonicalFullActionLorentzActualFirstJetLift source current
            space).gravityConnection (canonicalCauchySlicePoint time 0))
          spatialDirection.succ internalPair =
        sourceActionGeneratedLorentzSpatialConnectionCoordinate current space
            spatialDirection internalPair +
          time *
            linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity
              current space spatialDirection internalPair
    exact
      currentCanonicalFullActionLorentzActualFirstJetLift_connection_timeAxis
        source current space time spatialDirection internalPair
  · funext space direction
    change
      lorentzConnectionBFDifferentialMomentum
          (currentCanonicalFullActionLorentzActualFirstJetLift source current
            space)
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction))
          (canonicalCauchySlicePoint time 0) =
        currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation source
            current space direction +
          time *
            currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
              current space direction
    exact
      currentCanonicalFullActionLorentzActualFirstJetLift_BFMomentum_timeAxis
        source current space (identityCoframe space) time direction

/-- Actual-level faithful zero fiber.  The unit local response is fixed
exactly when the complete source/action-generated Lorentz phase velocity
vanishes. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetPhaseReadout_unit_eq_initial_iff
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (identityCoframe : ∀ space, current.coframe space = 1) :
    currentCanonicalFullActionLorentzActualFirstJetPhaseReadout source current
          1 =
        currentCanonicalFullActionLorentzActualFirstJetPhaseReadout source
          current 0 ↔
      currentCanonicalFullActionLorentzCanonicalPhaseVelocity source current =
        zeroLorentzCanonicalPhaseVelocity := by
  rw [currentCanonicalFullActionLorentzActualFirstJetPhaseReadout_realizes
      source current identityCoframe 1,
    currentCanonicalFullActionLorentzActualFirstJetPhaseReadout_realizes
      source current identityCoframe 0,
    currentCanonicalFullActionLorentzCanonicalPhaseUpdate_zero]
  exact
    currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate_eq_initial_iff
      source current

end

end SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
