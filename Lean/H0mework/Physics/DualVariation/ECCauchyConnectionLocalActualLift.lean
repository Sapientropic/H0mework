import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift
import H0mework.Physics.IdentityGerms.IdentityECLoad
import H0mework.Physics.IdentityGerms.IdentityECTemporalEvolutionSection
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation

/-!
# Repaired-root EC Cauchy connection write

The identity-contact Einstein--Cartan coframe equation splits into twelve
spatial-column evolution rows and four temporal-column constraints.  This
module turns the algebraic temporal section into a primitive Lorentz
connection germ.

For a source and a current actual, the repaired action itself determines the
twelve desired rows.  The constructor preserves the current origin
connection and every current lowered first-jet coordinate except the eighteen
`partial_0 omega_i` coordinates.  The canonical section changes only their
twelve-dimensional observable subspace while the six-dimensional electric
kernel and all spatial curvature coordinates are transported unchanged.

No response, target curvature, inverse witness, constraint certificate,
branch choice, coefficient, or stationarity receipt is accepted.  The four
constraints remain downstream readouts.  This is a current-state local
Cauchy write, not yet an iterated development or a neighborhood solution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Action-owned evolution target -/

/-- The twelve curvature rows forced by the live repaired-root load. -/
def diracDualFormNativeECDesiredEvolutionObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    IdentityECSpatialCoframeCovectorCoordinates :=
  -identityECSpatialCoframeCoordinatesOfCovector
    (diracDualFormNativeIdentityECLoad source current)

/-- Current curvature after recomputing the holonomic `II+` branch. -/
def diracDualFormNativeECCauchyCurrentCurvature
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  holonomicGravityCurvature
    (diracDualFormNativeECNormalPreparedActual current) 0

/-- Branch-free curvature target: solve the twelve evolution rows while
preserving the four constraints, all spatial curvature, and the electric
kernel. -/
def diracDualFormNativeECCauchyCurvatureTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  identityDiracDualECTotalEvolutionCurvatureTarget
    (diracDualFormNativeECCauchyCurrentCurvature current)
    (diracDualFormNativeECDesiredEvolutionObservation source current)

/-- The temporal-curvature increment read from current and target.  It is a
derived action write, not a constructor input. -/
def diracDualFormNativeECTemporalCurvatureIncrement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    IdentityECTemporalCurvatureCoordinates :=
  identityECTemporalCurvatureCoordinatesOf
      (diracDualFormNativeECCauchyCurvatureTarget source current) -
    identityECTemporalCurvatureCoordinatesOf
      (diracDualFormNativeECCauchyCurrentCurvature current)

private def ecTemporalCoordinatesLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECTemporalCurvatureCoordinates where
  toFun := identityECTemporalCurvatureCoordinatesOf
  map_add' := identityECTemporalCurvatureCoordinatesOf_add
  map_smul' := by intro parameter curvature; rfl

private def ecTemporalCurvatureLinearMap :
    IdentityECTemporalCurvatureCoordinates →ₗ[ℝ] PhysicalBivector where
  toFun := identityECTemporalCurvatureOfCoordinates
  map_add' := identityECTemporalCurvatureOfCoordinates_add
  map_smul' := by
    intro parameter coordinates
    funext internalPair spacetimePair
    fin_cases spacetimePair <;>
      simp [identityECTemporalCurvatureOfCoordinates]

private def ecTemporalObservationLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECSpatialCoframeCovectorCoordinates where
  toFun := identityDiracDualECTemporalEvolutionObservation
  map_add' := identityDiracDualECTemporalEvolutionObservation_add
  map_smul' := by
    intro parameter curvature
    funext row direction
    unfold identityDiracDualECTemporalEvolutionObservation
      identityDiracDualECCurvatureObservation
    change
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
            (coframeCoordinateDirection row direction.succ))
          (gravityInternalPairVarianceNormalization (parameter • curvature)) =
        parameter *
          gravityTopologicalWedgeCoefficient
            (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
              (coframeCoordinateDirection row direction.succ))
            (gravityInternalPairVarianceNormalization curvature)
    rw [map_smul, gravityTopologicalWedgeCoefficient_smul_right]

private def ecTemporalSectionCoordinatesLinearMap :
    IdentityECSpatialCoframeCovectorCoordinates →ₗ[ℝ]
      IdentityECTemporalCurvatureCoordinates where
  toFun := identityDiracDualECTemporalEvolutionSectionCoordinates
  map_add' := identityDiracDualECTemporalEvolutionSectionCoordinates_add
  map_smul' := by
    intro parameter response
    funext internalPair direction
    fin_cases internalPair <;> fin_cases direction <;>
      simp [identityDiracDualECTemporalEvolutionSectionCoordinates] <;> ring

private def ecSpatialCurvatureLinearMap :
    PhysicalBivector →ₗ[ℝ] PhysicalBivector :=
  LinearMap.id - ecTemporalCurvatureLinearMap.comp
    ecTemporalCoordinatesLinearMap

private def ecSpatialObservationLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECSpatialCoframeCovectorCoordinates :=
  ecTemporalObservationLinearMap.comp ecSpatialCurvatureLinearMap

private def ecTemporalKernelLinearMap :
    IdentityECTemporalCurvatureCoordinates →ₗ[ℝ]
      IdentityECTemporalCurvatureCoordinates :=
  LinearMap.id -
    ecTemporalSectionCoordinatesLinearMap.comp
      (ecTemporalObservationLinearMap.comp ecTemporalCurvatureLinearMap)

private theorem ecSpatialObservationLinearMap_apply
    (curvature : PhysicalBivector) :
    ecSpatialObservationLinearMap curvature =
      identityDiracDualECTemporalEvolutionObservation
        (identityECSpatialCurvaturePart curvature) := by
  rfl

private theorem ecTemporalKernelLinearMap_apply
    (coordinates : IdentityECTemporalCurvatureCoordinates) :
    ecTemporalKernelLinearMap coordinates =
      identityDiracDualECTemporalEvolutionKernelPart coordinates := by
  rfl

/-- Algebraic normal form of the generated Cauchy increment.  It exposes
only continuous linear operations on the current curvature and desired
action rows, so fixed-contact regularity proofs need not unfold the finite
coordinate section. -/
theorem diracDualFormNativeECTemporalCurvatureIncrement_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECTemporalCurvatureIncrement source current =
      ecTemporalKernelLinearMap
          (ecTemporalCoordinatesLinearMap
            (diracDualFormNativeECCauchyCurrentCurvature current)) +
        ecTemporalSectionCoordinatesLinearMap
          (diracDualFormNativeECDesiredEvolutionObservation source current -
            ecSpatialObservationLinearMap
              (diracDualFormNativeECCauchyCurrentCurvature current)) -
        ecTemporalCoordinatesLinearMap
          (diracDualFormNativeECCauchyCurrentCurvature current) := by
  funext internalPair direction
  unfold diracDualFormNativeECTemporalCurvatureIncrement
    diracDualFormNativeECCauchyCurvatureTarget
    identityECTemporalCurvatureCoordinatesOf
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [identityDiracDualECTotalEvolutionCurvatureTarget_temporal]
  rfl

/-- Current-curvature and desired-row germs of any common differentiability
order generate a temporal Cauchy increment germ of that same order.  This is
a readout regularity theorem for the source/current-only writer, not an extra
producer premise. -/
theorem diracDualFormNativeECTemporalCurvatureIncrement_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (source : SmoothUnifiedSource)
    (current : E → StageNineHolonomicConfiguration)
    (center : E)
    (curvatureRegular : ContDiffAt ℝ n
      (fun point =>
        diracDualFormNativeECCauchyCurrentCurvature (current point)) center)
    (desiredRegular : ContDiffAt ℝ n
      (fun point =>
        diracDualFormNativeECDesiredEvolutionObservation source
          (current point)) center) :
    ContDiffAt ℝ n (fun point =>
      diracDualFormNativeECTemporalCurvatureIncrement source
        (current point)) center := by
  have coordinatesRegular : ContDiffAt ℝ n (fun point =>
      ecTemporalCoordinatesLinearMap
        (diracDualFormNativeECCauchyCurrentCurvature (current point))) center :=
    ecTemporalCoordinatesLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp
      center curvatureRegular
  have spatialObservationRegular : ContDiffAt ℝ n (fun point =>
      ecSpatialObservationLinearMap
        (diracDualFormNativeECCauchyCurrentCurvature (current point))) center :=
    ecSpatialObservationLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp
      center curvatureRegular
  have responseRegular : ContDiffAt ℝ n (fun point =>
      diracDualFormNativeECDesiredEvolutionObservation source
          (current point) -
        ecSpatialObservationLinearMap
          (diracDualFormNativeECCauchyCurrentCurvature (current point))) center :=
    desiredRegular.sub spatialObservationRegular
  rw [show
    (fun point =>
      diracDualFormNativeECTemporalCurvatureIncrement source
        (current point)) =
      fun point =>
        ecTemporalKernelLinearMap
            (ecTemporalCoordinatesLinearMap
              (diracDualFormNativeECCauchyCurrentCurvature (current point))) +
          ecTemporalSectionCoordinatesLinearMap
            (diracDualFormNativeECDesiredEvolutionObservation source
                (current point) -
              ecSpatialObservationLinearMap
                (diracDualFormNativeECCauchyCurrentCurvature
                  (current point))) -
          ecTemporalCoordinatesLinearMap
            (diracDualFormNativeECCauchyCurrentCurvature (current point)) by
    funext point
    exact diracDualFormNativeECTemporalCurvatureIncrement_normalForm
      source (current point)]
  exact
    ((ecTemporalKernelLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp
      center coordinatesRegular).add
      (ecTemporalSectionCoordinatesLinearMap.toContinuousLinearMap.contDiff
        |>.contDiffAt.comp center responseRegular)).sub coordinatesRegular

/-- Continuous current-curvature and desired-row germs generate a continuous
temporal Cauchy increment germ. -/
theorem diracDualFormNativeECTemporalCurvatureIncrement_contDiffAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource)
    (current : E → StageNineHolonomicConfiguration)
    (center : E)
    (curvatureRegular : ContDiffAt ℝ 0
      (fun point =>
        diracDualFormNativeECCauchyCurrentCurvature (current point)) center)
    (desiredRegular : ContDiffAt ℝ 0
      (fun point =>
        diracDualFormNativeECDesiredEvolutionObservation source
          (current point)) center) :
    ContDiffAt ℝ 0 (fun point =>
      diracDualFormNativeECTemporalCurvatureIncrement source
        (current point)) center :=
  diracDualFormNativeECTemporalCurvatureIncrement_contDiffAt
    source current center curvatureRegular desiredRegular

theorem diracDualFormNativeECCauchyCurvatureTarget_eq_current_add_increment
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECCauchyCurvatureTarget source current =
      diracDualFormNativeECCauchyCurrentCurvature current +
        identityECTemporalCurvatureOfCoordinates
          (diracDualFormNativeECTemporalCurvatureIncrement source current) := by
  funext internalPair spacetimePair
  fin_cases spacetimePair
  · simp [diracDualFormNativeECTemporalCurvatureIncrement,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECTemporalSpatialPair]
  · simp [diracDualFormNativeECTemporalCurvatureIncrement,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECTemporalSpatialPair]
  · simp [diracDualFormNativeECTemporalCurvatureIncrement,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECTemporalSpatialPair]
  · simpa [diracDualFormNativeECCauchyCurvatureTarget,
      identityECSpatialSpatialPair,
      identityECTemporalCurvatureOfCoordinates] using
      identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (diracDualFormNativeECCauchyCurrentCurvature current)
        (diracDualFormNativeECDesiredEvolutionObservation source current)
        internalPair 0
  · simpa [diracDualFormNativeECCauchyCurvatureTarget,
      identityECSpatialSpatialPair,
      identityECTemporalCurvatureOfCoordinates] using
      identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (diracDualFormNativeECCauchyCurrentCurvature current)
        (diracDualFormNativeECDesiredEvolutionObservation source current)
        internalPair 1
  · simpa [diracDualFormNativeECCauchyCurvatureTarget,
      identityECSpatialSpatialPair,
      identityECTemporalCurvatureOfCoordinates] using
      identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (diracDualFormNativeECCauchyCurrentCurvature current)
        (diracDualFormNativeECDesiredEvolutionObservation source current)
        internalPair 2

/-! ## Temporal-only first-jet write -/

/-- Current lowered Lorentz first jet at the shared contact. -/
def diracDualFormNativeECCurrentLoweredConnectionJet
    (current : StageNineHolonomicConfiguration)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst internalPair) *
    gravityConnectionDerivative
      (diracDualFormNativeECNormalPreparedActual current) 0
      derivativeDirection formDirection
      (pairFirst internalPair) (pairSecond internalPair)

/-- Preserve the whole current first jet except for the eighteen
`partial_0 omega_i` coordinates.  Their twelve-dimensional observable
component is replaced and their six-dimensional kernel component is retained. -/
def diracDualFormNativeECCauchyConnectionJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  ![
    ![
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 0
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 1
          internalPair +
        diracDualFormNativeECTemporalCurvatureIncrement source current
          internalPair 0,
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 2
          internalPair +
        diracDualFormNativeECTemporalCurvatureIncrement source current
          internalPair 1,
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 3
          internalPair +
        diracDualFormNativeECTemporalCurvatureIncrement source current
          internalPair 2
    ],
    ![
      diracDualFormNativeECCurrentLoweredConnectionJet current 1 0
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 1 1
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 1 2
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 1 3
        internalPair
    ],
    ![
      diracDualFormNativeECCurrentLoweredConnectionJet current 2 0
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 2 1
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 2 2
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 2 3
        internalPair
    ],
    ![
      diracDualFormNativeECCurrentLoweredConnectionJet current 3 0
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 3 1
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 3 2
        internalPair,
      diracDualFormNativeECCurrentLoweredConnectionJet current 3 3
        internalPair
    ]
  ] derivativeDirection formDirection

theorem diracDualFormNativeECCauchyConnectionJet_temporalSpatial
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    diracDualFormNativeECCauchyConnectionJet source current 0 direction.succ
        internalPair =
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 direction.succ
          internalPair +
        diracDualFormNativeECTemporalCurvatureIncrement source current
          internalPair direction := by
  fin_cases direction <;> rfl

theorem diracDualFormNativeECCauchyConnectionJet_temporalTime
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internalPair : Fin 6) :
    diracDualFormNativeECCauchyConnectionJet source current 0 0 internalPair =
      diracDualFormNativeECCurrentLoweredConnectionJet current 0 0
        internalPair := by
  rfl

/-- Every spatial-derivative row of the current first jet is copied
literally; only the temporal derivative row can change. -/
theorem diracDualFormNativeECCauchyConnectionJet_spatialDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (derivativeDirection : Fin 3)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    diracDualFormNativeECCauchyConnectionJet source current
        derivativeDirection.succ formDirection internalPair =
      diracDualFormNativeECCurrentLoweredConnectionJet current
        derivativeDirection.succ formDirection internalPair := by
  fin_cases derivativeDirection <;> fin_cases formDirection <;> rfl

def diracDualFormNativeECCauchyConnectionIncrement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) : BasePoint →L[ℝ] ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (diracDualFormNativeECCauchyConnectionJet source current
        derivativeDirection formDirection internalPair)

def diracDualFormNativeECCauchyBivectorIncrement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    diracDualFormNativeECCauchyConnectionIncrement source current
      formDirection internalPair point

/-- Primitive affine germ carrying the repaired-root Cauchy write. -/
def diracDualFormNativeECCauchyConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : LorentzConnectionField :=
  fun point =>
    (diracDualFormNativeECNormalPreparedActual current).gravityConnection 0 +
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeECCauchyBivectorIncrement source current point)

@[simp] theorem diracDualFormNativeECCauchyConnection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECCauchyConnection source current 0 =
      current.gravityConnection 0 := by
  have incrementZero :
      diracDualFormNativeECCauchyBivectorIncrement source current 0 = 0 := by
    funext formDirection internalPair
    simp [diracDualFormNativeECCauchyBivectorIncrement,
      diracDualFormNativeECCauchyConnectionIncrement]
  unfold diracDualFormNativeECCauchyConnection
  rw [incrementZero]
  funext formDirection internalOut internalIn
  simp [diracDualFormNativeECNormalPreparedActual]

theorem diracDualFormNativeECCauchyConnection_loweredCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        (diracDualFormNativeECCauchyConnection source current point)
        formDirection internalPair =
      loweredLorentzConnectionCoefficient
          ((diracDualFormNativeECNormalPreparedActual current
            ).gravityConnection 0)
          formDirection internalPair +
        diracDualFormNativeECCauchyConnectionIncrement source current
          formDirection internalPair point := by
  rw [show
    diracDualFormNativeECCauchyConnection source current point =
      (diracDualFormNativeECNormalPreparedActual current).gravityConnection 0 +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeECCauchyBivectorIncrement source current point) by
    rfl]
  rw [loweredLorentzConnectionCoefficient_add,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  rfl

theorem diracDualFormNativeECCauchyConnection_loweredDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            (diracDualFormNativeECCauchyConnection source current point)
            formDirection internalPair)
        0 derivativeDirection =
      diracDualFormNativeECCauchyConnectionJet source current
        derivativeDirection formDirection internalPair := by
  rw [show
    (fun point =>
      loweredLorentzConnectionCoefficient
        (diracDualFormNativeECCauchyConnection source current point)
        formDirection internalPair) =
      fun point =>
        loweredLorentzConnectionCoefficient
            ((diracDualFormNativeECNormalPreparedActual current
              ).gravityConnection 0)
            formDirection internalPair +
          diracDualFormNativeECCauchyConnectionIncrement source current
            formDirection internalPair point by
    funext point
    exact diracDualFormNativeECCauchyConnection_loweredCoordinate
      source current point formDirection internalPair]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_add]
  rw [(diracDualFormNativeECCauchyConnectionIncrement source current
    formDirection internalPair).hasFDerivAt.fderiv]
  fin_cases derivativeDirection <;>
    simp [diracDualFormNativeECCauchyConnectionIncrement,
      baseCoordinate, coordinateDirection, Fin.sum_univ_four]

theorem diracDualFormNativeECCauchyConnection_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    SmoothLorentzConnectionField
      (diracDualFormNativeECCauchyConnection source current) := by
  intro formDirection internalOut internalIn
  unfold diracDualFormNativeECCauchyConnection
    lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
    diracDualFormNativeECCauchyBivectorIncrement
  apply contDiff_const.add
  apply contDiff_const.mul
  apply ContDiff.sum
  intro internalPair _
  exact
    (diracDualFormNativeECCauchyConnectionIncrement source current
      formDirection internalPair).contDiff.mul contDiff_const

theorem diracDualFormNativeECCauchyConnection_lorentzSkew
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (originSkew : LorentzSkew (current.gravityConnection 0))
    (point : BasePoint) :
    LorentzSkew (diracDualFormNativeECCauchyConnection source current point) := by
  have incrementSkew :=
    lorentzSkewConnectionOfBivectorOneForm_lorentzSkew
      (diracDualFormNativeECCauchyBivectorIncrement source current point)
  intro formDirection
  have originAt := originSkew formDirection
  have incrementAt := incrementSkew formDirection
  rw [show spinConnectionMatrix
        (diracDualFormNativeECCauchyConnection source current point)
          formDirection =
      spinConnectionMatrix (current.gravityConnection 0) formDirection +
        spinConnectionMatrix
          (lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeECCauchyBivectorIncrement source current point))
          formDirection by
    ext internalOut internalIn
    rfl]
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  calc
    (Matrix.transpose (spinConnectionMatrix (current.gravityConnection 0)
            formDirection) * minkowskiInternalMetric +
        Matrix.transpose
            (spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm
                (diracDualFormNativeECCauchyBivectorIncrement
                  source current point)) formDirection) *
          minkowskiInternalMetric) +
      (minkowskiInternalMetric *
          spinConnectionMatrix (current.gravityConnection 0) formDirection +
        minkowskiInternalMetric *
          spinConnectionMatrix
            (lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeECCauchyBivectorIncrement
                source current point)) formDirection) =
        (Matrix.transpose (spinConnectionMatrix (current.gravityConnection 0)
              formDirection) * minkowskiInternalMetric +
          minkowskiInternalMetric *
            spinConnectionMatrix (current.gravityConnection 0)
              formDirection) +
        (Matrix.transpose
              (spinConnectionMatrix
                (lorentzSkewConnectionOfBivectorOneForm
                  (diracDualFormNativeECCauchyBivectorIncrement
                    source current point)) formDirection) *
            minkowskiInternalMetric +
          minkowskiInternalMetric *
            spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm
                (diracDualFormNativeECCauchyBivectorIncrement
                  source current point)) formDirection) := by
      abel
    _ = 0 := by rw [originAt, incrementAt, add_zero]

theorem diracDualFormNativeECCurrentLoweredConnectionJet_curvature
    (current : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) :
    diracDualFormNativeECCurrentLoweredConnectionJet current
          (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair -
        diracDualFormNativeECCurrentLoweredConnectionJet current
          (pairSecond spacetimePair) (pairFirst spacetimePair) internalPair +
        originLorentzBracketCurvature
          ((diracDualFormNativeECNormalPreparedActual current
            ).gravityConnection 0)
          internalPair spacetimePair =
      diracDualFormNativeECCauchyCurrentCurvature current internalPair
        spacetimePair := by
  unfold diracDualFormNativeECCurrentLoweredConnectionJet
    diracDualFormNativeECCauchyCurrentCurvature
    originLorentzBracketCurvature holonomicGravityCurvature
  dsimp only
  ring

theorem diracDualFormNativeECCauchyConnectionJet_antisymmetrized
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) :
    diracDualFormNativeECCauchyConnectionJet source current
          (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair -
        diracDualFormNativeECCauchyConnectionJet source current
          (pairSecond spacetimePair) (pairFirst spacetimePair) internalPair =
      diracDualFormNativeECCurrentLoweredConnectionJet current
          (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair -
        diracDualFormNativeECCurrentLoweredConnectionJet current
          (pairSecond spacetimePair) (pairFirst spacetimePair) internalPair +
        identityECTemporalCurvatureOfCoordinates
          (diracDualFormNativeECTemporalCurvatureIncrement source current)
          internalPair spacetimePair := by
  fin_cases spacetimePair <;>
    simp [diracDualFormNativeECCauchyConnectionJet,
      identityECTemporalCurvatureOfCoordinates, pairFirst, pairSecond] <;>
    ring

theorem diracDualFormNativeECCauchyConnection_realizes_target
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        { diracDualFormNativeECNormalPreparedActual current with
          gravityConnection :=
            diracDualFormNativeECCauchyConnection source current }
        0 =
      diracDualFormNativeECCauchyCurvatureTarget source current := by
  let actual : StageNineHolonomicConfiguration :=
    { diracDualFormNativeECNormalPreparedActual current with
      gravityConnection :=
        diracDualFormNativeECCauchyConnection source current }
  have connectionSmooth :=
    diracDualFormNativeECCauchyConnection_smooth source current
  funext internalPair spacetimePair
  have connectionOrigin :
      actual.gravityConnection 0 = current.gravityConnection 0 :=
    diracDualFormNativeECCauchyConnection_origin source current
  have firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          actual.gravityConnection candidate (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair))
        0 :=
    (connectionSmooth (pairSecond spacetimePair)
      (pairFirst internalPair) (pairSecond internalPair)
      |>.differentiable (by simp)).differentiableAt
  have secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          actual.gravityConnection candidate (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair))
        0 :=
    (connectionSmooth (pairFirst spacetimePair)
      (pairFirst internalPair) (pairSecond internalPair)
      |>.differentiable (by simp)).differentiableAt
  have firstDerivative :
      minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative actual 0
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) =
        diracDualFormNativeECCauchyConnectionJet source current
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          internalPair := by
    calc
      _ = fieldDirectionalDerivative
            (fun candidate =>
              loweredLorentzConnectionCoefficient
                (actual.gravityConnection candidate)
                (pairSecond spacetimePair) internalPair)
            0 (pairFirst spacetimePair) := by
          symm
          exact loweredLorentzConnectionCoefficient_directionalDerivative
            actual 0 (pairFirst spacetimePair) (pairSecond spacetimePair)
              internalPair firstDifferentiable
      _ = _ := diracDualFormNativeECCauchyConnection_loweredDerivative
        source current (pairFirst spacetimePair) (pairSecond spacetimePair)
          internalPair
  have secondDerivative :
      minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative actual 0
            (pairSecond spacetimePair) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) =
        diracDualFormNativeECCauchyConnectionJet source current
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          internalPair := by
    calc
      _ = fieldDirectionalDerivative
            (fun candidate =>
              loweredLorentzConnectionCoefficient
                (actual.gravityConnection candidate)
                (pairFirst spacetimePair) internalPair)
            0 (pairSecond spacetimePair) := by
          symm
          exact loweredLorentzConnectionCoefficient_directionalDerivative
            actual 0 (pairSecond spacetimePair) (pairFirst spacetimePair)
              internalPair secondDifferentiable
      _ = _ := diracDualFormNativeECCauchyConnection_loweredDerivative
        source current (pairSecond spacetimePair) (pairFirst spacetimePair)
          internalPair
  have currentCurvature :=
    diracDualFormNativeECCurrentLoweredConnectionJet_curvature current
      internalPair spacetimePair
  have antisymmetrized :=
    diracDualFormNativeECCauchyConnectionJet_antisymmetrized source current
      internalPair spacetimePair
  have targetEquality := congrFun (congrFun
    (diracDualFormNativeECCauchyCurvatureTarget_eq_current_add_increment
      source current) internalPair) spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign (pairFirst internalPair) *
        (gravityConnectionDerivative actual 0
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) -
          gravityConnectionDerivative actual 0
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) +
          ∑ middle : LorentzianIndex,
            (actual.gravityConnection 0 (pairFirst spacetimePair)
                  (pairFirst internalPair) middle *
                actual.gravityConnection 0 (pairSecond spacetimePair)
                  middle (pairSecond internalPair) -
              actual.gravityConnection 0 (pairSecond spacetimePair)
                  (pairFirst internalPair) middle *
                actual.gravityConnection 0 (pairFirst spacetimePair)
                  middle (pairSecond internalPair))) =
      diracDualFormNativeECCauchyCurvatureTarget source current internalPair
        spacetimePair
  rw [connectionOrigin]
  have bracketCoordinate :
      minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (current.gravityConnection 0 (pairFirst spacetimePair)
                  (pairFirst internalPair) middle *
                current.gravityConnection 0 (pairSecond spacetimePair)
                  middle (pairSecond internalPair) -
              current.gravityConnection 0 (pairSecond spacetimePair)
                  (pairFirst internalPair) middle *
                current.gravityConnection 0 (pairFirst spacetimePair)
                  middle (pairSecond internalPair)) =
        originLorentzBracketCurvature
          ((diracDualFormNativeECNormalPreparedActual current
            ).gravityConnection 0)
          internalPair spacetimePair := by
    rfl
  calc
    _ =
        (minkowskiInternalSign (pairFirst internalPair) *
            gravityConnectionDerivative actual 0
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair)) -
          (minkowskiInternalSign (pairFirst internalPair) *
            gravityConnectionDerivative actual 0
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair)) +
          originLorentzBracketCurvature
            ((diracDualFormNativeECNormalPreparedActual current
              ).gravityConnection 0)
            internalPair spacetimePair := by
      rw [← bracketCoordinate]
      ring
    _ =
        diracDualFormNativeECCauchyConnectionJet source current
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              internalPair -
            diracDualFormNativeECCauchyConnectionJet source current
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              internalPair +
          originLorentzBracketCurvature
            ((diracDualFormNativeECNormalPreparedActual current
              ).gravityConnection 0)
            internalPair spacetimePair := by
      rw [firstDerivative, secondDerivative]
    _ =
        diracDualFormNativeECCauchyCurrentCurvature current internalPair
            spacetimePair +
          identityECTemporalCurvatureOfCoordinates
            (diracDualFormNativeECTemporalCurvatureIncrement source current)
            internalPair spacetimePair := by
      rw [antisymmetrized]
      linarith
    _ = _ := targetEquality.symm

/-! ## Source/current-only synchronized actual -/

/-- Install the Cauchy-faithful connection germ on the recomputed `II+`
carrier. -/
def diracDualFormNativeECCauchyConnectedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECNormalPreparedActual current with
    gravityConnection := diracDualFormNativeECCauchyConnection source current }

/-- Public write: after the primitive connection update, recompute the live
gravity reaction on that same actual. -/
def sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECCauchyConnectedActual source current with
    gravitySimplicityMultiplier :=
      formNativeGravityReactionField
        (diracDualFormNativeECCauchyConnectedActual source current) }

@[simp] theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).gravityConnection 0 = current.gravityConnection 0 :=
  diracDualFormNativeECCauchyConnection_origin source current

theorem diracDualFormNativeECCauchyConnectedActual_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (diracDualFormNativeECCauchyConnectedActual source current).Smooth := by
  have preparedSmooth :
      (diracDualFormNativeECNormalPreparedActual current).Smooth :=
    restrictHolonomicConfigurationToIIPlus_smooth current smooth
  rcases preparedSmooth with
    ⟨coframeSmooth, _connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      diracDualFormNativeECCauchyConnection_smooth source current,
      auxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).Smooth := by
  let connected := diracDualFormNativeECCauchyConnectedActual source current
  have connectedSmooth : connected.Smooth :=
    diracDualFormNativeECCauchyConnectedActual_smooth source current smooth
  have dualAuxiliarySmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (connected.gravityAuxiliary point) :=
    holonomicGravityInternalDualAuxiliary_contDiff connected connectedSmooth
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature connected point := by
    apply contDiff_pi'
    intro internalPair
    apply contDiff_pi'
    intro spacetimePair
    exact contDiff_const.mul
      (holonomicGravityCurvature_component_contDiff connected connectedSmooth
        internalPair spacetimePair)
  have reactionSmooth : ContDiff ℝ ∞
      (formNativeGravityReactionField connected) :=
    dualAuxiliarySmooth.sub curvatureSmooth
  rcases connectedSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp (contDiff_pi.mp reactionSmooth internalPair)
          spacetimePair,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).Nondegenerate := by
  intro point
  exact nondegenerate point

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible current) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current) := by
  intro point
  exact diracDualFormNativeECCauchyConnection_lorentzSkew source current
    (admissible 0) point

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current) := by
  intro point
  rfl

/-- The Cauchy write preserves the Cartan-generated connection value at the
shared contact. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connectionSelfGenerated_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) 0 := by
  let final :=
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current
  calc
    final.gravityConnection 0 = current.gravityConnection 0 :=
      sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero
        source current
    _ = diracDualFormNativeActionCartanConnectionAt source current 0 :=
      selfGenerated
    _ = diracDualFormNativeActionCartanConnectionAt source final 0 := by
      unfold diracDualFormNativeActionCartanConnectionAt
        diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
        source current final 0 rfl rfl rfl]
      rfl

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_typedTorsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    cartanTorsionThreeForm
        ((sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current).coframe 0)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current).coframe 0)
          ((sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current).gravityConnection 0)) =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) 0 := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connectionSelfGenerated_zero
      source current selfGenerated]
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    source
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current)
      0 nondegenerate

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_torsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          ((sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current).coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
                source current).coframe 0)
            ((sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current).gravityConnection 0))) =
      formNativePhysicalSpinCurrentThreeForm source 0 0
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current)) 0) := by
  rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_typedTorsionSpin_zero
      source current nondegenerate selfGenerated

/-- The primitive actual realizes the complete kernel-faithful Cauchy target. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) 0 =
      diracDualFormNativeECCauchyCurvatureTarget source current := by
  exact diracDualFormNativeECCauchyConnection_realizes_target source current

/-- Exactly the twelve spatial-column action rows are solved. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_evolutionObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionObservation
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current) 0) =
      diracDualFormNativeECDesiredEvolutionObservation source current := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero]
  exact identityDiracDualECTemporalEvolutionObservation_totalTarget _ _

/-- The four temporal-column constraints are neither manufactured nor
erased by the evolution write. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_constraintObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current) 0) =
      identityDiracDualECConstraintObservation
        (diracDualFormNativeECCauchyCurrentCurvature current) := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero]
  exact identityDiracDualECConstraintObservation_totalTarget _ _

/-- The full six-dimensional electric kernel remains attached to the same
current lineage. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_electricKernel
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current) 0)) =
      identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (diracDualFormNativeECCauchyCurrentCurvature current)) := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero]
  exact identityDiracDualECTemporalEvolutionKernelPart_totalTarget _ _

/-- Every magnetic/spatial curvature coordinate is transported literally. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_spatialCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internalPair : Fin 6)
    (direction : Fin 3) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) 0 internalPair
          (identityECSpatialSpatialPair direction) =
      diracDualFormNativeECCauchyCurrentCurvature current internalPair
        (identityECSpatialSpatialPair direction) := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero]
  exact identityDiracDualECTotalEvolutionCurvatureTarget_spatial _ _ _ _

/-- The generated evolution rows cancel the live repaired-root load.  This
is producer soundness for the twelve evolution equations, not an independent
constraint claim. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_evolutionBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current) 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source current) =
      0 := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_evolutionObservation]
  unfold diracDualFormNativeECDesiredEvolutionObservation
  exact neg_add_cancel _

/-- The unsolved four-row residual is faithfully transported as a typed
constraint responsibility. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_constraintResidual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current) 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source current) =
      identityDiracDualECConstraintObservation
          (diracDualFormNativeECCauchyCurrentCurvature current) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source current) := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_constraintObservation]

/-! ## Same-output load recomputation -/

/-- Forget exactly the gravity slots not read by the gauge or matter coframe
densities.  This is a proof projection, not a quotient producer. -/
private def ecCauchyNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

private theorem diracDualFormNativeCoframeGaugeDensity_ecCauchyProjection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source
        (ecCauchyNonGravityContactProjection field) =
      diracDualFormNativeCoframeGaugeDensity source field := by
  rfl

private theorem diracDualFormNativeCoframeMatterDensity_ecCauchyProjection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point
        (ecCauchyNonGravityContactProjection field) =
      diracDualFormNativeCoframeMatterDensity source point field := by
  rfl

private theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_ecProjection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    ecCauchyNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current)) =
      ecCauchyNonGravityContactProjection
        (diracDualFormNativeECNormalContactField current) := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current) 0 direction =
        holonomicMatterCovariantDerivative
          (diracDualFormNativeECNormalPreparedActual current) 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [
      sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero]
    rfl
  · rfl

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_gaugeEuler_preserved
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current)) =
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField current) := by
  let finalField :=
    diracDualFormNativeECNormalContactField
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      ecCauchyNonGravityContactProjection finalField =
        ecCauchyNonGravityContactProjection currentField :=
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity source finalField =
        diracDualFormNativeCoframeGaugeDensity source currentField := by
    rw [← diracDualFormNativeCoframeGaugeDensity_ecCauchyProjection
        source finalField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_ecCauchyProjection
        source currentField]
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [densityEquality]
  rfl

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_matterEuler_preserved
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
            source current)) =
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField current) := by
  let finalField :=
    diracDualFormNativeECNormalContactField
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      ecCauchyNonGravityContactProjection finalField =
        ecCauchyNonGravityContactProjection currentField :=
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity source 0 finalField =
        diracDualFormNativeCoframeMatterDensity source 0 currentField := by
    rw [← diracDualFormNativeCoframeMatterDensity_ecCauchyProjection
        source 0 finalField,
      projected,
      diracDualFormNativeCoframeMatterDensity_ecCauchyProjection
        source 0 currentField]
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [densityEquality]
  rfl

/-- The live identity-contact load is stable when recomputed on the output.
This upgrades the balance from a frozen-input check to a same-output read. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_loadSelfConsistent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad source
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) =
      diracDualFormNativeIdentityECLoad source current := by
  unfold diracDualFormNativeIdentityECLoad
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_gaugeEuler_preserved,
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_matterEuler_preserved]

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputEvolutionBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current) 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current)) =
      0 := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_loadSelfConsistent]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_evolutionBalance
      source current

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputConstraintResidual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current) 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
              source current)) =
      identityDiracDualECConstraintObservation
          (diracDualFormNativeECCauchyCurrentCurvature current) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source current) := by
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_loadSelfConsistent]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_constraintResidual
      source current

/-- Recomputing the action reaction on the output returns the installed
field. -/
theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
      source current).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
          source current) := by
  rfl

theorem
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
        source current)).2
      (sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_reactionSelfGenerated
        source current)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
