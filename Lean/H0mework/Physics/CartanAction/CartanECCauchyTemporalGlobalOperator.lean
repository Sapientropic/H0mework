import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.JointVariation.FullOccurrenceContactOperator
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLift
import H0mework.Physics.Exterior.GravityReactionInstallation
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Source-native Cartan--EC Cauchy temporal gravity write

The occurrence-local EC action generates temporal curvature increments, not a
closed four-dimensional connection one-form.  This module therefore compiles
that action data in its native Cauchy jurisdiction:

```text
(source, current)
  -> pointwise Cartan/reaction restart
  -> EC temporal-curvature increment at every occurrence
  -> canonical time primitive of that increment
  -> one global Lorentz connection
  -> live gravity reaction.
```

The public operator accepts only `(source,current)`.  No residual, support,
target field, branch, endpoint, or zero-fiber receipt enters the write.  The
zero time slice is retained exactly; its temporal connection jet is the
action-generated EC Cauchy jet.  All-spacetime stationarity remains a
downstream readback of the emitted actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Source/current-only action profiles -/

/-- The exact pointwise Cartan current on which the EC Cauchy action is read. -/
def cartanECCauchyTemporalBase
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current

/-- Canonical recentering of the same Cartan current at one occurrence. -/
def cartanECCauchyTemporalProfileInput
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration
    (cartanECCauchyTemporalBase source current) contact

/-- The three action-generated temporal curvature increments at one
occurrence, embedded as a lowered Lorentz one-form velocity. -/
def cartanECCauchyTemporalConnectionCorrectionProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    ![
      0,
      diracDualFormNativeECTemporalCurvatureIncrement source
        (cartanECCauchyTemporalProfileInput source current contact)
        internalPair 0,
      diracDualFormNativeECTemporalCurvatureIncrement source
        (cartanECCauchyTemporalProfileInput source current contact)
        internalPair 1,
      diracDualFormNativeECTemporalCurvatureIncrement source
        (cartanECCauchyTemporalProfileInput source current contact)
        internalPair 2
    ] formDirection

/-- Canonical time primitive of every faithful lowered connection
coordinate. -/
def cartanECCauchyTemporalConnectionCorrectionPrimitive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    canonicalTimePrimitive
      (fun candidate =>
        cartanECCauchyTemporalConnectionCorrectionProfile source current
          candidate formDirection internalPair)
      point

/-! ## One common global actual -/

/-- Install the Cauchy-temporal connection correction on the exact Cartan
base.  The correction vanishes on the complete zero-time slice. -/
def cartanECCauchyTemporalConnectedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { cartanECCauchyTemporalBase source current with
    gravityConnection := fun point =>
      (cartanECCauchyTemporalBase source current).gravityConnection point +
        lorentzSkewConnectionOfBivectorOneForm
          (cartanECCauchyTemporalConnectionCorrectionPrimitive
            source current point) }

/-- Recompute the live reaction only after the global connection exists. -/
def cartanECCauchyTemporalFinalActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installFormNativeGravityReaction
    (cartanECCauchyTemporalConnectedActual source current)

inductive CartanECCauchyTemporalWriteLeg where
  | cartanRestart
  | temporalConnection
  | liveReaction
  deriving DecidableEq

def cartanECCauchyTemporalActionWrite
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (leg : CartanECCauchyTemporalWriteLeg)
    (before : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .cartanRestart =>
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source before
  | .temporalConnection =>
      { before with
        gravityConnection := fun point =>
          before.gravityConnection point +
            lorentzSkewConnectionOfBivectorOneForm
              (cartanECCauchyTemporalConnectionCorrectionPrimitive
                source current point) }
  | .liveReaction => installFormNativeGravityReaction before

inductive CartanECCauchyTemporalOccurrence
    (_source : SmoothUnifiedSource)
    (_current : StageNineHolonomicConfiguration) where
  | generated

def sourceActionGeneratedCartanECCauchyTemporalOccurrence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    CartanECCauchyTemporalOccurrence source current :=
  .generated

namespace CartanECCauchyTemporalOccurrence

def before
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence : CartanECCauchyTemporalOccurrence source current) :
    CartanECCauchyTemporalWriteLeg -> StageNineHolonomicConfiguration
  | .cartanRestart => current
  | .temporalConnection => cartanECCauchyTemporalBase source current
  | .liveReaction => cartanECCauchyTemporalConnectedActual source current

def after
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence : CartanECCauchyTemporalOccurrence source current) :
    CartanECCauchyTemporalWriteLeg -> StageNineHolonomicConfiguration
  | .cartanRestart => cartanECCauchyTemporalBase source current
  | .temporalConnection => cartanECCauchyTemporalConnectedActual source current
  | .liveReaction => cartanECCauchyTemporalFinalActual source current

theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CartanECCauchyTemporalOccurrence source current)
    (leg : CartanECCauchyTemporalWriteLeg) :
    occurrence.after leg =
      cartanECCauchyTemporalActionWrite source current leg
        (occurrence.before leg) := by
  cases leg <;> rfl

@[simp] theorem cartanRestart_to_temporalConnection_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CartanECCauchyTemporalOccurrence source current) :
    occurrence.after .cartanRestart = occurrence.before .temporalConnection :=
  rfl

@[simp] theorem temporalConnection_to_liveReaction_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CartanECCauchyTemporalOccurrence source current) :
    occurrence.after .temporalConnection = occurrence.before .liveReaction :=
  rfl

abbrev finalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CartanECCauchyTemporalOccurrence source current) :
    StageNineHolonomicConfiguration :=
  occurrence.after .liveReaction

end CartanECCauchyTemporalOccurrence

/-- Public source/current-only global Cauchy gravity emitter. -/
def sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  (sourceActionGeneratedCartanECCauchyTemporalOccurrence source current
    ).finalActual

/-! ## Primitive producer laws -/

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).scalar = current.scalar :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).matter = current.matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        source current).gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      (cartanECCauchyTemporalBase source current).gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  change
    (cartanECCauchyTemporalConnectedActual source current).gravityConnection
        (canonicalCauchySlicePoint 0 space) = _
  funext formDirection internalOut internalIn
  simp [cartanECCauchyTemporalConnectedActual,
    cartanECCauchyTemporalConnectionCorrectionPrimitive,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix]

theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        source current) := by
  intro point
  rfl

theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source current) := by
  exact installFormNativeGravityReaction_reactionSelfGenerated
    (cartanECCauchyTemporalConnectedActual source current)

/-! ## Zero-slice Cauchy realization -/

theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source current).gravityConnection point)
        formDirection internalPair =
      loweredLorentzConnectionCoefficient
          ((cartanECCauchyTemporalBase source current).gravityConnection point)
          formDirection internalPair +
        cartanECCauchyTemporalConnectionCorrectionPrimitive source current point
          formDirection internalPair := by
  change
    loweredLorentzConnectionCoefficient
        ((cartanECCauchyTemporalConnectedActual source current
          ).gravityConnection point) formDirection internalPair = _
  rw [show
    (cartanECCauchyTemporalConnectedActual source current
        ).gravityConnection point =
      (cartanECCauchyTemporalBase source current).gravityConnection point +
        lorentzSkewConnectionOfBivectorOneForm
          (cartanECCauchyTemporalConnectionCorrectionPrimitive
            source current point) by rfl]
  rw [loweredLorentzConnectionCoefficient_add,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]

private theorem fderiv_canonicalCauchySlicePoint_spatial
    (field : BasePoint → ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint 0) space
        (canonicalSpatialCoordinateDirection direction) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  have derivative :=
    differentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- The generated lower connection coordinate has the exact temporal
derivative prescribed by the occurrence-local EC Cauchy action.  The
continuity and differentiability premises validate the emitted field; none
enters its source/current-only constructor. -/
theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredTemporalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6)
    (baseDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (cartanECCauchyTemporalBase source current).gravityConnection point
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current).gravityConnection point formDirection
              (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (profileContinuous :
      ContinuousAt
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        0)
    (profileMeasurable :
      StronglyMeasurableAtFilter
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        (nhds 0) MeasureTheory.volume) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
              source current).gravityConnection point)
            formDirection internalPair)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
          (fun point =>
            loweredLorentzConnectionCoefficient
              ((cartanECCauchyTemporalBase source current
                ).gravityConnection point)
              formDirection internalPair)
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection +
        cartanECCauchyTemporalConnectionCorrectionProfile source current
          (canonicalCauchySlicePoint 0 space) formDirection internalPair := by
  let baseCoordinate : BasePoint → ℝ := fun point =>
    loweredLorentzConnectionCoefficient
      ((cartanECCauchyTemporalBase source current).gravityConnection point)
      formDirection internalPair
  let finalCoordinate : BasePoint → ℝ := fun point =>
    loweredLorentzConnectionCoefficient
      ((sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        source current).gravityConnection point) formDirection internalPair
  have baseCoordinateDifferentiable : DifferentiableAt ℝ baseCoordinate
      (canonicalCauchySlicePoint 0 space) := by
    unfold baseCoordinate loweredLorentzConnectionCoefficient
    fun_prop
  have finalCoordinateDifferentiable : DifferentiableAt ℝ finalCoordinate
      (canonicalCauchySlicePoint 0 space) := by
    unfold finalCoordinate loweredLorentzConnectionCoefficient
    fun_prop
  have baseDerivative :=
    field_timeLine_hasDerivAt baseCoordinate space 0
      baseCoordinateDifferentiable
  have primitiveDerivative :=
    canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
      (fun point =>
        cartanECCauchyTemporalConnectionCorrectionProfile source current point
          formDirection internalPair)
      space 0 (by simp) profileMeasurable profileContinuous
  have generatedDerivative := baseDerivative.add primitiveDerivative
  have finalDerivative :=
    field_timeLine_hasDerivAt finalCoordinate space 0
      finalCoordinateDifferentiable
  apply finalDerivative.unique
  convert generatedDerivative using 1
  funext time
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredConnection
      source current (canonicalCauchySlicePoint time space)
        formDirection internalPair

/-- Spatial first derivatives on the retained zero slice are literal
derivatives of the Cartan base. -/
theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gravityConnectionDerivative_spatial_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex)
    (baseDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (cartanECCauchyTemporalBase source current).gravityConnection point
            formDirection internalOut internalIn)
        (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current).gravityConnection point formDirection
              internalOut internalIn)
        (canonicalCauchySlicePoint 0 space)) :
    gravityConnectionDerivative
        (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source current)
        (canonicalCauchySlicePoint 0 space) direction.succ formDirection
          internalOut internalIn =
      gravityConnectionDerivative (cartanECCauchyTemporalBase source current)
        (canonicalCauchySlicePoint 0 space) direction.succ formDirection
          internalOut internalIn := by
  let finalCoordinate : BasePoint → ℝ := fun point =>
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).gravityConnection point formDirection internalOut
        internalIn
  let baseCoordinate : BasePoint → ℝ := fun point =>
    (cartanECCauchyTemporalBase source current).gravityConnection point
      formDirection internalOut internalIn
  change
    fieldDirectionalDerivative finalCoordinate
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative baseCoordinate
        (canonicalCauchySlicePoint 0 space) direction.succ
  rw [← fderiv_canonicalCauchySlicePoint_spatial finalCoordinate space
      direction finalDifferentiable,
    ← fderiv_canonicalCauchySlicePoint_spatial baseCoordinate space
      direction baseDifferentiable]
  have sliceEquality :
      finalCoordinate ∘ canonicalCauchySlicePoint 0 =
        baseCoordinate ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact congrFun (congrFun (congrFun
      (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
        source current candidateSpace) formDirection) internalOut) internalIn
  rw [sliceEquality]

theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredGravityConnectionDerivative_temporal_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6)
    (baseDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (cartanECCauchyTemporalBase source current).gravityConnection point
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current).gravityConnection point formDirection
              (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (profileContinuous :
      ContinuousAt
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        0)
    (profileMeasurable :
      StronglyMeasurableAtFilter
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        (nhds 0) MeasureTheory.volume) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current)
          (canonicalCauchySlicePoint 0 space) 0 formDirection
            (pairFirst internalPair) (pairSecond internalPair) =
      minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative
            (cartanECCauchyTemporalBase source current)
            (canonicalCauchySlicePoint 0 space) 0 formDirection
              (pairFirst internalPair) (pairSecond internalPair) +
        cartanECCauchyTemporalConnectionCorrectionProfile source current
          (canonicalCauchySlicePoint 0 space) formDirection internalPair := by
  have generated :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredTemporalDerivative_zeroSlice
      source current space formDirection internalPair baseDifferentiable
        finalDifferentiable profileContinuous profileMeasurable
  simp only [canonicalLorentzianTimeDirection] at generated
  rw [loweredLorentzConnectionCoefficient_directionalDerivative
      (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        source current)
      (canonicalCauchySlicePoint 0 space) 0 formDirection internalPair
        finalDifferentiable,
    loweredLorentzConnectionCoefficient_directionalDerivative
      (cartanECCauchyTemporalBase source current)
      (canonicalCauchySlicePoint 0 space) 0 formDirection internalPair
        baseDifferentiable] at generated
  exact generated

theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gravityConnectionDerivative_temporal_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6)
    (baseDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (cartanECCauchyTemporalBase source current).gravityConnection point
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current).gravityConnection point formDirection
              (pairFirst internalPair) (pairSecond internalPair))
        (canonicalCauchySlicePoint 0 space))
    (profileContinuous :
      ContinuousAt
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        0)
    (profileMeasurable :
      StronglyMeasurableAtFilter
        (fun time =>
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint time space)
            formDirection internalPair)
        (nhds 0) MeasureTheory.volume) :
    gravityConnectionDerivative
        (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 0 formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      gravityConnectionDerivative (cartanECCauchyTemporalBase source current)
          (canonicalCauchySlicePoint 0 space) 0 formDirection
            (pairFirst internalPair) (pairSecond internalPair) +
        minkowskiInternalSign (pairFirst internalPair) *
          cartanECCauchyTemporalConnectionCorrectionProfile source current
            (canonicalCauchySlicePoint 0 space) formDirection internalPair := by
  have lowered :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_loweredGravityConnectionDerivative_temporal_zeroSlice
      source current space formDirection internalPair baseDifferentiable
        finalDifferentiable profileContinuous profileMeasurable
  fin_cases internalPair <;>
    simp [pairFirst, minkowskiInternalSign] at lowered ⊢ <;> linarith

/-- On the complete zero-time slice the one global emitted connection has
exactly the occurrence-local EC target curvature at every spatial point. -/
theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_curvature_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (baseDifferentiable :
      ∀ formDirection internalOut internalIn,
        DifferentiableAt ℝ
          (fun point =>
            (cartanECCauchyTemporalBase source current).gravityConnection point
              formDirection internalOut internalIn)
          (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      ∀ formDirection internalOut internalIn,
        DifferentiableAt ℝ
          (fun point =>
            (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
              source current).gravityConnection point formDirection
                internalOut internalIn)
          (canonicalCauchySlicePoint 0 space))
    (profileContinuous :
      ∀ formDirection internalPair,
        ContinuousAt
          (fun time =>
            cartanECCauchyTemporalConnectionCorrectionProfile source current
              (canonicalCauchySlicePoint time space)
              formDirection internalPair)
          0)
    (profileMeasurable :
      ∀ formDirection internalPair,
        StronglyMeasurableAtFilter
          (fun time =>
            cartanECCauchyTemporalConnectionCorrectionProfile source current
              (canonicalCauchySlicePoint time space)
              formDirection internalPair)
          (nhds 0) MeasureTheory.volume) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeECCauchyCurvatureTarget source
        (cartanECCauchyTemporalProfileInput source current
          (canonicalCauchySlicePoint 0 space)) := by
  have temporal (formDirection : LorentzianIndex) (internalPair : Fin 6) :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gravityConnectionDerivative_temporal_zeroSlice
      source current space formDirection internalPair
        (baseDifferentiable formDirection (pairFirst internalPair)
          (pairSecond internalPair))
        (finalDifferentiable formDirection (pairFirst internalPair)
          (pairSecond internalPair))
        (profileContinuous formDirection internalPair)
        (profileMeasurable formDirection internalPair)
  have spatial (direction : Fin 3) (formDirection : LorentzianIndex)
      (internalOut internalIn : LorentzianIndex) :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gravityConnectionDerivative_spatial_zeroSlice
      source current space direction formDirection internalOut internalIn
        (baseDifferentiable formDirection internalOut internalIn)
        (finalDifferentiable formDirection internalOut internalIn)
  have curvatureIncrement :
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
            source current)
          (canonicalCauchySlicePoint 0 space) =
        holonomicGravityCurvature (cartanECCauchyTemporalBase source current)
            (canonicalCauchySlicePoint 0 space) +
          identityECTemporalCurvatureOfCoordinates
            (diracDualFormNativeECTemporalCurvatureIncrement source
              (cartanECCauchyTemporalProfileInput source current
                (canonicalCauchySlicePoint 0 space))) := by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature
    have connectionValue :=
      sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
        source current space
    simp_rw [connectionValue]
    fin_cases spacetimePair
    all_goals
      dsimp only [Pi.add_apply]
      simp [identityECTemporalCurvatureOfCoordinates, pairFirst, pairSecond]
    · have temporalOne := temporal 1 internalPair
      have spatialOne :=
        spatial 0 0 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at temporalOne spatialOne
      rw [temporalOne, spatialOne]
      fin_cases internalPair <;>
        simp [cartanECCauchyTemporalConnectionCorrectionProfile,
          minkowskiInternalSign] <;> ring
    · have temporalTwo := temporal 2 internalPair
      have spatialTwo :=
        spatial 1 0 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at temporalTwo spatialTwo
      rw [temporalTwo, spatialTwo]
      fin_cases internalPair <;>
        simp [cartanECCauchyTemporalConnectionCorrectionProfile,
          minkowskiInternalSign] <;> ring
    · have temporalThree := temporal 3 internalPair
      have spatialThree :=
        spatial 2 0 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at temporalThree spatialThree
      rw [temporalThree, spatialThree]
      fin_cases internalPair <;>
        simp [cartanECCauchyTemporalConnectionCorrectionProfile,
          minkowskiInternalSign] <;> ring
    · have spatialFirst :=
        spatial 1 3 (pairFirst internalPair) (pairSecond internalPair)
      have spatialSecond :=
        spatial 2 2 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at spatialFirst spatialSecond
      rw [spatialFirst, spatialSecond]
      fin_cases internalPair <;>
        simp [minkowskiInternalSign]
    · have spatialFirst :=
        spatial 2 1 (pairFirst internalPair) (pairSecond internalPair)
      have spatialSecond :=
        spatial 0 3 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at spatialFirst spatialSecond
      rw [spatialFirst, spatialSecond]
      fin_cases internalPair <;>
        simp [minkowskiInternalSign]
    · have spatialFirst :=
        spatial 0 2 (pairFirst internalPair) (pairSecond internalPair)
      have spatialSecond :=
        spatial 1 1 (pairFirst internalPair) (pairSecond internalPair)
      simp [pairFirst, pairSecond] at spatialFirst spatialSecond
      rw [spatialFirst, spatialSecond]
      fin_cases internalPair <;>
        simp [minkowskiInternalSign]
  rw [curvatureIncrement]
  rw [diracDualFormNativeECCauchyCurvatureTarget_eq_current_add_increment]
  congr 1
  unfold diracDualFormNativeECCauchyCurrentCurvature
    cartanECCauchyTemporalProfileInput
    diracDualFormNativeECNormalPreparedActual
    restrictHolonomicConfigurationToIIPlus
  change
    holonomicGravityCurvature (cartanECCauchyTemporalBase source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration
          (cartanECCauchyTemporalBase source current)
          (canonicalCauchySlicePoint 0 space)) 0
  exact
    (fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
      (cartanECCauchyTemporalBase source current)
      (canonicalCauchySlicePoint 0 space)).symm

/-- Producer soundness for all twelve EC evolution rows on the emitted
zero slice.  The four Cauchy constraints remain independent downstream
readouts. -/
theorem
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_evolutionBalance_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (baseDifferentiable :
      ∀ formDirection internalOut internalIn,
        DifferentiableAt ℝ
          (fun point =>
            (cartanECCauchyTemporalBase source current).gravityConnection point
              formDirection internalOut internalIn)
          (canonicalCauchySlicePoint 0 space))
    (finalDifferentiable :
      ∀ formDirection internalOut internalIn,
        DifferentiableAt ℝ
          (fun point =>
            (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
              source current).gravityConnection point formDirection
                internalOut internalIn)
          (canonicalCauchySlicePoint 0 space))
    (profileContinuous :
      ∀ formDirection internalPair,
        ContinuousAt
          (fun time =>
            cartanECCauchyTemporalConnectionCorrectionProfile source current
              (canonicalCauchySlicePoint time space)
              formDirection internalPair)
          0)
    (profileMeasurable :
      ∀ formDirection internalPair,
        StronglyMeasurableAtFilter
          (fun time =>
            cartanECCauchyTemporalConnectionCorrectionProfile source current
              (canonicalCauchySlicePoint time space)
              formDirection internalPair)
          (nhds 0) MeasureTheory.volume) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
              source current)
            (canonicalCauchySlicePoint 0 space)) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (cartanECCauchyTemporalProfileInput source current
              (canonicalCauchySlicePoint 0 space))) =
      0 := by
  rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_curvature_zeroSlice
    source current space baseDifferentiable finalDifferentiable
      profileContinuous profileMeasurable]
  have observation :
      identityDiracDualECTemporalEvolutionObservation
          (diracDualFormNativeECCauchyCurvatureTarget source
            (cartanECCauchyTemporalProfileInput source current
              (canonicalCauchySlicePoint 0 space))) =
        diracDualFormNativeECDesiredEvolutionObservation source
          (cartanECCauchyTemporalProfileInput source current
            (canonicalCauchySlicePoint 0 space)) := by
    unfold diracDualFormNativeECCauchyCurvatureTarget
    exact identityDiracDualECTemporalEvolutionObservation_totalTarget _ _
  rw [observation]
  unfold diracDualFormNativeECDesiredEvolutionObservation
  exact neg_add_cancel _

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
