import H0mework.Physics.CartanGeneration.PrimitiveCauchyDevelopment

/-!
# S9-C3h129: synchronized action response of the generated current Cartan path

C3h128 already lets the source and actual dynamics generate the whole-slice
primitive path `U`.  This module differentiates that same path at every
relative time:

```text
source + initial primitive state
→ generated current primitive U(anchor)
→ matching torsion-free Cartan actual germs
→ whole-slice path U_Cartan(relativeTime)
→ complete time-indexed primitive response dU_Cartan / d relativeTime
→ later equation/residual acceptance.
```

The Cartan action owns the coframe response.  Since
`B(relativeTime) = II⁺(e(relativeTime))`, the gravity-auxiliary response is
the tangent of that same derived field and is generally time-dependent.
Every other primitive response is retained from the matching base action
actual.  Nothing is reconstructed from a residual or endpoint.

This is a current-state affine actual development.  It is not yet an
autonomous law `dU/dt = V(source, U(t))`, an exact flow, a global gluing
theorem, an on-shell statement, or a nonzero-spin Einstein--Cartan producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanLocalActualLift
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedJointPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## The generated time-indexed response -/

/-- Complete Cartan coframe response read from the first jet generated at
the current primitive state.  The temporal column keeps its declared zero
control; the spatial columns are the twelve Cartan velocities. -/
def sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    LorentzianCoframe :=
  fun internal coordinate =>
    (cartanTorsionFreeCoframeFirstJet
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      space).derivative canonicalLorentzianTimeDirection
        internal coordinate

/-- The complete primitive response of the already generated Cartan path.
The non-Cartan coordinates are inherited from the matching base action
actual.  The two replaced coordinates are generated forward: the coframe
from the Cartan jet and `Ḃ` from differentiating `II⁺(e)`. -/
def sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  { sourceActionGeneratedJointPrimitiveCauchyVelocity source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      space with
    coframe :=
      sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
        source anchor state space
    gravityAuxiliary :=
      physicalIIPlusCoframeTangent
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state).coframe space)
        (sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
          source anchor state space) }

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- Chain rule for an arbitrary point of the canonical local time line. -/
private theorem hasDerivAt_along_canonicalCauchyTimeLine
    (field : BasePoint → ℝ)
    (time : ℝ)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time 0)) :
    HasDerivAt
      (fun candidate : ℝ =>
        field (canonicalCauchySlicePoint candidate 0))
      (fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time 0)
        canonicalLorentzianTimeDirection)
      time := by
  let line := fun candidate : ℝ =>
    candidate • coordinateDirection canonicalLorentzianTimeDirection
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) time := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) time).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)
  have lineAt :
      line time = canonicalCauchySlicePoint time 0 := by
    exact (canonicalCauchySlicePoint_zeroSpace_eq_timeLine time).symm
  have outerDerivative :
      HasFDerivAt field
        (fderiv ℝ field (canonicalCauchySlicePoint time 0))
        (line time) := by
    rw [lineAt]
    exact differentiable.hasFDerivAt
  have composed :=
    outerDerivative.comp_hasDerivAt time lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun candidate : ℝ =>
      field (canonicalCauchySlicePoint candidate 0)) =
        field ∘ line by
    funext candidate
    simp only [Function.comp_apply, line,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]]
  exact composed

/-! ## The two Cartan-generated derivative sectors -/

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_coframeHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).coframe
            space internal coordinate)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).coframe internal coordinate)
      time := by
  let actual :=
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space
  let field : BasePoint → ℝ := fun point =>
    actual.coframe point internal coordinate
  have fieldDifferentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time 0) := by
    exact
      (((sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
        source anchor state space).smooth.1 internal coordinate).differentiable
          (by simp)).differentiableAt
  change HasDerivAt
    (fun candidate : ℝ =>
      field (canonicalCauchySlicePoint candidate 0)) _ time
  convert hasDerivAt_along_canonicalCauchyTimeLine
    field time fieldDifferentiable using 1
  unfold fieldDirectionalDerivative field actual
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
  exact
    (affineCoframeFieldOfJet_directionalDerivative
      (cartanTorsionFreeCoframeFirstJet
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state)
        space)
      (canonicalCauchySlicePoint time 0)
      canonicalLorentzianTimeDirection internal coordinate).symm

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityAuxiliaryHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).gravityAuxiliary
            space internalPair spacetimePair)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).gravityAuxiliary
          internalPair spacetimePair)
      time := by
  let actual :=
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space
  let field : BasePoint → ℝ := fun point =>
    actual.gravityAuxiliary point internalPair spacetimePair
  have fieldDifferentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time 0) := by
    exact
      (((sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
        source anchor state space).smooth.2.2.1
          internalPair spacetimePair).differentiable
          (by simp)).differentiableAt
  change HasDerivAt
    (fun candidate : ℝ =>
      field (canonicalCauchySlicePoint candidate 0)) _ time
  have along :=
    hasDerivAt_along_canonicalCauchyTimeLine
      field time fieldDifferentiable
  convert along using 1
  change
    physicalIIPlusCoframeTangent
        (actual.coframe (canonicalCauchySlicePoint time 0))
        (sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
          source anchor state space)
        internalPair spacetimePair =
      fieldDirectionalDerivative
        (fun point =>
          actual.gravityAuxiliary point internalPair spacetimePair)
        (canonicalCauchySlicePoint time 0)
        canonicalLorentzianTimeDirection
  symm
  rw [show
    (fun point =>
      actual.gravityAuxiliary point internalPair spacetimePair) =
        fun point =>
          physicalIIPlusBivector (actual.coframe point)
            internalPair spacetimePair by
    funext point
    rw [
      sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_gravityAuxiliary_generated]]
  rw [physicalIIPlusBivector_fieldDirectionalDerivative
    actual.coframe
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
      source anchor state space).smooth.1]
  congr 2
  funext internal coordinate
  unfold coframeFieldDirectionalTangent fieldDirectionalDerivative
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse actual
  exact
    affineCoframeFieldOfJet_directionalDerivative
      (cartanTorsionFreeCoframeFirstJet
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state)
        space)
      (canonicalCauchySlicePoint time 0)
      canonicalLorentzianTimeDirection internal coordinate

/-! ## Retained base-action derivative sectors -/

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityConnectionHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    HasDerivAt
      (fun candidate : ℝ =>
        loweredLorentzConnectionCoefficient
          ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor candidate state).gravityConnection space)
          formDirection internalPair)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).gravityConnection
          formDirection internalPair)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityConnectionHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space formDirection internalPair

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_multiplierHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).gravitySimplicityMultiplier
            space internalPair spacetimePair)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).gravitySimplicityMultiplier
          internalPair spacetimePair)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_multiplierHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space internalPair spacetimePair

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_p286ConnectionHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor candidate state).gaugeConnection
              space formDirection))
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).p286Connection formDirection)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286ConnectionHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space formDirection

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_p286AuxiliaryHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor candidate state).gaugeAuxiliary space pair))
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).p286Auxiliary pair)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286AuxiliaryHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space pair

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_scalarHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).scalar space)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).scalar)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_scalarVelocityHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).scalarVelocity space)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).scalarVelocity)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarVelocityHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_matterHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    HasDerivAt
      (fun candidate : ℝ =>
        matterCoordinateEquiv
          ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor candidate state).matter space))
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).matter)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_matterHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_conjugateMatterHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    HasDerivAt
      (fun candidate : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor candidate state).conjugateMatter space matter)
      ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor time state space).conjugateMatter matter)
      time := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_conjugateMatterHasDerivAt
      source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      time space matter

/-! ## Complete synchronized response law -/

/-- The generated C3h128 path carries one complete, time-indexed primitive
response at every relative time.  This law consumes the already generated
path; no response coordinate is accepted from the caller. -/
structure
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (development : ℝ → StageNineCauchyState) : Prop where
  producer :
    StageNineCurrentTorsionFreeCartanPrimitiveCauchyDevelopmentLaw
      source anchor state development
  coframeDerivative :
    ∀ time space internal coordinate,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).coframe space internal coordinate)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).coframe internal coordinate)
        time
  gravityConnectionDerivative :
    ∀ time space formDirection internalPair,
      HasDerivAt
        (fun candidate : ℝ =>
          loweredLorentzConnectionCoefficient
            ((development candidate).gravityConnection space)
            formDirection internalPair)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).gravityConnection
            formDirection internalPair)
        time
  gravityAuxiliaryDerivative :
    ∀ time space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).gravityAuxiliary
            space internalPair spacetimePair)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).gravityAuxiliary
            internalPair spacetimePair)
        time
  multiplierDerivative :
    ∀ time space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).gravitySimplicityMultiplier
            space internalPair spacetimePair)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).gravitySimplicityMultiplier
            internalPair spacetimePair)
        time
  p286ConnectionDerivative :
    ∀ time space formDirection,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((development candidate).gaugeConnection space formDirection))
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).p286Connection formDirection)
        time
  p286AuxiliaryDerivative :
    ∀ time space pair,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((development candidate).gaugeAuxiliary space pair))
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).p286Auxiliary pair)
        time
  scalarDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).scalar space)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).scalar)
        time
  scalarVelocityDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).scalarVelocity space)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).scalarVelocity)
        time
  matterDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ =>
          matterCoordinateEquiv ((development candidate).matter space))
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).matter)
        time
  conjugateMatterDerivative :
    ∀ time space matter,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).conjugateMatter space matter)
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor time state space).conjugateMatter matter)
        time

/-- Frontier theorem: source and actual dynamics generate `U` first, and
that same `U` realizes the complete synchronized primitive response at every
relative time. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
      source anchor state
      (fun relativeTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state) := by
  exact
    { producer :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_realizes
          source anchor state
      coframeDerivative :=
        fun time space internal coordinate =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_coframeHasDerivAt
            source anchor time state space internal coordinate
      gravityConnectionDerivative :=
        fun time space formDirection internalPair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityConnectionHasDerivAt
            source anchor time state space formDirection internalPair
      gravityAuxiliaryDerivative :=
        fun time space internalPair spacetimePair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityAuxiliaryHasDerivAt
            source anchor time state space internalPair spacetimePair
      multiplierDerivative :=
        fun time space internalPair spacetimePair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_multiplierHasDerivAt
            source anchor time state space internalPair spacetimePair
      p286ConnectionDerivative :=
        fun time space formDirection =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_p286ConnectionHasDerivAt
            source anchor time state space formDirection
      p286AuxiliaryDerivative :=
        fun time space pair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_p286AuxiliaryHasDerivAt
            source anchor time state space pair
      scalarDerivative :=
        fun time space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_scalarHasDerivAt
            source anchor time state space
      scalarVelocityDerivative :=
        fun time space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_scalarVelocityHasDerivAt
            source anchor time state space
      matterDerivative :=
        fun time space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_matterHasDerivAt
            source anchor time state space
      conjugateMatterDerivative :=
        fun time space matter =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_conjugateMatterHasDerivAt
            source anchor time state space matter }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
