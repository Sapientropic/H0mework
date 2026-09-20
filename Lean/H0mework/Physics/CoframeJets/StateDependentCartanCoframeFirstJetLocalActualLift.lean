import H0mework.Physics.CoframeJets.CartanActionCoframeSecondJetLocalActualLift
import H0mework.Physics.CoframeJets.CoframeFirstJet
import H0mework.Physics.Coframe.CoframeLocalDifferentiability

/-!
# S9-C3h104: state-dependent Cartan coframe first-jet actual lift

The Cauchy state itself supplies the coframe, its genuine spatial Fréchet
jet, and the mixed Lorentz connection.  The zero-spin Cartan formula then
generates the twelve spatial coframe velocities before an actual affine germ
is constructed:

```text
source + Cauchy state
→ actual action-generated joint germ
→ direct mixed Cartan update law
→ complete coframe first jet
→ affine coframe path U
→ B := II⁺(U).
```

Every other action-generated field is retained.  Smoothness, origin
nondegeneracy, simplicity, and mixed Cartan residual zero are read only after
the actual path exists.

This is the zero-spin Cartan sector: it does not claim the generic
Einstein--Cartan matter source law.  The nonzero Dirac spin contribution must
be generated forward from the actual Lorentz action and aligned with
`Dω II⁺(e)` before it can enter this update.  No residual, endpoint, preimage,
right inverse, supplied stationarity certificate, source knob, or branch
receipt enters a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineStateDependentCartanCoframeFirstJetLocalActualLift

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineCanonicalCauchyState
open StageNineCartanActionCoframeSecondJetLocalActualLift
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

abbrev StageNineSpatialCoframeVelocity :=
  StageNineSpatialPoint → Fin 3 → LorentzianIndex → ℝ

/-- Genuine spatial Fréchet derivative of the temporal or spatial coframe
coordinate carried by one Cauchy state. -/
def cauchyCoframeSpatialDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internal coordinate : LorentzianIndex) : ℝ :=
  fderiv ℝ
      (fun candidate => state.coframe candidate internal coordinate)
      space (canonicalSpatialCoordinateDirection direction)

/-- Restriction to a canonical Cauchy slice preserves every component of the
spatial coframe derivative.  This is the coframe analogue of the existing
P286 connection restriction bridge. -/
theorem cauchyCoframeSpatialDerivativeCoordinate_restriction
    (time : ℝ)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (internal coordinate : LorentzianIndex) :
    cauchyCoframeSpatialDerivativeCoordinate
        (canonicalCauchyRestriction time configuration)
        space derivativeDirection internal coordinate =
      fieldDirectionalDerivative
        (fun point => configuration.coframe point internal coordinate)
        (canonicalCauchySlicePoint time space)
        derivativeDirection.succ := by
  have fieldDifferentiable :
      DifferentiableAt ℝ
        (fun point => configuration.coframe point internal coordinate)
        (canonicalCauchySlicePoint time space) :=
    ((smooth.1 internal coordinate).differentiable (by simp)).differentiableAt
  have derivative :=
    fieldDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold cauchyCoframeSpatialDerivativeCoordinate fieldDirectionalDerivative
  change
    fderiv ℝ
        ((fun point => configuration.coframe point internal coordinate) ∘
          canonicalCauchySlicePoint time)
        space (canonicalSpatialCoordinateDirection derivativeDirection) =
      fderiv ℝ
        (fun point => configuration.coframe point internal coordinate)
        (canonicalCauchySlicePoint time space)
        (coordinateDirection derivativeDirection.succ)
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- Mixed Cartan torsion coordinate evaluated from a candidate spatial
coframe velocity. -/
def cauchyTemporalSpatialCartanTorsionCoordinate
    (state : StageNineCauchyState)
    (velocity : StageNineSpatialCoframeVelocity)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internal : LorentzianIndex) : ℝ :=
  velocity space direction internal -
      cauchyCoframeSpatialDerivativeCoordinate state space direction
        internal canonicalLorentzianTimeDirection +
    ∑ middle : LorentzianIndex,
      state.gravityConnection space canonicalLorentzianTimeDirection
          internal middle *
        state.coframe space middle direction.succ -
    ∑ middle : LorentzianIndex,
      state.gravityConnection space direction.succ internal middle *
        state.coframe space middle canonicalLorentzianTimeDirection

def CartanTorsionFreeSpatialCoframeVelocityLaw
    (state : StageNineCauchyState)
    (velocity : StageNineSpatialCoframeVelocity) : Prop :=
  ∀ space direction internal,
    cauchyTemporalSpatialCartanTorsionCoordinate state velocity
      space direction internal = 0

/-- The twelve spatial coframe velocities generated directly by the
zero-spin Cartan time--space equation. -/
def cartanTorsionFreeSpatialCoframeVelocity
    (state : StageNineCauchyState) :
    StageNineSpatialCoframeVelocity :=
  fun space direction internal =>
    cauchyCoframeSpatialDerivativeCoordinate state space direction
        internal canonicalLorentzianTimeDirection -
      ∑ middle : LorentzianIndex,
        state.gravityConnection space canonicalLorentzianTimeDirection
            internal middle *
          state.coframe space middle direction.succ +
      ∑ middle : LorentzianIndex,
        state.gravityConnection space direction.succ internal middle *
          state.coframe space middle canonicalLorentzianTimeDirection

theorem cartanTorsionFreeSpatialCoframeVelocity_satisfies_law
    (state : StageNineCauchyState) :
    CartanTorsionFreeSpatialCoframeVelocityLaw state
      (cartanTorsionFreeSpatialCoframeVelocity state) := by
  intro space direction internal
  unfold cauchyTemporalSpatialCartanTorsionCoordinate
    cartanTorsionFreeSpatialCoframeVelocity
  ring

theorem cartanTorsionFreeSpatialCoframeVelocityLaw_unique
    (state : StageNineCauchyState)
    (first second : StageNineSpatialCoframeVelocity)
    (firstLaw : CartanTorsionFreeSpatialCoframeVelocityLaw state first)
    (secondLaw : CartanTorsionFreeSpatialCoframeVelocityLaw state second) :
    first = second := by
  funext space direction internal
  have firstCoordinate := firstLaw space direction internal
  have secondCoordinate := secondLaw space direction internal
  unfold cauchyTemporalSpatialCartanTorsionCoordinate at firstCoordinate
  unfold cauchyTemporalSpatialCartanTorsionCoordinate at secondCoordinate
  linarith

/-- Complete coframe first jet.  The temporal coframe column uses the existing
zero control; Cartan generates only the twelve spatial-column velocities.
All spatial derivatives are read from the actual Cauchy field. -/
def cartanTorsionFreeCoframeFirstJet
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    PointwiseLorentzianCoframeJet where
  coframe := state.coframe space
  derivative := fun derivativeDirection internal coordinate =>
    ![
      ![
        0,
        cartanTorsionFreeSpatialCoframeVelocity state space 0 internal,
        cartanTorsionFreeSpatialCoframeVelocity state space 1 internal,
        cartanTorsionFreeSpatialCoframeVelocity state space 2 internal
      ] coordinate,
      cauchyCoframeSpatialDerivativeCoordinate state space 0
        internal coordinate,
      cauchyCoframeSpatialDerivativeCoordinate state space 1
        internal coordinate,
      cauchyCoframeSpatialDerivativeCoordinate state space 2
        internal coordinate
    ] derivativeDirection

def sourceActionCartanCoframeLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  let base :=
    sourceActionGeneratedJointLocalActualLift source state space
  let coframe :=
    affineCoframeFieldOfJet
      (cartanTorsionFreeCoframeFirstJet state space)
  { base with
    coframe := coframe
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector (coframe point) }

def SourceActionCartanCoframeRetainedFields
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (actual : StageNineHolonomicConfiguration) : Prop :=
  let base :=
    sourceActionGeneratedJointLocalActualLift source state space
  actual.gravityConnection = base.gravityConnection ∧
    actual.gravitySimplicityMultiplier =
      base.gravitySimplicityMultiplier ∧
    actual.gaugeConnection = base.gaugeConnection ∧
    actual.gaugeAuxiliary = base.gaugeAuxiliary ∧
    actual.scalar = base.scalar ∧
    actual.matter = base.matter ∧
    actual.conjugateMatter = base.conjugateMatter

theorem sourceActionCartanCoframeLocalActualLift_retains_action_fields
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    SourceActionCartanCoframeRetainedFields source state space
      (sourceActionCartanCoframeLocalActualLift source state space) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sourceActionCartanCoframeLocalActualLift_coframe_generated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionCartanCoframeLocalActualLift source state space).coframe =
      affineCoframeFieldOfJet
        (cartanTorsionFreeCoframeFirstJet state space) := by
  rfl

theorem sourceActionCartanCoframeLocalActualLift_gravityAuxiliary_generated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionCartanCoframeLocalActualLift source state
        space).gravityAuxiliary =
      fun point =>
        physicalIIPlusBivector
          ((sourceActionCartanCoframeLocalActualLift source state
            space).coframe point) := by
  rfl

theorem sourceActionCartanCoframeLocalActualLift_initialCoframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionCartanCoframeLocalActualLift source state space).coframe 0 =
      state.coframe space := by
  exact affineCoframeFieldOfJet_origin _

theorem sourceActionCartanCoframeLocalActualLift_coframeFirstJet
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (sourceActionCartanCoframeLocalActualLift source state space).coframe
        0 =
      cartanTorsionFreeCoframeFirstJet state space := by
  exact holonomicCoframeFirstJetAt_affine_origin _

theorem sourceActionCartanCoframeLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionCartanCoframeLocalActualLift source state space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedJointLocalActualLift_smooth source state space
  rcases baseSmooth with
    ⟨_baseCoframeSmooth, gravityConnectionSmooth,
      _baseGravityAuxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩
  let jet := cartanTorsionFreeCoframeFirstJet state space
  have coframeSmooth :
      ContDiff ℝ ∞ (affineCoframeFieldOfJet jet) := by
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro coordinate
    exact affineCoframeFieldOfJet_componentwiseSmooth
      jet internal coordinate
  have gravityAuxiliarySmooth :
      ContDiff ℝ ∞ fun point =>
        physicalIIPlusBivector
          (affineCoframeFieldOfJet jet point) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  exact
    ⟨fun internal coordinate =>
        contDiff_pi.mp (contDiff_pi.mp coframeSmooth internal) coordinate,
      gravityConnectionSmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp
          (contDiff_pi.mp gravityAuxiliarySmooth internalPair)
          spacetimePair,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

theorem sourceActionCartanCoframeLocalActualLift_originNondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (stateNondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    Matrix.det
        ((sourceActionCartanCoframeLocalActualLift source state
          space).coframe 0) ≠ 0 := by
  rw [sourceActionCartanCoframeLocalActualLift_initialCoframe]
  exact stateNondegenerate

theorem sourceActionCartanCoframeLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNinePlebanskiMultiplierVariation.GravitySimplicityEquation
      (sourceActionCartanCoframeLocalActualLift source state space) := by
  intro point
  rfl

theorem sourceActionCartanCoframeLocalActualLift_mixedCartan_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internal : LorentzianIndex) :
    cartanTorsionCoordinate
        (sourceActionCartanCoframeLocalActualLift source state space)
        0 canonicalLorentzianTimeDirection direction.succ internal = 0 := by
  have jetReadback :=
    sourceActionCartanCoframeLocalActualLift_coframeFirstJet
      source state space
  have temporalDerivative :
      fieldDirectionalDerivative
          (fun point =>
            (sourceActionCartanCoframeLocalActualLift source state space).coframe
              point internal direction.succ)
          0 canonicalLorentzianTimeDirection =
        cartanTorsionFreeSpatialCoframeVelocity state space direction
          internal := by
    change
      (holonomicCoframeFirstJetAt
          (sourceActionCartanCoframeLocalActualLift source state space).coframe
          0).derivative canonicalLorentzianTimeDirection internal
            direction.succ =
        _
    rw [jetReadback]
    fin_cases direction <;>
      simp [cartanTorsionFreeCoframeFirstJet,
        canonicalLorentzianTimeDirection]
  have spatialTemporalDerivative :
      fieldDirectionalDerivative
          (fun point =>
            (sourceActionCartanCoframeLocalActualLift source state space).coframe
              point internal canonicalLorentzianTimeDirection)
          0 direction.succ =
        cauchyCoframeSpatialDerivativeCoordinate state space direction
          internal canonicalLorentzianTimeDirection := by
    change
      (holonomicCoframeFirstJetAt
          (sourceActionCartanCoframeLocalActualLift source state space).coframe
          0).derivative direction.succ internal
            canonicalLorentzianTimeDirection =
        _
    rw [jetReadback]
    fin_cases direction <;>
      simp [cartanTorsionFreeCoframeFirstJet,
        canonicalLorentzianTimeDirection]
  have connectionOrigin :
      (sourceActionCartanCoframeLocalActualLift source state space).gravityConnection
          0 =
        state.gravityConnection space := by
    exact
      sourceActionGeneratedJointLocalActualLift_initialGravityConnection
        source state space
  have coframeOrigin :
      (sourceActionCartanCoframeLocalActualLift source state space).coframe 0 =
        state.coframe space := by
    exact affineCoframeFieldOfJet_origin _
  unfold cartanTorsionCoordinate
  rw [temporalDerivative, spatialTemporalDerivative, connectionOrigin,
    coframeOrigin]
  exact
    cartanTorsionFreeSpatialCoframeVelocity_satisfies_law state
      space direction internal

/-- Complete source/action-first local response.  The constructor and the
actual field path are recorded before the final Cartan acceptance law. -/
structure SourceActionCartanCoframeFirstJetLocalActualLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (actual : StageNineHolonomicConfiguration) : Prop where
  retainsActionFields :
    SourceActionCartanCoframeRetainedFields source state space actual
  coframeGenerated :
    actual.coframe =
      affineCoframeFieldOfJet
        (cartanTorsionFreeCoframeFirstJet state space)
  gravityAuxiliaryGenerated :
    actual.gravityAuxiliary =
      fun point => physicalIIPlusBivector (actual.coframe point)
  spatialVelocityGenerated :
    CartanTorsionFreeSpatialCoframeVelocityLaw state
      (cartanTorsionFreeSpatialCoframeVelocity state)
  coframeFirstJet :
    holonomicCoframeFirstJetAt actual.coframe 0 =
      cartanTorsionFreeCoframeFirstJet state space
  coframeInitial :
    actual.coframe 0 = state.coframe space
  smooth :
    actual.Smooth
  originNondegenerate :
    Matrix.det (state.coframe space) ≠ 0 →
      Matrix.det (actual.coframe 0) ≠ 0
  gravitySimplicity :
    StageNinePlebanskiMultiplierVariation.GravitySimplicityEquation actual
  mixedCartanAcceptance :
    ∀ (direction : Fin 3) (internal : LorentzianIndex),
      cartanTorsionCoordinate actual 0 canonicalLorentzianTimeDirection
          direction.succ internal = 0

theorem sourceActionCartanCoframeLocalActualLift_realizes_update_law
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    SourceActionCartanCoframeFirstJetLocalActualLaw source state space
      (sourceActionCartanCoframeLocalActualLift source state space) := by
  exact
    { retainsActionFields :=
        sourceActionCartanCoframeLocalActualLift_retains_action_fields
          source state space
      coframeGenerated :=
        sourceActionCartanCoframeLocalActualLift_coframe_generated
          source state space
      gravityAuxiliaryGenerated :=
        sourceActionCartanCoframeLocalActualLift_gravityAuxiliary_generated
          source state space
      spatialVelocityGenerated :=
        cartanTorsionFreeSpatialCoframeVelocity_satisfies_law state
      coframeFirstJet :=
        sourceActionCartanCoframeLocalActualLift_coframeFirstJet
          source state space
      coframeInitial :=
        sourceActionCartanCoframeLocalActualLift_initialCoframe
          source state space
      smooth :=
        sourceActionCartanCoframeLocalActualLift_smooth source state space
      originNondegenerate :=
        sourceActionCartanCoframeLocalActualLift_originNondegenerate
          source state space
      gravitySimplicity :=
        sourceActionCartanCoframeLocalActualLift_simplicity
          source state space
      mixedCartanAcceptance :=
        sourceActionCartanCoframeLocalActualLift_mixedCartan_origin
          source state space }

def positiveSourceActionCartanCoframeLocalActualLift :
    StageNineHolonomicConfiguration :=
  sourceActionCartanCoframeLocalActualLift
    positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

theorem
    positiveSourceActionCartanCoframeLocalActualLift_realizes_C3h104 :
    SourceActionCartanCoframeFirstJetLocalActualLaw
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
      positiveSourceActionCartanCoframeLocalActualLift := by
  exact sourceActionCartanCoframeLocalActualLift_realizes_update_law
    positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

theorem positiveCartanSpatialCoframeVelocity_zero :
    cartanTorsionFreeSpatialCoframeVelocity
        positivePhaseProbeCauchyState = 0 := by
  funext space direction internal
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  simp [cartanTorsionFreeSpatialCoframeVelocity,
    cauchyCoframeSpatialDerivativeCoordinate,
    positiveProbeCauchyStateNormalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineStateDependentCartanCoframeFirstJetLocalActualLift
