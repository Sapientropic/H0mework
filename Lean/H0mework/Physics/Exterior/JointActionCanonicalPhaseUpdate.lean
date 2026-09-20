import H0mework.Physics.Lorentz.LorentzActionCanonicalPairUpdate
import H0mework.Physics.Exterior.ScalarActionCanonicalMomentumUpdate

/-!
# S9-C3h99: joint action-generated canonical phase update

The preceding producer chain already generates, from one primitive Cauchy
state and one actual action:

* the P286 spatial connection/BF-momentum tangent;
* the Lorentz spatial connection/BF-momentum tangent, including the matter
  spin-current coefficient;
* the scalar coordinate/temporal-momentum tangent;
* the identity-coframe matter and conjugate-matter temporal candidates.

This module gives those outputs one shared-input physical-time package.  It
does not try to decode the Lorentz BF momentum back into a coframe endpoint.
The frozen coframe snapshot, temporal connection controls, and simplicity
multiplier remain explicit in the carrier while the action-generated
canonical pairs evolve.

The construction order is therefore

```text
source + primitive Cauchy state + actual action
→ sector action tangents
→ one reduced joint canonical phase U(time)
→ sector action-law acceptance
→ later simplicity/coframe/residual acceptance.
```

No downstream equation/shell residual, zero fiber, quotient, endpoint,
coframe inverse, range witness, equation receipt, or branch selector is read
by `U`.  This is a reduced shared-input Euler aggregate: the matter/dual
entries are only formal identity-coframe candidates until the
identity-coframe domain is established.  It is not a single joint local
actual field, an integral curve, a primitive nine-field history, or a proof
that the Lorentz momentum update lies in the tangent range of the simplicity
map.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineJointActionCanonicalPhaseUpdate

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionPointwiseEquation
open StageNineMatterActionTimeVelocity
open StageNineMatterPointwiseEquation
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-! ## Reduced shared-input canonical carrier -/

/-- Reduced canonical phase data after the algebraic auxiliary equations have
been used to generate the two BF momenta.

The four fixed fields comprise one frozen unevolved coframe snapshot plus
explicit multiplier/temporal-control data.  In particular, their presence is
not a claim that a coframe velocity has already been generated. -/
@[ext] structure StageNineJointCanonicalPhaseState where
  frozenCoframeSnapshot :
    StageNineSpatialPoint → LorentzianCoframe
  gravitySimplicityMultiplier :
    StageNineSpatialPoint → PhysicalBivector
  temporalGravityConnection :
    StageNineSpatialPoint → Fin 6 → ℝ
  temporalGaugeConnection :
    StageNineSpatialPoint → P286LieBlockData
  gravityGauge :
    StageNineGravityGaugeCanonicalPhaseState
  scalar :
    StageNineScalarCanonicalPhaseState
  matter :
    StageNineSpatialPoint → DiracExteriorMatterCarrier
  conjugateMatter :
    StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier

/-- Constraint/multiplier data and all derived canonical phase coordinates
read from one primitive Cauchy state. -/
def sourceActionGeneratedJointCanonicalPhaseState
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineJointCanonicalPhaseState where
  frozenCoframeSnapshot := state.coframe
  gravitySimplicityMultiplier := state.gravitySimplicityMultiplier
  temporalGravityConnection := fun space internalPair =>
    loweredLorentzConnectionCoefficient
      (state.gravityConnection space)
      canonicalLorentzianTimeDirection internalPair
  temporalGaugeConnection := fun space =>
    state.gaugeConnection space canonicalLorentzianTimeDirection
  gravityGauge :=
    sourceActionGeneratedGravityGaugeCanonicalPhaseState source state
  scalar :=
    sourceActionGeneratedScalarCanonicalPhaseState source state
  matter := state.matter
  conjugateMatter := state.conjugateMatter

/-! ## Matter-sector updates -/

/-- Formal identity-coframe matter-coordinate candidate obtained from the
action-generated raw temporal derivative.  Its actual Dirac interpretation is
only valid on the identity-coframe domain. -/
def actionGeneratedMatterPhaseUpdate
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → DiracExteriorMatterCarrier :=
  fun space =>
    state.matter space +
      time • actionGeneratedMatterRawTimeVelocity state space

/-- Formal identity-coframe dual-coordinate candidate obtained from the
adjoint temporal derivative.  Its actual adjoint interpretation is only valid
on the identity-coframe domain. -/
def actionGeneratedConjugateMatterPhaseUpdate
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier :=
  fun space =>
    state.conjugateMatter space +
      time • actionGeneratedConjugateMatterTimeDerivative state space

@[simp] theorem actionGeneratedMatterPhaseUpdate_zero
    (state : StageNineCauchyState) :
    actionGeneratedMatterPhaseUpdate 0 state = state.matter := by
  funext space
  change
    state.matter space +
        (0 : ℝ) • actionGeneratedMatterRawTimeVelocity state space =
      state.matter space
  module

@[simp] theorem actionGeneratedConjugateMatterPhaseUpdate_zero
    (state : StageNineCauchyState) :
    actionGeneratedConjugateMatterPhaseUpdate 0 state =
      state.conjugateMatter := by
  funext space
  simp [actionGeneratedConjugateMatterPhaseUpdate]

theorem actionGeneratedMatterPhaseUnitIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterPhaseUpdate 1 state space -
      state.matter space =
      actionGeneratedMatterRawTimeVelocity state space := by
  unfold actionGeneratedMatterPhaseUpdate
  module

theorem actionGeneratedConjugateMatterPhaseUnitIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterPhaseUpdate 1 state space -
        state.conjugateMatter space =
      actionGeneratedConjugateMatterTimeDerivative state space := by
  simp [actionGeneratedConjugateMatterPhaseUpdate]

/-! ## One common action-generated update -/

/-- One physical-time argument advances the gravity--gauge and scalar
canonical sectors and packages the identity-coframe matter/dual candidates.
Constraint/multiplier coordinates are carried explicitly and are not
reconstructed from the new momenta.  The `source` indexes the sectors that
actually consume it; the matter/dual candidates are generated from `state`.
-/
def sourceActionGeneratedJointCanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineJointCanonicalPhaseState where
  frozenCoframeSnapshot := state.coframe
  gravitySimplicityMultiplier := state.gravitySimplicityMultiplier
  temporalGravityConnection := fun space internalPair =>
    loweredLorentzConnectionCoefficient
      (state.gravityConnection space)
      canonicalLorentzianTimeDirection internalPair
  temporalGaugeConnection := fun space =>
    state.gaugeConnection space canonicalLorentzianTimeDirection
  gravityGauge :=
    sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate source time state
  scalar :=
    sourceActionGeneratedScalarCanonicalPhaseUpdate source time state
  matter := actionGeneratedMatterPhaseUpdate time state
  conjugateMatter :=
    actionGeneratedConjugateMatterPhaseUpdate time state

@[simp] theorem sourceActionGeneratedJointCanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedJointCanonicalPhaseState source state := by
  apply StageNineJointCanonicalPhaseState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact
      sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate_zero source state
  · exact
      sourceActionGeneratedScalarCanonicalPhaseUpdate_zero source state
  · exact actionGeneratedMatterPhaseUpdate_zero state
  · exact actionGeneratedConjugateMatterPhaseUpdate_zero state

@[simp] theorem sourceActionGeneratedJointCanonicalPhaseUpdate_gravityGauge
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source time
      state).gravityGauge =
        sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate
          source time state :=
  rfl

@[simp] theorem sourceActionGeneratedJointCanonicalPhaseUpdate_scalar
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source time
      state).scalar =
        sourceActionGeneratedScalarCanonicalPhaseUpdate source time state :=
  rfl

@[simp] theorem sourceActionGeneratedJointCanonicalPhaseUpdate_matter
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source time
      state).matter =
        actionGeneratedMatterPhaseUpdate time state :=
  rfl

@[simp] theorem
    sourceActionGeneratedJointCanonicalPhaseUpdate_conjugateMatter
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source time
      state).conjugateMatter =
        actionGeneratedConjugateMatterPhaseUpdate time state :=
  rfl

/-! ## Downstream action-law acceptance -/

/-- The gravity--P286 projection of the joint output satisfies the already
generated spatial connection/BF-momentum action system.  This is stated on
the joint carrier rather than merely citing an independent sector value. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitGravityGauge_satisfies_spatialActionLaws
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (P286ActionGeneratedSpatialVelocityLaw source state
        (sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).gravityGauge.p286.spatialBFMomentumEvaluation
                space direction -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).gravityGauge.p286.spatialBFMomentumEvaluation
                space direction =
          sourceActionGeneratedP286SpatialBFMomentumVelocity
            source state space direction) ∧
      (∀ space,
        holonomicGravityCurvature
            (sourceActionGeneratedGravityGaugeLocalActualLift
              source state space)
            0 =
          actionGeneratedGravityCurvature state space) ∧
      LorentzActionGeneratedSpatialVelocityLaw state
        (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).gravityGauge.lorentz.spatialBFMomentumEvaluation
                space direction -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).gravityGauge.lorentz.spatialBFMomentumEvaluation
                space direction =
          let actual :=
            sourceActionGeneratedGravityGaugeLocalActualLift
              source state space
          let fullDirection :=
            canonicalLorentzSpatialBivectorOneForm direction
          lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
              fullDirection 0 -
            sourceActionGeneratedLorentzSpatialBFMomentumDivergence
              source state space direction := by
  simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
    sourceActionGeneratedJointCanonicalPhaseState] using
    (sourceActionGeneratedGravityGaugeCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws
      source state)

/-- The scalar projection of the same joint output realizes the complete
Cauchy scalar first jet and its coordinate/temporal-momentum action split. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitScalar_satisfies_actionSystem
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (∀ space,
      (sourceActionGeneratedMatterDualScalarLocalActualLift source state
          space).scalar 0 =
        state.scalar space ∧
      ∀ direction : LorentzianIndex,
        fieldDirectionalDerivative
            (sourceActionGeneratedMatterDualScalarLocalActualLift source state
              space).scalar
            0 direction =
          actionGeneratedScalarLocalJetCoordinate state space direction) ∧
      (∀ space,
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).scalar.scalarCoordinate space -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).scalar.scalarCoordinate space =
          state.scalarVelocity space) ∧
      ∀ space direction,
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).scalar.temporalMomentumEvaluation space direction -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).scalar.temporalMomentumEvaluation space direction =
          scalarAlgebraicDirectionalCoefficient source
              (sourceActionGeneratedMatterDualScalarLocalActualLift
                source state space)
              direction 0 -
            sourceActionGeneratedScalarSpatialMomentumDivergence
              source state space direction := by
  simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
    sourceActionGeneratedJointCanonicalPhaseState] using
    (sourceActionGeneratedScalarCanonicalPhaseUnitUpdate_satisfies_actionSystem
      source state)

theorem
    sourceActionGeneratedJointCanonicalPhaseUnitMatterIncrement
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
          state).matter space -
        (sourceActionGeneratedJointCanonicalPhaseState source
          state).matter space =
      actionGeneratedMatterRawTimeVelocity state space := by
  exact actionGeneratedMatterPhaseUnitIncrement state space

theorem
    sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatterIncrement
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
          state).conjugateMatter space -
        (sourceActionGeneratedJointCanonicalPhaseState source
          state).conjugateMatter space =
      actionGeneratedConjugateMatterTimeDerivative state space := by
  exact actionGeneratedConjugateMatterPhaseUnitIncrement state space

/-- The matter increment of the reduced joint package reconstructs the unique
formal identity-coframe temporal covariant derivative.  This theorem is an
algebraic formula check, not an actual arbitrary-coframe Dirac equation. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitMatter_satisfies_identityCoframeFormula
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeMatterTimeActionLaw state space
      ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
            state).matter space -
          (sourceActionGeneratedJointCanonicalPhaseState source
            state).matter space +
        cauchyMatterConnectionAction state space
          canonicalLorentzianTimeDirection) := by
  rw [
    sourceActionGeneratedJointCanonicalPhaseUnitMatterIncrement]
  have covariant :
      actionGeneratedMatterRawTimeVelocity state space +
          cauchyMatterConnectionAction state space
            canonicalLorentzianTimeDirection =
        actionGeneratedMatterTimeCovariantDerivative state space := by
    unfold actionGeneratedMatterRawTimeVelocity
    abel
  rw [covariant]
  exact actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw
    state space

/-- The dual increment of the same reduced package satisfies the formal
identity-coframe adjoint formula without a separately supplied branch. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatter_satisfies_identityCoframeFormula
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeConjugateMatterTimeActionLaw state space
      ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
            state).conjugateMatter space -
        (sourceActionGeneratedJointCanonicalPhaseState source
          state).conjugateMatter space) := by
  rw [
    sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatterIncrement]
  exact actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
    state space

/-- On the identity-coframe domain, the packaged matter increment is accepted
both by the formal time formula and by the actual Dirac--Yukawa local field
equation from C3h96. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitMatter_isActualAt_identityCoframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    matterCoordinateEquiv
        ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).matter space -
          (sourceActionGeneratedJointCanonicalPhaseState source
            state).matter space) =
        fieldDirectionalDerivative
          (fun point =>
            matterCoordinateEquiv
              ((sourceActionGeneratedMatterLocalActualLift
                source state space).matter point))
          0 canonicalLorentzianTimeDirection ∧
      IdentityCoframeMatterTimeActionLaw state space
        ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).matter space -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).matter space +
          cauchyMatterConnectionAction state space
            canonicalLorentzianTimeDirection) ∧
      generatedContinuumMatterVector source 0 0
          (toContinuumPointField
            (sourceActionGeneratedMatterLocalActualLift source state space)
            0) =
        0 := by
  refine
    ⟨?_,
      sourceActionGeneratedJointCanonicalPhaseUnitMatter_satisfies_identityCoframeFormula
        source state space,
      sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
        source state space identityCoframe⟩
  rw [sourceActionGeneratedJointCanonicalPhaseUnitMatterIncrement]
  rw [sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin]
  simp [actionGeneratedMatterLocalJetCoordinate,
    canonicalLorentzianTimeDirection]

/-- On the identity-coframe domain, the packaged dual increment is accepted
by the formal adjoint time formula and by the actual all-direction matter
Euler--Lagrange equation from C3h97. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatter_isActualAt_identityCoframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    (∀ matter : DiracExteriorMatterCarrier,
      ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
            state).conjugateMatter space -
        (sourceActionGeneratedJointCanonicalPhaseState source
          state).conjugateMatter space) matter =
      fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedMatterDualLocalActualLift
            source state space).conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection) ∧
      IdentityCoframeConjugateMatterTimeActionLaw state space
        ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
              state).conjugateMatter space -
          (sourceActionGeneratedJointCanonicalPhaseState source
            state).conjugateMatter space) ∧
      ∀ direction : MatterCoordinateCarrier,
        matterEulerLagrangeDirectionalCoefficient source
            (sourceActionGeneratedMatterDualLocalActualLift
              source state space)
            direction 0 =
          0 := by
  refine
    ⟨?_,
      sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatter_satisfies_identityCoframeFormula
        source state space,
      sourceActionGeneratedMatterDualLocalActualLift_matterEulerLagrange_origin
        source state space identityCoframe⟩
  intro matter
  rw [
    sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatterIncrement]
  rw [
    sourceActionGeneratedMatterDualLocalActualLift_conjugateDerivative_origin]
  simp [actionGeneratedConjugateMatterLocalJet,
    canonicalLorentzianTimeDirection]

/-- Packaging theorem: one reduced carrier has the gravity--gauge and scalar
canonical updates as literal projections, while its matter and dual entries
satisfy only their formal identity-coframe formulas.

The stronger gravity--gauge and scalar laws are already proved for these
literal projections by
`sourceActionGeneratedGravityGaugeCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws`
and
`sourceActionGeneratedScalarCanonicalPhaseUnitUpdate_satisfies_actionSystem`.
-/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitUpdate_packages_sectorCandidates
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
        state).gravityGauge =
          sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate
            source 1 state ∧
      (sourceActionGeneratedJointCanonicalPhaseUpdate source 1
        state).scalar =
          sourceActionGeneratedScalarCanonicalPhaseUpdate source 1 state ∧
      (∀ space,
        IdentityCoframeMatterTimeActionLaw state space
          ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
                state).matter space -
              (sourceActionGeneratedJointCanonicalPhaseState source
                state).matter space +
            cauchyMatterConnectionAction state space
              canonicalLorentzianTimeDirection)) ∧
      ∀ space,
        IdentityCoframeConjugateMatterTimeActionLaw state space
          ((sourceActionGeneratedJointCanonicalPhaseUpdate source 1
                state).conjugateMatter space -
            (sourceActionGeneratedJointCanonicalPhaseState source
              state).conjugateMatter space) := by
  exact
    ⟨rfl, rfl,
      sourceActionGeneratedJointCanonicalPhaseUnitMatter_satisfies_identityCoframeFormula
        source state,
      sourceActionGeneratedJointCanonicalPhaseUnitConjugateMatter_satisfies_identityCoframeFormula
        source state⟩

/-! ## Positive and negative controls -/

/-- Any nonzero identity-coframe matter candidate makes the reduced common
unit package nontrivial.  This observes a produced component; it does not
supply a target state or establish arbitrary-coframe matter dynamics. -/
theorem
    sourceActionGeneratedJointCanonicalPhaseUnitUpdate_ne_initial_of_matterVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (velocityNonzero :
      actionGeneratedMatterRawTimeVelocity state space ≠ 0) :
    sourceActionGeneratedJointCanonicalPhaseUpdate source 1 state ≠
      sourceActionGeneratedJointCanonicalPhaseState source state := by
  intro updateFixed
  have componentFixed := congrArg
    (fun phase : StageNineJointCanonicalPhaseState =>
      phase.matter space)
    updateFixed
  apply velocityNonzero
  have increment :=
    sourceActionGeneratedJointCanonicalPhaseUnitMatterIncrement
      source state space
  rw [componentFixed, sub_self] at increment
  exact increment.symm

/-- Zero physical path length returns the initial reduced carrier.  This is
the negative regression for the shared-time constructor. -/
theorem sourceActionGeneratedJointCanonicalPhaseIdentityPath
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedJointCanonicalPhaseState source state :=
  sourceActionGeneratedJointCanonicalPhaseUpdate_zero source state

end

end
  SaturationMonoid.PhysicsCore.StageNineJointActionCanonicalPhaseUpdate
