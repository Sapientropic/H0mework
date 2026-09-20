import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# S9-C3h121: source/action-generated joint primitive Cauchy path

C3h101 already constructs one complete primitive local actual
`StageNineHolonomicConfiguration` directly from a proof-free source, a
primitive Cauchy state, and the existing local actions.  C3h107 supplies the
positive P506/L0 source specialization with nonzero matter spin.

This module restores the path-first/action-first order:

```text
proof-free source + primitive Cauchy state
→ actual local action germ U
→ canonical Cauchy path t ↦ U|Σₜ
→ complete primitive first-jet law
→ later equation/residual acceptance.
```

The constructor does not read an equation residual, response coordinate,
zero-fiber witness, target endpoint, preimage, range certificate, quotient
representative, or branch receipt.  The currently unevolved coframe,
gravity auxiliary, multiplier, and P286 auxiliary have zero time tangent;
that is an explicit boundary of the present local action germ, not a claim
that the final interacting Stage-9 vector field has been produced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyPath

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceGeneratedMatterSpinActionUpdate
open DiracExteriorMatterAction
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

/-! ## Actual-first primitive path -/

/-- The complete local actual is generated before a time path is read from
it.  This is a faithful restriction of all primitive fields carried by that
single `U`. -/
def sourceActionGeneratedJointPrimitiveCauchyPath
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    StageNineCauchyState :=
  canonicalCauchyRestriction time
    (sourceActionGeneratedJointLocalActualLift source state space)

/-- The initial slice is an output of the same generated actual. -/
def sourceActionGeneratedJointPrimitiveCauchyInitialSlice
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineCauchyState :=
  sourceActionGeneratedJointPrimitiveCauchyPath source state space 0

@[simp] theorem sourceActionGeneratedJointPrimitiveCauchyPath_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedJointPrimitiveCauchyPath source state space 0 =
      sourceActionGeneratedJointPrimitiveCauchyInitialSlice
        source state space :=
  rfl

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  rw [canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  simp

private theorem deriv_along_canonicalCauchyOrigin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (differentiable : DifferentiableAt ℝ field 0) :
    deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 =
      fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection := by
  let line := fun time : ℝ =>
    time • coordinateDirection canonicalLorentzianTimeDirection
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)
  have outerDerivative :
      HasFDerivAt field (fderiv ℝ field 0) (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed :=
    outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : ℝ =>
      field (canonicalCauchySlicePoint time 0)) =
        field ∘ line by
    funext time
    simp only [Function.comp_apply, line,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]]
  exact composed.deriv

/-! ## One synchronized primitive action velocity -/

/-- All primitive physical-time coordinates generated by the current local
action grammar.  This is data, not an on-shell receipt. -/
@[ext] structure StageNineJointPrimitiveActionVelocity where
  coframe :
    LorentzianIndex → LorentzianIndex → ℝ
  gravityConnection :
    LorentzianIndex → Fin 6 → ℝ
  gravityAuxiliary :
    Fin 6 → Fin 6 → ℝ
  gravitySimplicityMultiplier :
    Fin 6 → Fin 6 → ℝ
  p286Connection :
    LorentzianIndex → P286CoordinateCarrier
  p286Auxiliary :
    Fin 6 → P286CoordinateCarrier
  scalar :
    ScalarCoordinateCarrier
  scalarVelocity :
    ScalarCoordinateCarrier
  matter :
    MatterCoordinateCarrier
  conjugateMatter :
    DiracExteriorMatterCarrier → ℂ

/-- The current primitive action velocity is generated from the same source
and Cauchy state that generate the local actual.  Zero components are stated
explicitly instead of being reconstructed from a downstream residual. -/
def sourceActionGeneratedJointPrimitiveActionVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity where
  coframe := 0
  gravityConnection :=
    actionGeneratedLorentzLocalConnectionJet state space
      canonicalLorentzianTimeDirection
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  p286Connection :=
    sourceGeneratedP286ActionLocalConnectionJet source state space
      canonicalLorentzianTimeDirection
  p286Auxiliary := 0
  scalar := state.scalarVelocity space
  scalarVelocity := 0
  matter :=
    actionGeneratedMatterLocalJetCoordinate state space
      canonicalLorentzianTimeDirection
  conjugateMatter :=
    actionGeneratedConjugateMatterLocalJet state space
      canonicalLorentzianTimeDirection

/-! ## Complete primitive origin and tangent laws -/

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialCoframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).coframe 0 =
      state.coframe space := by
  simp [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction,
    sourceActionGeneratedJointLocalActualLift,
    sourceActionGeneratedMatterDualScalarLocalActualLift,
    sourceActionGeneratedMatterDualLocalActualLift,
    sourceActionGeneratedMatterLocalActualLift,
    sourceActionGeneratedGravityGaugeLocalActualLift,
    sourceGeneratedP286ActionLocalActualLift]

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityConnection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).gravityConnection 0 =
      state.gravityConnection space := by
  simp [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero,
    sourceActionGeneratedJointLocalActualLift_initialGravityConnection]

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityAuxiliary
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).gravityAuxiliary 0 =
      actionGeneratedGravityAuxiliary state space := by
  rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialMultiplier
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).gravitySimplicityMultiplier 0 =
      state.gravitySimplicityMultiplier space := by
  rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Connection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).gaugeConnection 0 =
      state.gaugeConnection space := by
  simp only [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  funext formDirection
  change
    sourceGeneratedP286ActionLocalConnection source state space 0
        formDirection =
      state.gaugeConnection space formDirection
  exact sourceGeneratedP286ActionLocalConnection_origin
    source state space formDirection

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Auxiliary
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).gaugeAuxiliary 0 =
      state.gaugeAuxiliary space := by
  rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialScalar
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).scalar 0 =
      state.scalar space := by
  simp only [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  change
    (sourceActionGeneratedMatterDualScalarLocalActualLift
      source state space).scalar 0 =
      state.scalar space
  exact
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
      source state space

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialScalarVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).scalarVelocity 0 =
      state.scalarVelocity space := by
  simp only [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  change
    fieldDirectionalDerivative
        (sourceActionGeneratedMatterDualScalarLocalActualLift
          source state space).scalar
        0 canonicalLorentzianTimeDirection =
      state.scalarVelocity space
  exact
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalarTimeVelocity_origin
      source state space

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).matter 0 =
      state.matter space := by
  simp only [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  change
    (sourceActionGeneratedMatterLocalActualLift
      source state space).matter 0 =
      state.matter space
  exact sourceActionGeneratedMatterLocalActualLift_matter_origin
    source state space

theorem sourceActionGeneratedJointPrimitiveCauchyPath_initialConjugateMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space 0).conjugateMatter 0 =
      state.conjugateMatter space := by
  simp only [sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  change
    (sourceActionGeneratedMatterDualLocalActualLift
      source state space).conjugateMatter 0 =
      state.conjugateMatter space
  exact sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin
    source state space

theorem sourceActionGeneratedJointPrimitiveCauchyPath_coframeTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).coframe 0 internal coordinate)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).coframe internal coordinate := by
  change deriv (fun _ : ℝ => state.coframe space internal coordinate) 0 = 0
  simp

theorem sourceActionGeneratedJointPrimitiveCauchyPath_gravityConnectionTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    deriv
        (fun time : ℝ =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedJointPrimitiveCauchyPath
              source state space time).gravityConnection 0)
            formDirection internalPair)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).gravityConnection
          formDirection internalPair := by
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  let field : BasePoint → ℝ := fun point =>
    loweredLorentzConnectionCoefficient
      (actual.gravityConnection point) formDirection internalPair
  have componentDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          actual.gravityConnection point formDirection
            (lorentzBivectorFirst internalPair)
            (lorentzBivectorSecond internalPair))
        0 :=
    ((sourceActionGeneratedJointLocalActualLift_smooth source state space
      |>.2.1 formDirection
        (lorentzBivectorFirst internalPair)
        (lorentzBivectorSecond internalPair)).differentiable
          (by simp)).differentiableAt
  have fieldDifferentiable : DifferentiableAt ℝ field 0 := by
    simpa [field, loweredLorentzConnectionCoefficient] using
      componentDifferentiable.const_mul
        (minkowskiInternalSign (lorentzBivectorFirst internalPair))
  calc
    _ = deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 := rfl
    _ = fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin field fieldDifferentiable
    _ = actionGeneratedLorentzLocalConnectionJet state space
          canonicalLorentzianTimeDirection formDirection internalPair := by
      exact
        sourceActionGeneratedJointLocalActualLift_lorentzLoweredDerivative
          source state space canonicalLorentzianTimeDirection
            formDirection internalPair
    _ = _ := rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_gravityAuxiliaryTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).gravityAuxiliary
              0 internalPair spacetimePair)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).gravityAuxiliary
          internalPair spacetimePair := by
  change
    deriv
        (fun _ : ℝ =>
          actionGeneratedGravityAuxiliary state space
            internalPair spacetimePair)
        0 =
      0
  simp

theorem sourceActionGeneratedJointPrimitiveCauchyPath_multiplierTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).gravitySimplicityMultiplier
              0 internalPair spacetimePair)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).gravitySimplicityMultiplier
          internalPair spacetimePair := by
  change
    deriv
        (fun _ : ℝ =>
          state.gravitySimplicityMultiplier
            space internalPair spacetimePair)
        0 =
      0
  simp

theorem sourceActionGeneratedJointPrimitiveCauchyPath_p286ConnectionTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    deriv
        (fun time : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyPath
              source state space time).gaugeConnection 0 formDirection))
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).p286Connection formDirection := by
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  let field : BasePoint → P286CoordinateCarrier := fun point =>
    p286CoordinateEquiv (actual.gaugeConnection point formDirection)
  have fieldDifferentiable : DifferentiableAt ℝ field 0 :=
    ((sourceActionGeneratedJointLocalActualLift_smooth source state space
      |>.2.2.2.2.1 formDirection).differentiable
        (by simp)).differentiableAt
  calc
    _ = deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 := rfl
    _ = fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin field fieldDifferentiable
    _ =
        sourceGeneratedP286ActionLocalConnectionJet source state space
          canonicalLorentzianTimeDirection formDirection := by
      change
        p286GaugeConnectionCoordinateDerivative
            (sourceGeneratedP286ActionLocalActualLift source state space)
            0 canonicalLorentzianTimeDirection formDirection =
          _
      exact sourceGeneratedP286ActionLocalActualLift_connectionDerivative
        source state space canonicalLorentzianTimeDirection formDirection
    _ = _ := rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_p286AuxiliaryTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    deriv
        (fun time : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyPath
              source state space time).gaugeAuxiliary 0 pair))
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).p286Auxiliary pair := by
  change
    deriv
        (fun _ : ℝ =>
          p286CoordinateEquiv (state.gaugeAuxiliary space pair))
        0 =
      0
  simp

theorem sourceActionGeneratedJointPrimitiveCauchyPath_scalarTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).scalar 0)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).scalar := by
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  have scalarDifferentiable : DifferentiableAt ℝ actual.scalar 0 :=
    ((sourceActionGeneratedJointLocalActualLift_smooth source state space
      |>.2.2.2.2.2.2.1).differentiable (by simp)).differentiableAt
  calc
    _ = fieldDirectionalDerivative actual.scalar 0
        canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin actual.scalar scalarDifferentiable
    _ = state.scalarVelocity space := by
      change
        fieldDirectionalDerivative
            (sourceActionGeneratedMatterDualScalarLocalActualLift
              source state space).scalar
            0 canonicalLorentzianTimeDirection =
          _
      exact
        sourceActionGeneratedMatterDualScalarLocalActualLift_scalarTimeVelocity_origin
          source state space
    _ = _ := rfl

private theorem actionGeneratedScalarLocalField_timeDerivative_at
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (actionGeneratedScalarLocalField state space)
        point canonicalLorentzianTimeDirection =
      state.scalarVelocity space := by
  unfold fieldDirectionalDerivative actionGeneratedScalarLocalField
  rw [fderiv_const_add]
  rw [(actionGeneratedScalarLocalIncrement state space).hasFDerivAt.fderiv]
  simp [actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate, localBaseCoordinate,
    coordinateDirection, canonicalLorentzianTimeDirection,
    Fin.sum_univ_four]

theorem sourceActionGeneratedJointPrimitiveCauchyPath_scalarVelocityTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).scalarVelocity 0)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).scalarVelocity := by
  rw [show
    (fun time : ℝ =>
      (sourceActionGeneratedJointPrimitiveCauchyPath
        source state space time).scalarVelocity 0) =
        fun _ : ℝ => state.scalarVelocity space by
    funext time
    change
      fieldDirectionalDerivative
          (actionGeneratedScalarLocalField state space)
          (canonicalCauchySlicePoint time 0)
          canonicalLorentzianTimeDirection =
        state.scalarVelocity space
    exact actionGeneratedScalarLocalField_timeDerivative_at
      state space (canonicalCauchySlicePoint time 0)]
  simp [sourceActionGeneratedJointPrimitiveActionVelocity]

theorem sourceActionGeneratedJointPrimitiveCauchyPath_matterTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyPath
              source state space time).matter 0))
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).matter := by
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  let field : BasePoint → MatterCoordinateCarrier := fun point =>
    matterCoordinateEquiv (actual.matter point)
  have fieldDifferentiable : DifferentiableAt ℝ field 0 :=
    ((sourceActionGeneratedJointLocalActualLift_smooth source state space
      |>.2.2.2.2.2.2.2.1).differentiable
        (by simp)).differentiableAt
  calc
    _ = deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 := rfl
    _ = fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin field fieldDifferentiable
    _ =
        actionGeneratedMatterLocalJetCoordinate state space
          canonicalLorentzianTimeDirection := by
      change
        fieldDirectionalDerivative
            (fun point =>
              matterCoordinateEquiv
                ((sourceActionGeneratedMatterLocalActualLift
                  source state space).matter point))
            0 canonicalLorentzianTimeDirection =
          _
      exact sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
        source state space canonicalLorentzianTimeDirection
    _ = _ := rfl

theorem sourceActionGeneratedJointPrimitiveCauchyPath_conjugateMatterTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source state space time).conjugateMatter 0 matter)
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).conjugateMatter matter := by
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  let field : BasePoint → ℂ := fun point =>
    actual.conjugateMatter point matter
  have fieldEquality :
      field =
        fun point =>
          actionGeneratedConjugateMatterLocalField
            state space point matter :=
    rfl
  have fieldDifferentiable : DifferentiableAt ℝ field 0 := by
    rw [fieldEquality]
    rw [show
      (fun point =>
        actionGeneratedConjugateMatterLocalField
          state space point matter) =
        fun point =>
          state.conjugateMatter space matter +
            actionGeneratedConjugateMatterLocalEvaluationIncrement
              state space matter point by
      funext point
      exact actionGeneratedConjugateMatterLocalField_apply
        state space point matter]
    fun_prop
  calc
    _ = deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 := rfl
    _ = fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin field fieldDifferentiable
    _ =
        actionGeneratedConjugateMatterLocalJet state space
          canonicalLorentzianTimeDirection matter := by
      change
        fieldDirectionalDerivative
            (fun point =>
              (sourceActionGeneratedMatterDualLocalActualLift
                source state space).conjugateMatter point matter)
            0 canonicalLorentzianTimeDirection =
          _
      exact
        sourceActionGeneratedMatterDualLocalActualLift_conjugateDerivative_origin
          source state space matter canonicalLorentzianTimeDirection
    _ = _ := rfl

/-! ## Bundled producer law -/

/-- One actual-first law for all primitive values and physical-time
tangents.  Equation and residual fields are deliberately absent. -/
structure StageNineJointPrimitiveActionCauchyPathLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (actual : StageNineHolonomicConfiguration)
    (path : ℝ → StageNineCauchyState) : Prop where
  actualGenerated :
    actual =
      sourceActionGeneratedJointLocalActualLift source state space
  pathGenerated :
    path = fun time =>
      canonicalCauchyRestriction time actual
  smooth :
    actual.Smooth
  initialCoframe :
    (path 0).coframe 0 = state.coframe space
  initialGravityConnection :
    (path 0).gravityConnection 0 = state.gravityConnection space
  initialGravityAuxiliary :
    (path 0).gravityAuxiliary 0 =
      actionGeneratedGravityAuxiliary state space
  initialMultiplier :
    (path 0).gravitySimplicityMultiplier 0 =
      state.gravitySimplicityMultiplier space
  initialP286Connection :
    (path 0).gaugeConnection 0 = state.gaugeConnection space
  initialP286Auxiliary :
    (path 0).gaugeAuxiliary 0 = state.gaugeAuxiliary space
  initialScalar :
    (path 0).scalar 0 = state.scalar space
  initialScalarVelocity :
    (path 0).scalarVelocity 0 = state.scalarVelocity space
  initialMatter :
    (path 0).matter 0 = state.matter space
  initialConjugateMatter :
    (path 0).conjugateMatter 0 = state.conjugateMatter space
  coframeTangent :
    ∀ internal coordinate,
      deriv
          (fun time : ℝ =>
            (path time).coframe 0 internal coordinate)
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).coframe internal coordinate
  gravityConnectionTangent :
    ∀ formDirection internalPair,
      deriv
          (fun time : ℝ =>
            loweredLorentzConnectionCoefficient
              ((path time).gravityConnection 0)
              formDirection internalPair)
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).gravityConnection
            formDirection internalPair
  gravityAuxiliaryTangent :
    ∀ internalPair spacetimePair,
      deriv
          (fun time : ℝ =>
            (path time).gravityAuxiliary
              0 internalPair spacetimePair)
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).gravityAuxiliary
            internalPair spacetimePair
  multiplierTangent :
    ∀ internalPair spacetimePair,
      deriv
          (fun time : ℝ =>
            (path time).gravitySimplicityMultiplier
              0 internalPair spacetimePair)
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).gravitySimplicityMultiplier
            internalPair spacetimePair
  p286ConnectionTangent :
    ∀ formDirection,
      deriv
          (fun time : ℝ =>
            p286CoordinateEquiv
              ((path time).gaugeConnection 0 formDirection))
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).p286Connection formDirection
  p286AuxiliaryTangent :
    ∀ pair,
      deriv
          (fun time : ℝ =>
            p286CoordinateEquiv
              ((path time).gaugeAuxiliary 0 pair))
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).p286Auxiliary pair
  scalarTangent :
    deriv (fun time : ℝ => (path time).scalar 0) 0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).scalar
  scalarVelocityTangent :
    deriv (fun time : ℝ => (path time).scalarVelocity 0) 0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).scalarVelocity
  matterTangent :
    deriv
        (fun time : ℝ =>
          matterCoordinateEquiv ((path time).matter 0))
        0 =
      (sourceActionGeneratedJointPrimitiveActionVelocity
        source state space).matter
  conjugateMatterTangent :
    ∀ matter,
      deriv
          (fun time : ℝ =>
            (path time).conjugateMatter 0 matter)
          0 =
        (sourceActionGeneratedJointPrimitiveActionVelocity
          source state space).conjugateMatter matter

/-- Frontier theorem: source and local action generate one full primitive
actual and its complete Cauchy update law before any residual is consulted. -/
theorem sourceActionGeneratedJointPrimitiveCauchyPath_realizes
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionCauchyPathLaw
      source state space
      (sourceActionGeneratedJointLocalActualLift source state space)
      (sourceActionGeneratedJointPrimitiveCauchyPath
        source state space) := by
  exact
    { actualGenerated := rfl
      pathGenerated := rfl
      smooth :=
        sourceActionGeneratedJointLocalActualLift_smooth source state space
      initialCoframe :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialCoframe
          source state space
      initialGravityConnection :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityConnection
          source state space
      initialGravityAuxiliary :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityAuxiliary
          source state space
      initialMultiplier :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialMultiplier
          source state space
      initialP286Connection :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Connection
          source state space
      initialP286Auxiliary :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Auxiliary
          source state space
      initialScalar :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialScalar
          source state space
      initialScalarVelocity :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialScalarVelocity
          source state space
      initialMatter :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialMatter
          source state space
      initialConjugateMatter :=
        sourceActionGeneratedJointPrimitiveCauchyPath_initialConjugateMatter
          source state space
      coframeTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_coframeTangent
          source state space
      gravityConnectionTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_gravityConnectionTangent
          source state space
      gravityAuxiliaryTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_gravityAuxiliaryTangent
          source state space
      multiplierTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_multiplierTangent
          source state space
      p286ConnectionTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_p286ConnectionTangent
          source state space
      p286AuxiliaryTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_p286AuxiliaryTangent
          source state space
      scalarTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_scalarTangent
          source state space
      scalarVelocityTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_scalarVelocityTangent
          source state space
      matterTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_matterTangent
          source state space
      conjugateMatterTangent :=
        sourceActionGeneratedJointPrimitiveCauchyPath_conjugateMatterTangent
          source state space }

/-! ## P506/L0 positive specialization -/

def positiveSourceActionGeneratedJointPrimitiveCauchyPath
    (time : ℝ) :
    StageNineCauchyState :=
  sourceActionGeneratedJointPrimitiveCauchyPath
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0 time

theorem positiveSourceActionGeneratedJointPrimitiveCauchyPath_realizes :
    StageNineJointPrimitiveActionCauchyPathLaw
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterActual
      positiveSourceActionGeneratedJointPrimitiveCauchyPath := by
  exact sourceActionGeneratedJointPrimitiveCauchyPath_realizes
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyPath
