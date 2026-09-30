import H0mework.Physics.DiracEvolution.SafeCanonicalDynamicMassProjection

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalMassProjectionConvergence

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDynamicBreakingVacuum

noncomputable section

set_option autoImplicit false

private theorem inverseMassProjection_pairing
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ)
    (massInvertible :
      (galerkinWeakMassOperator massForm time).IsInvertible)
    (functional : H →L[ℝ] ℝ)
    (test : H) :
    massForm time
        ((galerkinWeakMassOperator massForm time).inverse
          ((InnerProductSpace.toDual ℝ H).symm functional))
        test = functional test := by
  rw [← real_inner_galerkinWeakMassOperator,
    massInvertible.self_apply_inverse]
  change ((InnerProductSpace.toDual ℝ H)
    ((InnerProductSpace.toDual ℝ H).symm functional)) test = functional test
  exact congrArg (fun map : H →L[ℝ] ℝ ↦ map test)
    ((InnerProductSpace.toDual ℝ H).apply_symm_apply functional)

def canonicalPhysicalMassProjectionFunctional
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ] ℝ :=
  (fixedP506L0CauchySafeMatterL2MassForm
    time a b C operatorBound field).comp
      (fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount)

def canonicalPhysicalMassProjectionRiesz
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  (InnerProductSpace.toDual ℝ
    (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)).symm
      (canonicalPhysicalMassProjectionFunctional
        time a b C operatorBound testCount field)

def canonicalPhysicalMassProjectionCoefficient
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  (galerkinWeakMassOperator
    (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
    time).inverse
      (canonicalPhysicalMassProjectionRiesz
        time a b C operatorBound testCount field)

def canonicalPhysicalMassProjection
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) :
    CauchySafeMatterSpatialL2 a b → CauchySafeMatterSpatialL2 a b :=
  fun field ↦
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
      (canonicalPhysicalMassProjectionCoefficient
        time a b C operatorBound testCount field)

theorem canonicalPhysicalMassProjectionCoefficient_massLaw
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (canonicalPhysicalMassProjectionCoefficient
          time a b C operatorBound testCount field)
        test =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound field
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  have massInvertible :
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).IsInvertible := by
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time
  simpa only [canonicalPhysicalMassProjectionCoefficient,
    canonicalPhysicalMassProjectionRiesz,
    canonicalPhysicalMassProjectionFunctional,
    ContinuousLinearMap.comp_apply] using
      inverseMassProjection_pairing
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time massInvertible
        (canonicalPhysicalMassProjectionFunctional
          time a b C operatorBound testCount field)
        test

/-- The canonical finite action coefficient is exactly the physical-mass
projection coefficient of its native Volterra response. -/
theorem canonicalPhysicalMassProjectionCoefficient_actionResponse_eq
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    canonicalPhysicalMassProjectionCoefficient
        time a b C operatorBound testCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time a b testCount coefficient) =
      fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time coefficient := by
  have massInvertible :
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).IsInvertible := by
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time
  apply massInvertible.injective
  apply ext_inner_right ℝ
  intro test
  rw [real_inner_galerkinWeakMassOperator,
    real_inner_galerkinWeakMassOperator]
  exact (canonicalPhysicalMassProjectionCoefficient_massLaw
    time a b C operatorBound testCount
      (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        time a b testCount coefficient) test).trans
    (canonicalWeakActionOperator_l2MassProjectionLaw
      time a b C operatorBound testCount coefficient test).symm

/-- Synthesis turns the coefficient identity into an equality of physical
spatial velocities on the same canonical prefix. -/
theorem canonicalPhysicalMassProjection_actionResponse_eq_synthesizedVelocity
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    canonicalPhysicalMassProjection
        time a b C operatorBound testCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time a b testCount coefficient) =
      fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time coefficient) := by
  unfold canonicalPhysicalMassProjection
  rw [canonicalPhysicalMassProjectionCoefficient_actionResponse_eq]

/-- Prefix inclusion does not change the physical `L²` realization of the
native action response. -/
theorem canonicalWeakActionResponseL2_embedding
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        time a b secondCount
          (canonicalCoefficientEmbedding a b countMonotone coefficient) =
      fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        time a b firstCount coefficient := by
  apply Lp.ext
  filter_upwards [
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
      time a b secondCount
        (canonicalCoefficientEmbedding a b countMonotone coefficient),
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
      time a b firstCount coefficient] with space largeRead smallRead
  rw [largeRead, smallRead]
  exact congrFun
    (canonicalWeakActionResponse_embedding
      time a b countMonotone coefficient) space

/-- The failure of finite action velocity to commute with prefix inclusion is
exactly the difference of two canonical mass projections of one native
response. -/
theorem canonicalWeakActionOperator_embedding_commutator_synthesis
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b secondCount time
              (canonicalCoefficientEmbedding
                a b countMonotone coefficient) -
          canonicalCoefficientEmbedding a b countMonotone
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b firstCount time coefficient)) =
      canonicalPhysicalMassProjection time a b C operatorBound secondCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time a b firstCount coefficient) -
        canonicalPhysicalMassProjection time a b C operatorBound firstCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time a b firstCount coefficient) := by
  have embeddedSmallRead := canonicalSynthesis_embedding
    a b countMonotone
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b firstCount time coefficient)
  have largeRead :=
    (canonicalPhysicalMassProjection_actionResponse_eq_synthesizedVelocity
      time a b C operatorBound secondCount
        (canonicalCoefficientEmbedding
          a b countMonotone coefficient)).symm
  have smallRead :=
    (canonicalPhysicalMassProjection_actionResponse_eq_synthesizedVelocity
      time a b C operatorBound firstCount coefficient).symm
  have responseRead := canonicalWeakActionResponseL2_embedding
    time a b countMonotone coefficient
  calc
    _ =
        fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b secondCount time
                (canonicalCoefficientEmbedding
                  a b countMonotone coefficient)) -
          fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
            (canonicalCoefficientEmbedding a b countMonotone
              (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b firstCount time coefficient)) :=
      map_sub _ _ _
    _ =
        fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b secondCount time
                (canonicalCoefficientEmbedding
                  a b countMonotone coefficient)) -
          fixedP506L0CauchySafeMatterCanonicalSynthesis a b firstCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b firstCount time coefficient) := by
      exact congrArg
        (fun value ↦
          fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
              (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b secondCount time
                  (canonicalCoefficientEmbedding
                    a b countMonotone coefficient)) - value)
        embeddedSmallRead
    _ =
        canonicalPhysicalMassProjection time a b C operatorBound secondCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time a b secondCount
                (canonicalCoefficientEmbedding
                  a b countMonotone coefficient)) -
          canonicalPhysicalMassProjection time a b C operatorBound firstCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time a b firstCount coefficient) :=
      congrArg₂ (· - ·) largeRead smallRead
    _ = _ := by
      exact congrArg
        (fun field ↦
          canonicalPhysicalMassProjection
              time a b C operatorBound secondCount field -
            canonicalPhysicalMassProjection time a b C operatorBound firstCount
              (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
                time a b firstCount coefficient))
        responseRead

/-- The physical cross-level velocity splits into the large-level action on
the state error plus one exact projection-commutator tail. -/
theorem canonicalCrossLevelVelocity_synthesis_eq_errorAction_add_projectionTail
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (small : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount)
    (large : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b secondCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b secondCount time large -
          canonicalCoefficientEmbedding a b countMonotone
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b firstCount time small)) =
      fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b secondCount time
              (large - canonicalCoefficientEmbedding
                a b countMonotone small)) +
        (canonicalPhysicalMassProjection time a b C operatorBound secondCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time a b firstCount small) -
          canonicalPhysicalMassProjection time a b C operatorBound firstCount
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time a b firstCount small)) := by
  let largeAction := fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
    a b secondCount time
  let embed := canonicalCoefficientEmbedding a b countMonotone
  let smallAction := fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
    a b firstCount time
  let synthesis := fixedP506L0CauchySafeMatterCanonicalSynthesis
    a b secondCount
  have actionSub :
      largeAction (large - embed small) =
        largeAction large - largeAction (embed small) :=
    map_sub largeAction large (embed small)
  have coefficientSplit :
      largeAction large - embed (smallAction small) =
        largeAction (large - embed small) +
          (largeAction (embed small) - embed (smallAction small)) := by
    rw [actionSub]
    abel
  have commutatorRead :=
    canonicalWeakActionOperator_embedding_commutator_synthesis
      time a b C operatorBound countMonotone small
  calc
    _ = synthesis
        (largeAction (large - embed small) +
          (largeAction (embed small) - embed (smallAction small))) :=
      congrArg synthesis coefficientSplit
    _ = synthesis (largeAction (large - embed small)) +
        synthesis (largeAction (embed small) - embed (smallAction small)) :=
      map_add synthesis _ _
    _ = _ := by
      exact congrArg
        (fun value ↦ synthesis (largeAction (large - embed small)) + value)
        commutatorRead

theorem canonicalPhysicalMassProjection_bestApproximation
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b)
    (trialCoefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (field - canonicalPhysicalMassProjection
          time a b C operatorBound testCount field)
        (field - canonicalPhysicalMassProjection
          time a b C operatorBound testCount field) ≤
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (field - fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount trialCoefficient)
        (field - fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount trialCoefficient) := by
  let form := fixedP506L0CauchySafeMatterL2MassForm
    time a b C operatorBound
  let finiteForm := fixedP506L0CauchySafeMatterCanonicalWeakMassForm
    a b testCount time
  let synthesis := fixedP506L0CauchySafeMatterCanonicalSynthesis
    a b testCount
  let coefficient := canonicalPhysicalMassProjectionCoefficient
    time a b C operatorBound testCount field
  have ambientSymm : ∀ first second,
      form first second = form second first := by
    intro first second
    exact fixedP506L0CauchySafeMatterL2MassForm_symm
      time a b C operatorBound first second
  have ambientNonnegative : ∀ candidate, 0 ≤ form candidate candidate := by
    intro candidate
    exact fixedP506L0CauchySafeMatterL2MassForm_nonnegative
      time a b C operatorBound candidate
  have finiteRead : ∀ first second,
      finiteForm first second = form (synthesis first) (synthesis second) := by
    intro first second
    exact fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      time a b
      (fun mode point outside ↦
        cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
          a b testCount mode point outside)
      C operatorBound first second
  have projectionLaw : ∀ finiteTest,
      finiteForm coefficient finiteTest =
        form field (synthesis finiteTest) := by
    intro finiteTest
    exact canonicalPhysicalMassProjectionCoefficient_massLaw
      time a b C operatorBound testCount field finiteTest
  change form (field - synthesis coefficient) (field - synthesis coefficient) ≤
    form (field - synthesis trialCoefficient)
      (field - synthesis trialCoefficient)
  exact continuousBilinear_projection_bestApproximation
    form finiteForm synthesis field coefficient trialCoefficient
      ambientSymm ambientNonnegative finiteRead projectionLaw

private theorem canonicalPhysicalMassProjection_error_le_denseTest
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b)
    (denseTest testCount : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry denseTest ≤
      testCount) :
    fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (field - canonicalPhysicalMassProjection
          time a b C operatorBound testCount field)
        (field - canonicalPhysicalMassProjection
          time a b C operatorBound testCount field) ≤
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (field - cauchySafeMatterSmoothCompactTestToL2 a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b denseTest))
        (field - cauchySafeMatterSmoothCompactTestToL2 a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b denseTest)) := by
  let trialCoefficient :=
    fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount denseTest
  have synthesisEq :=
    fixedP506L0CauchySafeMatterCanonicalSynthesis_testCoefficient
      a b testCount denseTest entered
  have bestApproximation := canonicalPhysicalMassProjection_bestApproximation
    time a b C operatorBound testCount field trialCoefficient
  have trialEnergyEq := congrArg
    (fun trial ↦ fixedP506L0CauchySafeMatterL2MassForm
      time a b C operatorBound (field - trial) (field - trial))
    synthesisEq
  exact bestApproximation.trans_eq trialEnergyEq

private theorem tendsto_atTop_of_coercive_bestApproximation_dense
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (projection : ℕ → E)
    (field : E)
    (form : E →L[ℝ] E →L[ℝ] ℝ)
    (κ : ℝ)
    (κPositive : 0 < κ)
    (coercive : ∀ candidate,
      κ * ‖candidate‖ * ‖candidate‖ ≤ form candidate candidate)
    (denseTest : ℕ → E)
    (denseRange : DenseRange denseTest)
    (entry : ℕ → ℕ)
    (bestApproximation : ∀ denseIndex testCount,
      entry denseIndex ≤ testCount →
        form (field - projection testCount) (field - projection testCount) ≤
          form (field - denseTest denseIndex) (field - denseTest denseIndex)) :
    Tendsto projection atTop (nhds field) := by
  rw [Metric.tendsto_atTop]
  intro ε εPositive
  let energyNeighborhood : Set E :=
    { trial | form (field - trial) (field - trial) < κ * ε * ε }
  have energyNeighborhoodOpen : IsOpen energyNeighborhood := by
    apply isOpen_lt
    · exact ((form.continuous.comp (continuous_const.sub continuous_id)).clm_apply
        (continuous_const.sub continuous_id))
    · exact continuous_const
  have positiveEnergyRadius : 0 < κ * ε * ε :=
    mul_pos (mul_pos κPositive εPositive) εPositive
  have fieldMem : field ∈ energyNeighborhood := by
    change form (field - field) (field - field) < κ * ε * ε
    simpa only [sub_self, map_zero] using positiveEnergyRadius
  obtain ⟨denseIndex, denseTestMem⟩ :=
    denseRange.exists_mem_open energyNeighborhoodOpen ⟨field, fieldMem⟩
  refine ⟨entry denseIndex, ?_⟩
  intro testCount countMem
  have energyLt :=
    (bestApproximation denseIndex testCount countMem).trans_lt denseTestMem
  rw [dist_eq_norm]
  by_contra notClose
  have epsilonLe : ε ≤ ‖projection testCount - field‖ := le_of_not_gt notClose
  have coerciveBound := coercive (field - projection testCount)
  rw [norm_sub_rev] at epsilonLe
  have squaredLe : ε * ε ≤
      ‖field - projection testCount‖ * ‖field - projection testCount‖ :=
    mul_self_le_mul_self εPositive.le epsilonLe
  have lowerBound : κ * ε * ε ≤
      form (field - projection testCount) (field - projection testCount) := by
    calc
      κ * ε * ε = κ * (ε * ε) := by ring
      _ ≤ κ *
          (‖field - projection testCount‖ * ‖field - projection testCount‖) :=
        mul_le_mul_of_nonneg_left squaredLe κPositive.le
      _ = κ * ‖field - projection testCount‖ *
          ‖field - projection testCount‖ := by ring
      _ ≤ form (field - projection testCount) (field - projection testCount) :=
        coerciveBound
  exact (not_lt_of_ge lowerBound) energyLt

/-- Canonical physical-mass projections along the source-owned nested dense
prefix converge strongly to every fixed physical spatial field. -/
theorem canonicalPhysicalMassProjection_tendsto
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    Tendsto
      (fun testCount ↦ canonicalPhysicalMassProjection
        time a b C operatorBound testCount field)
      atTop (nhds field) := by
  let form := fixedP506L0CauchySafeMatterL2MassForm
    time a b C operatorBound
  obtain ⟨κ, κPositive, coercive⟩ :=
    fixedP506L0CauchySafeMatterL2MassForm_coercive
      time a b boxOrder C operatorBound
  apply tendsto_atTop_of_coercive_bestApproximation_dense
    (fun testCount ↦ canonicalPhysicalMassProjection
      time a b C operatorBound testCount field)
    field form κ κPositive coercive
    (fun denseTest ↦ cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b denseTest))
    (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b)
    cauchySafeMatterCanonicalInteriorTestEntry
  intro denseIndex testCount entered
  exact canonicalPhysicalMassProjection_error_le_denseTest
    time a b C operatorBound field denseIndex testCount entered

/-- On every fixed source-generated finite core state, the embedded canonical
action velocities converge strongly to the ambient native Volterra response.
This is the source-owned graph-consistency mouth; no target evolution or
convergence certificate is supplied. -/
theorem canonicalEmbeddedActionVelocity_tendsto_nativeResponse
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (firstCount : ℕ)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    Tendsto
      (fun extra ↦
        fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b (extra + firstCount)
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b (extra + firstCount) time
              (canonicalCoefficientEmbedding a b
                (Nat.le_add_left firstCount extra) coefficient)))
      atTop
      (nhds
        (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b firstCount coefficient)) := by
  let response :=
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
      time a b firstCount coefficient
  have projectionLimit :=
    (canonicalPhysicalMassProjection_tendsto
      time a b boxOrder C operatorBound response).comp
        (tendsto_add_atTop_nat firstCount)
  apply projectionLimit.congr'
  exact Filter.Eventually.of_forall fun extra ↦ by
    have actionRead :=
      canonicalPhysicalMassProjection_actionResponse_eq_synthesizedVelocity
        time a b C operatorBound (extra + firstCount)
          (canonicalCoefficientEmbedding a b
            (Nat.le_add_left firstCount extra) coefficient)
    have responseRead := canonicalWeakActionResponseL2_embedding
      time a b (Nat.le_add_left firstCount extra) coefficient
    calc
      canonicalPhysicalMassProjection
          time a b C operatorBound (extra + firstCount) response =
        canonicalPhysicalMassProjection time a b C operatorBound
          (extra + firstCount)
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time a b (extra + firstCount)
              (canonicalCoefficientEmbedding a b
                (Nat.le_add_left firstCount extra) coefficient)) := by
          exact congrArg
            (canonicalPhysicalMassProjection
              time a b C operatorBound (extra + firstCount)) responseRead.symm
      _ = _ := actionRead

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalMassProjectionConvergence
