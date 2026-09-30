import H0mework.Physics.DiracEvolution.SafeCanonicalResponseL2TimeContinuity
import H0mework.Physics.DiracEvolution.SafeCanonicalMassProjectionConvergence
import H0mework.Physics.DiracEvolution.SafeCanonicalUniformTimeMassGeometry

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeProjection

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open StageEightSourceGeneratedMatter
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalMassProjectionConvergence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalResponseL2TimeContinuity
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeMassGeometry
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private theorem fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp_norm_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C) :
    ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
      time a b C operatorBound‖ ≤ C := by
  rw [fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp,
    Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal
        (eLpNormEssSup
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time)
          (volume.restrict (Icc a b))) ≤
        ENNReal.toReal (ENNReal.ofReal C) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
      exact operatorBound space spaceMem
    _ = C := ENNReal.toReal_ofReal CNonnegative

theorem fixedP506L0CauchySafeMatterL2MassAction_norm_apply_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound field‖ ≤
        ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
  change
    ‖matterFiberMassRieszCoordinateBilinear.holder 2
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
        time a b C operatorBound) field‖ ≤ _
  calc
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ *
          ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
            time a b C operatorBound‖ * ‖field‖ :=
      matterFiberMassRieszCoordinateBilinear.norm_holder_apply_apply_le _ _
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
      gcongr
      exact fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp_norm_le
        time a b C CNonnegative operatorBound

private theorem fixedP506L0CauchySafeMatterL2MassForm_apply_self_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound field field ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖field‖ * ‖field‖ := by
  change inner ℝ
      (fixedP506L0CauchySafeMatterL2MassAction
        time a b C operatorBound field) field ≤ _
  calc
    _ ≤ |inner ℝ
        (fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field) field| := le_abs_self _
    _ ≤ ‖fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field‖ * ‖field‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖matterFiberMassRieszCoordinateBilinear‖ * C *
          ‖field‖) * ‖field‖ := by
      gcongr
      exact fixedP506L0CauchySafeMatterL2MassAction_norm_apply_le
        time a b C CNonnegative operatorBound field
    _ = _ := by ring

/-- The canonical physical-mass projection satisfies one source-owned
squared Céa estimate.  The estimate is independent of the selected finite
level once the compact-box mass bounds are fixed. -/
private theorem canonicalPhysicalMassProjection_error_sq_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (κ : ℝ)
    (pointwiseCoercivity :
      ∀ space ∈ Icc a b, ∀ value : MatterCoordinateCarrier,
        κ * ‖value‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy
            (time, space) value)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b)
    (trialCoefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    κ *
        ‖field - canonicalPhysicalMassProjection
          time a b C operatorBound testCount field‖ ^ 2 ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖field - fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount trialCoefficient‖ ^ 2 := by
  let error := field - canonicalPhysicalMassProjection
    time a b C operatorBound testCount field
  let trialError := field -
    fixedP506L0CauchySafeMatterCanonicalSynthesis
      a b testCount trialCoefficient
  calc
    κ * ‖error‖ ^ 2 = κ * ‖error‖ * ‖error‖ := by ring
    _ ≤ fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound error error :=
      fixedP506L0CauchySafeMatterL2MassForm_coercive_of_pointwise
        time a b C operatorBound κ pointwiseCoercivity error
    _ ≤ fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound trialError trialError := by
      exact canonicalPhysicalMassProjection_bestApproximation
        time a b C operatorBound testCount field trialCoefficient
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖trialError‖ * ‖trialError‖ :=
      fixedP506L0CauchySafeMatterL2MassForm_apply_self_le
        time a b C CNonnegative operatorBound trialError
    _ = ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖trialError‖ ^ 2 := by ring

/-- The source-mass projection is uniformly stable in physical `L²`, with
no dependence on the selected canonical prefix. -/
theorem canonicalPhysicalMassProjection_norm_stable
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (κ : ℝ)
    (pointwiseCoercivity :
      ∀ space ∈ Icc a b, ∀ value : MatterCoordinateCarrier,
        κ * ‖value‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy
            (time, space) value)
    (testCount : ℕ)
    (field : CauchySafeMatterSpatialL2 a b) :
    κ *
        ‖canonicalPhysicalMassProjection
          time a b C operatorBound testCount field‖ ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
  let projection := canonicalPhysicalMassProjection
    time a b C operatorBound testCount field
  let coefficient := canonicalPhysicalMassProjectionCoefficient
    time a b C operatorBound testCount field
  have projectionRead : projection =
      fixedP506L0CauchySafeMatterCanonicalSynthesis
        a b testCount coefficient := rfl
  have projectionMassLaw :
      fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound projection projection =
        fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound field projection := by
    have finiteRead :=
      fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        time a b
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
          a b testCount)
        C operatorBound coefficient coefficient
    have sourceRead := canonicalPhysicalMassProjectionCoefficient_massLaw
      time a b C operatorBound testCount field coefficient
    rw [projectionRead]
    change
      fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound
          (fixedMatterTrialL2
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            (fun mode ↦
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b testCount mode).continuous)
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
              a b testCount)
            coefficient a b)
          (fixedMatterTrialL2
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            (fun mode ↦
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b testCount mode).continuous)
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
              a b testCount)
            coefficient a b) =
        fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound field
          (fixedMatterTrialL2
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            (fun mode ↦
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b testCount mode).continuous)
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
              a b testCount)
            coefficient a b)
    exact finiteRead.symm.trans sourceRead
  have massPairingBound :
      |fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound field projection| ≤
        ‖matterFiberMassRieszCoordinateBilinear‖ * C *
          ‖field‖ * ‖projection‖ := by
    change |inner ℝ
      (fixedP506L0CauchySafeMatterL2MassAction
        time a b C operatorBound field) projection| ≤ _
    calc
      _ ≤ ‖fixedP506L0CauchySafeMatterL2MassAction
            time a b C operatorBound field‖ * ‖projection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖matterFiberMassRieszCoordinateBilinear‖ * C *
            ‖field‖) * ‖projection‖ := by
        gcongr
        exact fixedP506L0CauchySafeMatterL2MassAction_norm_apply_le
          time a b C CNonnegative operatorBound field
      _ = _ := by ring
  have coercive :
      κ * ‖projection‖ * ‖projection‖ ≤
        fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound projection projection :=
    fixedP506L0CauchySafeMatterL2MassForm_coercive_of_pointwise
      time a b C operatorBound κ pointwiseCoercivity projection
  have quadraticBound :
      κ * ‖projection‖ * ‖projection‖ ≤
        (‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖) *
          ‖projection‖ := by
    calc
      _ ≤ fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound projection projection := coercive
      _ = fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound field projection := projectionMassLaw
      _ ≤ |fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound field projection| := le_abs_self _
      _ ≤ _ := massPairingBound
  by_cases projectionZero : ‖projection‖ = 0
  · rw [projectionZero, mul_zero]
    positivity
  · have projectionPositive : 0 < ‖projection‖ :=
      lt_of_le_of_ne (norm_nonneg projection) (Ne.symm projectionZero)
    exact le_of_mul_le_mul_right (by
      simpa only [mul_assoc] using quadraticBound) projectionPositive

private theorem exists_uniform_canonical_dense_test_entry_of_continuous
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (response : ℝ → CauchySafeMatterSpatialL2 a b)
    (responseContinuous : Continuous response)
    (ε : ℝ)
    (εPositive : 0 < ε) :
    ∃ testCount : ℕ, ∀ time ∈ Icc timeStart timeEnd,
      ∃ denseTest : ℕ,
        cauchySafeMatterCanonicalInteriorTestEntry denseTest ≤ testCount ∧
          ‖response time -
              cauchySafeMatterSmoothCompactTestToL2 a b
                (cauchySafeMatterCanonicalInteriorDenseTest a b denseTest)‖ < ε := by
  let denseTest : ℕ → CauchySafeMatterSpatialL2 a b := fun test ↦
    cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b test)
  have responseImageCompact : IsCompact (response '' Icc timeStart timeEnd) :=
    isCompact_Icc.image responseContinuous
  have responseImageCovered :
      response '' Icc timeStart timeEnd ⊆
        ⋃ test, Metric.ball (denseTest test) ε := by
    intro field fieldMem
    obtain ⟨test, testClose⟩ :=
      (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b).exists_dist_lt
        field εPositive
    apply mem_iUnion.2
    refine ⟨test, ?_⟩
    apply Metric.mem_ball.2
    change dist field (denseTest test) < ε at testClose
    exact testClose
  obtain ⟨tests, testsCover⟩ := responseImageCompact.elim_finite_subcover
    (fun test ↦ Metric.ball (denseTest test) ε)
    (fun _ ↦ Metric.isOpen_ball)
    responseImageCovered
  refine ⟨∑ test ∈ tests,
      cauchySafeMatterCanonicalInteriorTestEntry test, ?_⟩
  intro time timeMem
  have responseMem : response time ∈ response '' Icc timeStart timeEnd :=
    ⟨time, timeMem, rfl⟩
  have covered := testsCover responseMem
  simp only [mem_iUnion] at covered
  obtain ⟨test, testMem, testClose⟩ := covered
  refine ⟨test, ?_, ?_⟩
  · exact Finset.single_le_sum
      (fun other _ ↦ Nat.zero_le
        (cauchySafeMatterCanonicalInteriorTestEntry other)) testMem
  · have distanceClose : dist (response time) (denseTest test) < ε :=
      Metric.mem_ball.1 testClose
    change ‖response time - denseTest test‖ < ε
    simpa only [dist_eq_norm] using distanceClose

/-- Canonical mass projections converge uniformly on every compact source-time
interval when they are applied to a continuous physical L² response. -/
theorem canonicalPhysicalMassProjection_tendstoUniformlyOn_of_continuous
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (response : ℝ → CauchySafeMatterSpatialL2 a b)
    (responseContinuous : Continuous response) :
    TendstoUniformly
      (fun testCount (time : Icc timeStart timeEnd) ↦
        canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2) testCount
          (response time.1))
      (fun time ↦ response time.1)
      atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε εPositive
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnTimeSpaceBox
      timeStart timeEnd timeOrder a b boxOrder
  let M := ‖matterFiberMassRieszCoordinateBilinear‖ * C
  have massOperatorNormNonnegative :
      0 ≤ ‖matterFiberMassRieszCoordinateBilinear‖ :=
    matterFiberMassRieszCoordinateBilinear.opNorm_nonneg
  have MNonnegative : 0 ≤ M :=
    mul_nonneg massOperatorNormNonnegative CNonnegative
  have targetPositive : 0 < κ * ε ^ 2 :=
    mul_pos κPositive (sq_pos_of_pos εPositive)
  obtain ⟨η, ηPositive, etaBound⟩ :=
    exists_pos_mul_lt targetPositive M
  let δ := min η 1
  have deltaPositive : 0 < δ := lt_min ηPositive zero_lt_one
  have deltaLeEta : δ ≤ η := min_le_left _ _
  have deltaLeOne : δ ≤ 1 := min_le_right _ _
  have deltaSquareLe : δ ^ 2 ≤ δ := by
    nlinarith [deltaPositive.le]
  have factorDeltaSquareLt : M * δ ^ 2 < κ * ε ^ 2 := by
    calc
      M * δ ^ 2 ≤ M * δ :=
        mul_le_mul_of_nonneg_left deltaSquareLe MNonnegative
      _ ≤ M * η :=
        mul_le_mul_of_nonneg_left deltaLeEta MNonnegative
      _ < κ * ε ^ 2 := etaBound
  obtain ⟨entry, denseApproximation⟩ :=
    exists_uniform_canonical_dense_test_entry_of_continuous
      timeStart timeEnd a b response responseContinuous δ deltaPositive
  filter_upwards [eventually_ge_atTop entry] with testCount countLarge
  intro time
  obtain ⟨denseTest, denseEntered, denseClose⟩ :=
    denseApproximation time.1 time.2
  let responseAt := response time.1
  let denseField := cauchySafeMatterSmoothCompactTestToL2 a b
    (cauchySafeMatterCanonicalInteriorDenseTest a b denseTest)
  let trialCoefficient :=
    fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount denseTest
  have entered :
      cauchySafeMatterCanonicalInteriorTestEntry denseTest ≤ testCount :=
    denseEntered.trans countLarge
  have synthesisEq :=
    fixedP506L0CauchySafeMatterCanonicalSynthesis_testCoefficient
      a b testCount denseTest entered
  have cea := canonicalPhysicalMassProjection_error_sq_le
    time.1 a b C CNonnegative (operatorBound time.1 time.2)
      κ (pointwiseCoercivity time.1 time.2)
      testCount responseAt trialCoefficient
  have ceaDense :
      κ * ‖responseAt - canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2)
          testCount responseAt‖ ^ 2 ≤
        M * ‖responseAt - denseField‖ ^ 2 := by
    simpa only [M, responseAt, denseField, trialCoefficient, synthesisEq] using cea
  have denseSquareLe : ‖responseAt - denseField‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) deltaPositive.le).2 denseClose.le
  have weightedErrorLt :
      κ * ‖responseAt - canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2)
          testCount responseAt‖ ^ 2 < κ * ε ^ 2 :=
    ceaDense.trans_lt <|
      (mul_le_mul_of_nonneg_left denseSquareLe MNonnegative).trans_lt
        factorDeltaSquareLt
  have errorSquareLt :
      ‖responseAt - canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2)
          testCount responseAt‖ ^ 2 < ε ^ 2 :=
    lt_of_mul_lt_mul_left weightedErrorLt κPositive.le
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) εPositive.le).mp errorSquareLt

private theorem canonicalPhysicalMassProjection_tendstoUniformlyOn_response
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (firstCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b firstCount) :
    TendstoUniformly
      (fun testCount (time : Icc timeStart timeEnd) ↦
        canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2) testCount
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time.1 a b firstCount coefficient))
      (fun time ↦
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time.1 a b firstCount coefficient)
      atTop := by
  exact canonicalPhysicalMassProjection_tendstoUniformlyOn_of_continuous
    timeStart timeEnd timeOrder a b boxOrder C CNonnegative operatorBound
      (fun time ↦
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b firstCount coefficient)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_continuous
        a b firstCount coefficient)

/-- Embedded finite action velocities of one source-generated finite core
converge to its native Volterra response uniformly on compact source time. -/
theorem canonicalEmbeddedActionVelocity_tendstoUniformlyOn_nativeResponse
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (firstCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b firstCount) :
    TendstoUniformly
      (fun extra (time : Icc timeStart timeEnd) ↦
        fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b (extra + firstCount)
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b (extra + firstCount) time.1
              (canonicalCoefficientEmbedding a b
                (Nat.le_add_left firstCount extra) coefficient)))
      (fun time ↦
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time.1 a b firstCount coefficient)
      atTop := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      timeStart timeEnd a b
  have projectionLimit :=
    canonicalPhysicalMassProjection_tendstoUniformlyOn_response
      timeStart timeEnd timeOrder a b boxOrder C CNonnegative operatorBound
        firstCount coefficient
  have projectionExtra : TendstoUniformly
      (fun extra (time : Icc timeStart timeEnd) ↦
        canonicalPhysicalMassProjection
          time.1 a b C (operatorBound time.1 time.2)
          (extra + firstCount)
          (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
            time.1 a b firstCount coefficient))
      (fun time ↦
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time.1 a b firstCount coefficient)
      atTop := by
    intro entourage entourageMem
    exact (tendsto_add_atTop_nat firstCount).eventually
      (projectionLimit entourage entourageMem)
  apply (tendstoUniformly_congr
    (Filter.Eventually.of_forall fun extra ↦ by
      funext time
      have actionRead :=
        canonicalPhysicalMassProjection_actionResponse_eq_synthesizedVelocity
          time.1 a b C (operatorBound time.1 time.2)
          (extra + firstCount)
          (canonicalCoefficientEmbedding a b
            (Nat.le_add_left firstCount extra) coefficient)
      have responseRead := canonicalWeakActionResponseL2_embedding
        time.1 a b (Nat.le_add_left firstCount extra) coefficient
      calc
        canonicalPhysicalMassProjection
            time.1 a b C (operatorBound time.1 time.2)
            (extra + firstCount)
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time.1 a b firstCount coefficient) =
          canonicalPhysicalMassProjection
            time.1 a b C (operatorBound time.1 time.2)
            (extra + firstCount)
            (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
              time.1 a b (extra + firstCount)
                (canonicalCoefficientEmbedding a b
                  (Nat.le_add_left firstCount extra) coefficient)) := by
            exact congrArg
              (canonicalPhysicalMassProjection
                time.1 a b C (operatorBound time.1 time.2)
                (extra + firstCount)) responseRead.symm
        _ = _ := actionRead)).mp projectionExtra

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeProjection
