import Mathlib.Analysis.Calculus.ContDiff.RCLike
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Canonical first-primitive ambient first-jet regularity

The canonical first time primitive factors as the time coordinate multiplied
by a fixed-interval average.  For a locally `C¹` profile, that average is
locally Lipschitz.  When the action profile vanishes at the common
occurrence, both factors vanish there, so the full ambient first derivative
of their product converges to zero.  The conclusion controls temporal and
spatial directions together, including nearby points at which the average
itself is not differentiable.

This theorem reads the regularity of an already generated canonical
primitive.  It accepts no residual, target jet, branch witness, or
zero-fiber receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity

open Asymptotics Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped Interval NNReal Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance (priority := high)
    canonicalFirstPrimitiveBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance (priority := high)
    canonicalFirstPrimitiveBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

private theorem canonical_time_single
    (time : ℝ) :
    EuclideanSpace.single canonicalLorentzianTimeDirection time =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

private def normalizedCanonicalTimeSliceCLM
    (parameter : ℝ) : BasePoint →L[ℝ] BasePoint :=
  parameter •
      canonicalTimeProjection.smulRight
        (coordinateDirection canonicalLorentzianTimeDirection) +
    canonicalSpatialInclusion.comp canonicalSpatialProjection

private theorem normalizedCanonicalTimeSliceCLM_apply
    (parameter : ℝ) (point : BasePoint) :
    normalizedCanonicalTimeSliceCLM parameter point =
      canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point) := by
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion,
    canonical_time_single]
  simp only [normalizedCanonicalTimeSliceCLM,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    smul_smul]
  rw [mul_comm parameter]

private def normalizedCanonicalTimeSliceBound : ℝ :=
  ‖canonicalTimeProjection.smulRight
      (coordinateDirection canonicalLorentzianTimeDirection)‖ +
    ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ + 1

private theorem normalizedCanonicalTimeSliceBound_pos :
    0 < normalizedCanonicalTimeSliceBound := by
  unfold normalizedCanonicalTimeSliceBound
  positivity

private theorem normalizedCanonicalTimeSliceCLM_norm_lt_bound
    {parameter : ℝ} (parameter_mem : parameter ∈ Icc (0 : ℝ) 1) :
    ‖normalizedCanonicalTimeSliceCLM parameter‖ <
      normalizedCanonicalTimeSliceBound := by
  unfold normalizedCanonicalTimeSliceCLM
    normalizedCanonicalTimeSliceBound
  calc
    ‖parameter •
          canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection) +
        canonicalSpatialInclusion.comp canonicalSpatialProjection‖
        ≤ ‖parameter •
            canonicalTimeProjection.smulRight
              (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ :=
      norm_add_le _ _
    _ = |parameter| *
          ‖canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ := by
      have parameter_abs : |parameter| ≤ 1 := by
        rw [abs_of_nonneg parameter_mem.1]
        exact parameter_mem.2
      exact add_le_add
        (mul_le_of_le_one_left
          (norm_nonneg
            (canonicalTimeProjection.smulRight
              (coordinateDirection canonicalLorentzianTimeDirection)))
          parameter_abs)
        le_rfl
    _ < _ := by linarith

private def normalizedFirstAverage
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) : E :=
  ∫ parameter in (0 : ℝ)..1,
    profile (normalizedCanonicalTimeSliceCLM parameter point)

private theorem canonicalTimePrimitive_scaleIdentity
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) :
    canonicalTimePrimitive profile point =
      canonicalTimeProjection point • normalizedFirstAverage profile point := by
  unfold canonicalTimePrimitive normalizedFirstAverage
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  have scaled :=
    (intervalIntegral.smul_integral_comp_mul_left
      (f := fun candidateTime =>
        profile (canonicalCauchySlicePoint candidateTime space))
      (a := (0 : ℝ)) (b := (1 : ℝ)) time).symm
  simpa [time, space, normalizedCanonicalTimeSliceCLM_apply] using scaled

private theorem normalizedFirstAverage_lipschitzOnWith
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {profile : BasePoint → E}
    {target domain : Set BasePoint}
    {K : ℝ≥0}
    (profileLipschitz : LipschitzOnWith K profile target)
    (mapsTo :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          normalizedCanonicalTimeSliceCLM parameter point ∈ target) :
    LipschitzOnWith
      (K * ⟨normalizedCanonicalTimeSliceBound,
        normalizedCanonicalTimeSliceBound_pos.le⟩)
      (normalizedFirstAverage profile) domain := by
  have intervalIntegrable
      {point : BasePoint} (point_mem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter =>
          profile (normalizedCanonicalTimeSliceCLM parameter point))
        MeasureTheory.volume 0 1 := by
    have sliceContinuous :
        Continuous fun parameter : ℝ =>
          normalizedCanonicalTimeSliceCLM parameter point := by
      unfold normalizedCanonicalTimeSliceCLM
      fun_prop
    have profileContinuous := profileLipschitz.continuousOn
    have composed :
        ContinuousOn
          (fun parameter =>
            profile (normalizedCanonicalTimeSliceCLM parameter point))
          (Icc (0 : ℝ) 1) := by
      exact profileContinuous.comp sliceContinuous.continuousOn
        (fun parameter parameter_mem => mapsTo point point_mem parameter
          parameter_mem)
    exact composed.intervalIntegrable_of_Icc (by norm_num)
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [dist_eq_norm]
  unfold normalizedFirstAverage
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable first_mem) (intervalIntegrable second_mem)]
  have estimate :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun parameter =>
        profile (normalizedCanonicalTimeSliceCLM parameter first) -
          profile (normalizedCanonicalTimeSliceCLM parameter second))
      (C := ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
        ‖first - second‖)
      (fun parameter parameter_mem => by
        have parameter_mem' : parameter ∈ Icc (0 : ℝ) 1 := by
          have actual := uIoc_subset_uIcc parameter_mem
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
        calc
          ‖profile (normalizedCanonicalTimeSliceCLM parameter first) -
              profile (normalizedCanonicalTimeSliceCLM parameter second)‖
              ≤ (K : ℝ) *
                  ‖normalizedCanonicalTimeSliceCLM parameter first -
                    normalizedCanonicalTimeSliceCLM parameter second‖ :=
            profileLipschitz.norm_sub_le
              (mapsTo first first_mem parameter parameter_mem')
              (mapsTo second second_mem parameter parameter_mem')
          _ = (K : ℝ) *
                ‖normalizedCanonicalTimeSliceCLM parameter
                  (first - second)‖ := by
            rw [map_sub]
          _ ≤ (K : ℝ) *
                (normalizedCanonicalTimeSliceBound * ‖first - second‖) := by
            apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
            exact
              (normalizedCanonicalTimeSliceCLM parameter).le_opNorm
                  (first - second)
                |>.trans
                  (mul_le_mul_of_nonneg_right
                    (normalizedCanonicalTimeSliceCLM_norm_lt_bound
                      parameter_mem').le
                    (norm_nonneg _))
          _ = ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                ‖first - second‖ := by ring)
  change
    ‖∫ parameter in (0 : ℝ)..1,
        profile (normalizedCanonicalTimeSliceCLM parameter first) -
          profile (normalizedCanonicalTimeSliceCLM parameter second)‖ ≤
      ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
        ‖first - second‖
  simpa using estimate

private theorem clm_smul_continuousAt_hasFDerivAt_zero
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    (continuousAt : ContinuousAt field 0) :
    HasFDerivAt (fun point => L point • field point)
      (L.smulRight (field 0)) 0 := by
  have linearBound :
      (fun point : X => L point) =O[𝓝 0]
        (fun point : X => ‖point‖) :=
    (L.isBigO_id (𝓝 0)).norm_right
  have fieldRemainder :
      (fun point : X => field point - field 0) =o[𝓝 0]
        (fun _ : X => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    exact tendsto_sub_nhds_zero_iff.mpr continuousAt
  have productNormRemainder :
      (fun point : X => L point • (field point - field 0)) =o[𝓝 0]
        (fun point : X => ‖point‖) := by
    simpa only [smul_eq_mul, mul_one] using
      linearBound.smul_isLittleO fieldRemainder
  have productRemainder :
      (fun point : X => L point • (field point - field 0)) =o[𝓝 0]
        (fun point : X => point) :=
    productNormRemainder.of_norm_right
  have derivativeRemainder :
      (fun point : X =>
        (L point • field point) - (L 0 • field 0) -
          (L.smulRight (field 0)) (point - 0)) =o[𝓝 0]
        (fun point : X => point) := by
    apply productRemainder.congr_left
    intro point
    simp only [map_zero, zero_smul, sub_zero,
      ContinuousLinearMap.smulRight_apply, smul_sub]
  apply HasFDerivAt.of_isLittleO
  simpa only [sub_zero] using derivativeRemainder

private theorem linear_smul_zeroField_continuousAt_fderiv_zero
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    {domain : Set X}
    {A : ℝ≥0}
    (domainOpen : IsOpen domain)
    (zero_mem : (0 : X) ∈ domain)
    (fieldLipschitz : LipschitzOnWith A field domain)
    (fieldZero : field 0 = 0) :
    ContinuousAt (fderiv ℝ (fun point => L point • field point)) 0 := by
  have domain_nhd : domain ∈ 𝓝 (0 : X) :=
    domainOpen.mem_nhds zero_mem
  have fieldContinuous : ContinuousAt field 0 :=
    fieldLipschitz.continuousOn.continuousAt domain_nhd
  have derivativeZero :
      fderiv ℝ (fun point => L point • field point) 0 =
        (0 : X →L[ℝ] E) := by
    have generated :=
      clm_smul_continuousAt_hasFDerivAt_zero L field fieldContinuous
    simpa [fieldZero] using generated.fderiv
  let control : X → ℝ := fun point =>
    3 * ‖L‖ * (A : ℝ) * ‖point‖
  have controlTends : Tendsto control (𝓝 (0 : X)) (𝓝 0) := by
    have normTends :
        Tendsto (fun point : X => ‖point‖) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, id_eq, norm_zero] using
        (continuousAt_id.norm :
          ContinuousAt (fun point : X => ‖point‖) 0)
    simpa [control] using
      (((tendsto_const_nhds.mul tendsto_const_nhds).mul
        tendsto_const_nhds).mul normTends)
  have derivativeBound :
      ∀ᶠ point in 𝓝 (0 : X),
        ‖fderiv ℝ (fun candidate => L candidate • field candidate) point‖ ≤
          control point := by
    filter_upwards [domain_nhd] with point point_mem
    by_cases pointZero : point = 0
    · subst point
      rw [derivativeZero]
      simp [control]
    · have pointNormPos : 0 < ‖point‖ := norm_pos_iff.mpr pointZero
      have normEventually :
          ∀ᶠ candidate in 𝓝 point,
            ‖candidate‖ < 2 * ‖point‖ := by
        filter_upwards [Metric.ball_mem_nhds point pointNormPos] with
            candidate candidate_mem
        rw [Metric.mem_ball, dist_eq_norm] at candidate_mem
        calc
          ‖candidate‖ = ‖(candidate - point) + point‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖candidate - point‖ + ‖point‖ := norm_add_le _ _
          _ < ‖point‖ + ‖point‖ :=
            add_lt_add_left candidate_mem ‖point‖
          _ = 2 * ‖point‖ := by ring
      have pointDomainNhd : domain ∈ 𝓝 point :=
        domainOpen.mem_nhds point_mem
      apply norm_fderiv_le_of_lip' ℝ
      · dsimp [control]
        positivity
      · filter_upwards [normEventually, pointDomainNhd] with
          candidate candidateNorm candidate_mem
        have timeCandidate :
            |L candidate| ≤ ‖L‖ * (2 * ‖point‖) := by
          calc
            |L candidate| = ‖L candidate‖ := by rw [Real.norm_eq_abs]
            _ ≤ ‖L‖ * ‖candidate‖ := L.le_opNorm candidate
            _ ≤ ‖L‖ * (2 * ‖point‖) :=
              mul_le_mul_of_nonneg_left candidateNorm.le (norm_nonneg _)
        have timeDifference :
            |L candidate - L point| ≤
              ‖L‖ * ‖candidate - point‖ := by
          rw [← map_sub, ← Real.norm_eq_abs]
          exact L.le_opNorm (candidate - point)
        have fieldDifference :
            ‖field candidate - field point‖ ≤
              (A : ℝ) * ‖candidate - point‖ :=
          fieldLipschitz.norm_sub_le candidate_mem point_mem
        have fieldPointNorm :
            ‖field point‖ ≤ (A : ℝ) * ‖point‖ := by
          have generated := fieldLipschitz.norm_sub_le point_mem zero_mem
          simpa [fieldZero] using generated
        have decomposition :
            L candidate • field candidate - L point • field point =
              L candidate • (field candidate - field point) +
                (L candidate - L point) • field point := by
          module
        rw [decomposition]
        calc
          ‖L candidate • (field candidate - field point) +
              (L candidate - L point) • field point‖
              ≤ ‖L candidate • (field candidate - field point)‖ +
                ‖(L candidate - L point) • field point‖ :=
            norm_add_le _ _
          _ = |L candidate| * ‖field candidate - field point‖ +
                |L candidate - L point| * ‖field point‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
          _ ≤ (‖L‖ * (2 * ‖point‖)) *
                  ((A : ℝ) * ‖candidate - point‖) +
                (‖L‖ * ‖candidate - point‖) *
                  ((A : ℝ) * ‖point‖) := by
            gcongr
          _ = control point * ‖candidate - point‖ := by
            dsimp [control]
            ring
  rw [ContinuousAt, derivativeZero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero'
    (Eventually.of_forall fun point => norm_nonneg _)
    derivativeBound controlTends

private theorem normalizedFirstAverage_exists_local_lipschitzOnWith
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ∃ A : ℝ≥0, ∃ domain : Set BasePoint,
      IsOpen domain ∧
        (0 : BasePoint) ∈ domain ∧
          LipschitzOnWith A (normalizedFirstAverage profile) domain := by
  obtain ⟨K, target, targetNhd, profileLipschitz⟩ :=
    regular.exists_lipschitzOnWith
  obtain ⟨epsilon, epsilon_pos, ballSubset⟩ :=
    Metric.mem_nhds_iff.mp targetNhd
  let radius : ℝ := epsilon / normalizedCanonicalTimeSliceBound
  have radius_pos : 0 < radius :=
    div_pos epsilon_pos normalizedCanonicalTimeSliceBound_pos
  let domain : Set BasePoint := Metric.ball 0 radius
  have domainOpen : IsOpen domain := Metric.isOpen_ball
  have zero_mem : (0 : BasePoint) ∈ domain :=
    Metric.mem_ball_self radius_pos
  have mapsTo :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          normalizedCanonicalTimeSliceCLM parameter point ∈ target := by
    intro point point_mem parameter parameter_mem
    have point_norm_lt : ‖point‖ < radius := by
      simpa [domain, Metric.mem_ball, dist_eq_norm] using point_mem
    apply ballSubset
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖normalizedCanonicalTimeSliceCLM parameter point‖
          ≤ ‖normalizedCanonicalTimeSliceCLM parameter‖ * ‖point‖ :=
        (normalizedCanonicalTimeSliceCLM parameter).le_opNorm point
      _ ≤ normalizedCanonicalTimeSliceBound * ‖point‖ :=
        mul_le_mul_of_nonneg_right
          (normalizedCanonicalTimeSliceCLM_norm_lt_bound parameter_mem).le
          (norm_nonneg _)
      _ < normalizedCanonicalTimeSliceBound * radius :=
        mul_lt_mul_of_pos_left point_norm_lt
          normalizedCanonicalTimeSliceBound_pos
      _ = epsilon := by
        dsimp [radius]
        field_simp [normalizedCanonicalTimeSliceBound_pos.ne']
  refine
    ⟨K * ⟨normalizedCanonicalTimeSliceBound,
        normalizedCanonicalTimeSliceBound_pos.le⟩,
      domain, domainOpen, zero_mem, ?_⟩
  exact normalizedFirstAverage_lipschitzOnWith profileLipschitz mapsTo

theorem canonicalTimePrimitive_continuousAt_fderiv_zero_of_contDiffAt_of_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0)
    (profileZero : profile 0 = 0) :
    ContinuousAt (fderiv ℝ (canonicalTimePrimitive profile)) 0 := by
  obtain ⟨A, domain, domainOpen, zero_mem, averageLipschitz⟩ :=
    normalizedFirstAverage_exists_local_lipschitzOnWith profile regular
  have averageZero : normalizedFirstAverage profile 0 = 0 := by
    unfold normalizedFirstAverage
    simp [profileZero]
  have generated :=
    linear_smul_zeroField_continuousAt_fderiv_zero
      canonicalTimeProjection (normalizedFirstAverage profile)
      domainOpen zero_mem averageLipschitz averageZero
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point • normalizedFirstAverage profile point) =
        canonicalTimePrimitive profile := by
    funext point
    exact (canonicalTimePrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

private theorem normalizedFirstAverage_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ContDiffAt ℝ 1 (normalizedFirstAverage profile) 0 := by
  obtain
      ⟨profileDerivative, derivativeTarget, derivativeTargetNhd,
        derivativeContinuous, derivativeAt⟩ :=
    contDiffAt_one_iff.mp regular
  obtain ⟨K, lipschitzTarget, lipschitzTargetNhd, profileLipschitz⟩ :=
    regular.exists_lipschitzOnWith
  have combinedTargetNhd :
      derivativeTarget ∩ lipschitzTarget ∈ 𝓝 (0 : BasePoint) :=
    inter_mem derivativeTargetNhd lipschitzTargetNhd
  obtain ⟨epsilon, epsilon_pos, ballSubset⟩ :=
    Metric.mem_nhds_iff.mp combinedTargetNhd
  let radius : ℝ := epsilon / normalizedCanonicalTimeSliceBound
  have radius_pos : 0 < radius :=
    div_pos epsilon_pos normalizedCanonicalTimeSliceBound_pos
  let domain : Set BasePoint := Metric.ball 0 radius
  have domainOpen : IsOpen domain := Metric.isOpen_ball
  have zero_mem : (0 : BasePoint) ∈ domain :=
    Metric.mem_ball_self radius_pos
  have mapsToBall :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          normalizedCanonicalTimeSliceCLM parameter point ∈
            Metric.ball 0 epsilon := by
    intro point point_mem parameter parameter_mem
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have point_norm_lt : ‖point‖ < radius := by
      simpa [domain, Metric.mem_ball, dist_eq_norm] using point_mem
    calc
      ‖normalizedCanonicalTimeSliceCLM parameter point‖
          ≤ ‖normalizedCanonicalTimeSliceCLM parameter‖ * ‖point‖ :=
        (normalizedCanonicalTimeSliceCLM parameter).le_opNorm point
      _ ≤ normalizedCanonicalTimeSliceBound * ‖point‖ :=
        mul_le_mul_of_nonneg_right
          (normalizedCanonicalTimeSliceCLM_norm_lt_bound parameter_mem).le
          (norm_nonneg _)
      _ < normalizedCanonicalTimeSliceBound * radius :=
        mul_lt_mul_of_pos_left point_norm_lt
          normalizedCanonicalTimeSliceBound_pos
      _ = epsilon := by
        dsimp [radius]
        field_simp [normalizedCanonicalTimeSliceBound_pos.ne']
  have mapsToCombined :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          normalizedCanonicalTimeSliceCLM parameter point ∈
            derivativeTarget ∩ lipschitzTarget := by
    intro point point_mem parameter parameter_mem
    exact ballSubset (mapsToBall point point_mem parameter parameter_mem)
  have sliceContinuous (point : BasePoint) :
      Continuous fun parameter : ℝ =>
        normalizedCanonicalTimeSliceCLM parameter point := by
    unfold normalizedCanonicalTimeSliceCLM
    fun_prop
  have sliceCLMContinuous :
      Continuous normalizedCanonicalTimeSliceCLM := by
    unfold normalizedCanonicalTimeSliceCLM
    fun_prop
  have functionIntervalIntegrable
      (point : BasePoint) (point_mem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter : ℝ =>
          profile (normalizedCanonicalTimeSliceCLM parameter point))
        MeasureTheory.volume 0 1 := by
    have composed :
        ContinuousOn
          (fun parameter : ℝ =>
            profile (normalizedCanonicalTimeSliceCLM parameter point))
          (Icc (0 : ℝ) 1) :=
      profileLipschitz.continuousOn.comp
        (sliceContinuous point).continuousOn
        (fun parameter parameter_mem =>
          (mapsToCombined point point_mem parameter parameter_mem).2)
    exact composed.intervalIntegrable_of_Icc (by norm_num)
  let B : ℝ≥0 :=
    ⟨normalizedCanonicalTimeSliceBound,
      normalizedCanonicalTimeSliceBound_pos.le⟩
  have B_coe : (B : ℝ) = normalizedCanonicalTimeSliceBound := rfl
  let averageDerivative : BasePoint → BasePoint →L[ℝ] E := fun point =>
    ∫ parameter in (0 : ℝ)..1,
      (profileDerivative
          (normalizedCanonicalTimeSliceCLM parameter point)).comp
        (normalizedCanonicalTimeSliceCLM parameter)
  let bound : ℝ → ℝ := fun _ => ((K * B : ℝ≥0) : ℝ)
  have boundIntegrable :
      IntervalIntegrable bound MeasureTheory.volume 0 1 := by
    exact intervalIntegrable_const
  have derivativeIntervalIntegrable
      (point : BasePoint) (point_mem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter : ℝ =>
          (profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter point)).comp
            (normalizedCanonicalTimeSliceCLM parameter))
        MeasureTheory.volume 0 1 := by
    have derivativeAlongSlice :
        ContinuousOn
          (fun parameter : ℝ =>
            profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter point))
          (Icc (0 : ℝ) 1) :=
      derivativeContinuous.comp
        (sliceContinuous point).continuousOn
        (fun parameter parameter_mem =>
          (mapsToCombined point point_mem parameter parameter_mem).1)
    have composed :
        ContinuousOn
          (fun parameter : ℝ =>
            (profileDerivative
                (normalizedCanonicalTimeSliceCLM parameter point)).comp
              (normalizedCanonicalTimeSliceCLM parameter))
          (Icc (0 : ℝ) 1) :=
      derivativeAlongSlice.clm_comp sliceCLMContinuous.continuousOn
    exact composed.intervalIntegrable_of_Icc (by norm_num)
  have averageHasFDerivAt :
      ∀ point ∈ domain,
        HasFDerivAt (normalizedFirstAverage profile)
          (averageDerivative point) point := by
    intro point point_mem
    have pointDomainNhd : domain ∈ 𝓝 point :=
      domainOpen.mem_nhds point_mem
    have functionMeasurable :
        ∀ᶠ candidate in 𝓝 point,
          AEStronglyMeasurable
            (fun parameter : ℝ =>
              profile
                (normalizedCanonicalTimeSliceCLM parameter candidate))
            (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
      filter_upwards [pointDomainNhd] with candidate candidate_mem
      exact
        (functionIntervalIntegrable candidate candidate_mem).def'
          |>.aestronglyMeasurable
    have derivativeMeasurable :
        AEStronglyMeasurable
          (fun parameter : ℝ =>
            (profileDerivative
                (normalizedCanonicalTimeSliceCLM parameter point)).comp
              (normalizedCanonicalTimeSliceCLM parameter))
          (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) :=
      (derivativeIntervalIntegrable point point_mem).def'
        |>.aestronglyMeasurable
    have integrandLipschitz :
        ∀ᵐ parameter ∂MeasureTheory.volume,
          parameter ∈ Ι (0 : ℝ) 1 →
            LipschitzOnWith (Real.nnabs (bound parameter))
              (fun candidate : BasePoint =>
                profile
                  (normalizedCanonicalTimeSliceCLM parameter candidate))
              domain := by
      filter_upwards [] with parameter parameter_mem
      have parameter_mem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameter_mem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      have generated :
          LipschitzOnWith (K * B)
            (fun candidate : BasePoint =>
              profile
                (normalizedCanonicalTimeSliceCLM parameter candidate))
            domain := by
        apply LipschitzOnWith.of_dist_le_mul
        intro first first_mem second second_mem
        rw [dist_eq_norm]
        calc
          ‖profile (normalizedCanonicalTimeSliceCLM parameter first) -
              profile (normalizedCanonicalTimeSliceCLM parameter second)‖
              ≤ (K : ℝ) *
                  ‖normalizedCanonicalTimeSliceCLM parameter first -
                    normalizedCanonicalTimeSliceCLM parameter second‖ :=
            profileLipschitz.norm_sub_le
              (mapsToCombined first first_mem parameter parameter_mem').2
              (mapsToCombined second second_mem parameter parameter_mem').2
          _ = (K : ℝ) *
                ‖normalizedCanonicalTimeSliceCLM parameter
                  (first - second)‖ := by
            rw [map_sub]
          _ ≤ (K : ℝ) *
                (normalizedCanonicalTimeSliceBound * ‖first - second‖) := by
            apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
            exact
              (normalizedCanonicalTimeSliceCLM parameter).le_opNorm
                  (first - second)
                |>.trans
                  (mul_le_mul_of_nonneg_right
                    (normalizedCanonicalTimeSliceCLM_norm_lt_bound
                      parameter_mem').le
                    (norm_nonneg _))
          _ = ((K * B : ℝ≥0) : ℝ) * ‖first - second‖ := by
            rw [NNReal.coe_mul, B_coe]
            ring
      simpa [bound] using generated
    have integrandDerivative :
        ∀ᵐ parameter ∂MeasureTheory.volume,
          parameter ∈ Ι (0 : ℝ) 1 →
            HasFDerivAt
              (fun candidate : BasePoint =>
                profile
                  (normalizedCanonicalTimeSliceCLM parameter candidate))
              ((profileDerivative
                  (normalizedCanonicalTimeSliceCLM parameter point)).comp
                (normalizedCanonicalTimeSliceCLM parameter))
              point := by
      filter_upwards [] with parameter parameter_mem
      have parameter_mem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameter_mem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      exact
        (derivativeAt
            (normalizedCanonicalTimeSliceCLM parameter point)
            (mapsToCombined point point_mem parameter parameter_mem').1).comp
          point (normalizedCanonicalTimeSliceCLM parameter).hasFDerivAt
    have generated :=
      intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
        (μ := MeasureTheory.volume)
        (s := domain)
        (a := (0 : ℝ))
        (b := (1 : ℝ))
        (F := fun candidate parameter =>
          profile (normalizedCanonicalTimeSliceCLM parameter candidate))
        (F' := fun parameter =>
          (profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter point)).comp
            (normalizedCanonicalTimeSliceCLM parameter))
        (bound := bound)
        pointDomainNhd functionMeasurable
        (functionIntervalIntegrable point point_mem)
        derivativeMeasurable integrandLipschitz boundIntegrable
        integrandDerivative
    exact generated.2
  have averageDerivativeContinuous :
      ContinuousOn averageDerivative domain := by
    intro point point_mem
    have derivativeMeasurable :
        ∀ᶠ candidate in 𝓝[domain] point,
          AEStronglyMeasurable
            (fun parameter : ℝ =>
              (profileDerivative
                  (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
                (normalizedCanonicalTimeSliceCLM parameter))
            (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
      filter_upwards [self_mem_nhdsWithin] with candidate candidate_mem
      exact
        (derivativeIntervalIntegrable candidate candidate_mem).def'
          |>.aestronglyMeasurable
    have derivativeBound :
        ∀ᶠ candidate in 𝓝[domain] point,
          ∀ᵐ parameter ∂MeasureTheory.volume,
            parameter ∈ Ι (0 : ℝ) 1 →
              ‖(profileDerivative
                    (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
                  (normalizedCanonicalTimeSliceCLM parameter)‖ ≤
                bound parameter := by
      filter_upwards [self_mem_nhdsWithin] with candidate candidate_mem
      filter_upwards [] with parameter parameter_mem
      have parameter_mem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameter_mem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      have slice_mem_ball :=
        mapsToBall candidate candidate_mem parameter parameter_mem'
      have slice_mem_combined :=
        mapsToCombined candidate candidate_mem parameter parameter_mem'
      have profileDerivativeNorm :
          ‖profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter candidate)‖ ≤
            (K : ℝ) := by
        rw [← (derivativeAt
          (normalizedCanonicalTimeSliceCLM parameter candidate)
          slice_mem_combined.1).fderiv]
        exact
          norm_fderiv_le_of_lipschitzOn ℝ
            (Metric.isOpen_ball.mem_nhds slice_mem_ball)
            (profileLipschitz.mono
              (ballSubset.trans inter_subset_right))
      calc
        ‖(profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
            (normalizedCanonicalTimeSliceCLM parameter)‖
            ≤ ‖profileDerivative
                (normalizedCanonicalTimeSliceCLM parameter candidate)‖ *
              ‖normalizedCanonicalTimeSliceCLM parameter‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * normalizedCanonicalTimeSliceBound := by
          gcongr
          exact
            (normalizedCanonicalTimeSliceCLM_norm_lt_bound
              parameter_mem').le
        _ = bound parameter := by
          simp [bound, NNReal.coe_mul, B_coe]
    have derivativeContinuousAt :
        ∀ᵐ parameter ∂MeasureTheory.volume,
          parameter ∈ Ι (0 : ℝ) 1 →
            ContinuousWithinAt
              (fun candidate : BasePoint =>
                (profileDerivative
                    (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
                  (normalizedCanonicalTimeSliceCLM parameter))
              domain point := by
      filter_upwards [] with parameter parameter_mem
      have parameter_mem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameter_mem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      have derivativeAlongDomain :
          ContinuousOn
            (fun candidate : BasePoint =>
              profileDerivative
                (normalizedCanonicalTimeSliceCLM parameter candidate))
            domain :=
        derivativeContinuous.comp
          (normalizedCanonicalTimeSliceCLM parameter).continuous.continuousOn
          (fun candidate candidate_mem =>
            (mapsToCombined candidate candidate_mem parameter parameter_mem').1)
      have composed :
          ContinuousOn
            (fun candidate : BasePoint =>
              (profileDerivative
                  (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
                (normalizedCanonicalTimeSliceCLM parameter))
            domain :=
        derivativeAlongDomain.clm_comp continuousOn_const
      exact composed point point_mem
    change ContinuousWithinAt
      (fun candidate =>
        ∫ parameter in (0 : ℝ)..1,
          (profileDerivative
              (normalizedCanonicalTimeSliceCLM parameter candidate)).comp
            (normalizedCanonicalTimeSliceCLM parameter))
      domain point
    exact
      intervalIntegral.continuousWithinAt_of_dominated_interval
        (μ := MeasureTheory.volume)
        derivativeMeasurable derivativeBound boundIntegrable
        derivativeContinuousAt
  exact contDiffAt_one_iff.mpr
    ⟨averageDerivative, domain, domainOpen.mem_nhds zero_mem,
      averageDerivativeContinuous, averageHasFDerivAt⟩

private theorem normalizedFirstAverage_eventually_differentiableAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ∀ᶠ point in 𝓝 (0 : BasePoint),
      DifferentiableAt ℝ (normalizedFirstAverage profile) point := by
  filter_upwards
      [(normalizedFirstAverage_contDiffAt profile regular).eventually
        (by simp)] with point pointRegular
  exact pointRegular.differentiableAt (by norm_num)

/-- A locally `C¹` action profile generates a locally `C¹` canonical first
primitive in the full ambient spacetime carrier.  This is the reusable
regularity seam for a generated temporal write that becomes the current of a
later action leg. -/
theorem canonicalTimePrimitive_contDiffAt_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ContDiffAt ℝ 1 (canonicalTimePrimitive profile) 0 := by
  have generated :=
    canonicalTimeProjection.contDiff.contDiffAt.smul
      (normalizedFirstAverage_contDiffAt profile regular)
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point • normalizedFirstAverage profile point) =
        canonicalTimePrimitive profile := by
    funext point
    exact (canonicalTimePrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

/-- Canonical temporal integration commutes with recentering at a point on
the distinguished zero slice.  The statement preserves the full spatial
occurrence instead of identifying equal coarse values at different points. -/
theorem
    canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint) :
    canonicalTimePrimitive profile ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) =
      canonicalTimePrimitive
        (profile ∘ canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) := by
  funext point
  unfold canonicalTimePrimitive Function.comp
  simp only
  have timeProjectionTranslation :
      canonicalTimeProjection
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) point) =
      canonicalTimeProjection point := by
    simp [canonicalSpacetimeContactTranslation,
      canonicalTimeProjection, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]
  rw [timeProjectionTranslation]
  apply intervalIntegral.integral_congr
  intro time _
  apply congrArg profile
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpacetimeContactTranslation,
      canonicalSpatialProjection, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- A locally `C¹` action profile makes its canonical first primitive
differentiable at every point in a neighborhood of the common occurrence.
Together with
`canonicalTimePrimitive_continuousAt_fderiv_zero_of_contDiffAt_of_eq_zero`,
this supplies the exact first-jet regularity needed when the generated
primitive becomes the input to a later action leg. -/
theorem canonicalTimePrimitive_eventually_differentiableAt_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ∀ᶠ point in 𝓝 (0 : BasePoint),
      DifferentiableAt ℝ (canonicalTimePrimitive profile) point := by
  filter_upwards
      [normalizedFirstAverage_eventually_differentiableAt profile regular]
      with point averageDifferentiable
  have generated :=
    canonicalTimeProjection.differentiableAt.smul averageDifferentiable
  have primitiveEq :
      (fun candidate =>
        canonicalTimeProjection candidate •
          normalizedFirstAverage profile candidate) =
        canonicalTimePrimitive profile := by
    funext candidate
    exact (canonicalTimePrimitive_scaleIdentity profile candidate).symm
  rw [← primitiveEq]
  exact generated

private theorem linear_smul_lipschitz_continuousAt_fderiv
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    {domain : Set X}
    {A : ℝ≥0}
    (domainOpen : IsOpen domain)
    (zero_mem : (0 : X) ∈ domain)
    (fieldLipschitz : LipschitzOnWith A field domain)
    (fieldEventuallyDifferentiable :
      ∀ᶠ point in 𝓝 (0 : X), DifferentiableAt ℝ field point) :
    ContinuousAt (fderiv ℝ (fun point => L point • field point)) 0 := by
  have domain_nhd : domain ∈ 𝓝 (0 : X) :=
    domainOpen.mem_nhds zero_mem
  have fieldContinuous : ContinuousAt field 0 :=
    fieldLipschitz.continuousOn.continuousAt domain_nhd
  have derivativeZero :
      fderiv ℝ (fun point => L point • field point) 0 =
        L.smulRight (field 0) :=
    (clm_smul_continuousAt_hasFDerivAt_zero
      L field fieldContinuous).fderiv
  have fieldDerivativeBound :
      ∀ᶠ point in 𝓝 (0 : X), ‖fderiv ℝ field point‖ ≤ (A : ℝ) := by
    filter_upwards [domain_nhd] with point point_mem
    exact
      norm_fderiv_le_of_lipschitzOn ℝ
        (domainOpen.mem_nhds point_mem) fieldLipschitz
  let control : X → ℝ := fun point =>
    ‖L‖ * ‖point‖ * (A : ℝ)
  have controlTends : Tendsto control (𝓝 (0 : X)) (𝓝 0) := by
    have normTends :
        Tendsto (fun point : X => ‖point‖) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, id_eq, norm_zero] using
        (continuousAt_id.norm :
          ContinuousAt (fun point : X => ‖point‖) 0)
    simpa [control] using
      ((tendsto_const_nhds.mul normTends).mul tendsto_const_nhds)
  have timeDerivativeTermBound :
      ∀ᶠ point in 𝓝 (0 : X),
        ‖L point • fderiv ℝ field point‖ ≤ control point := by
    filter_upwards [fieldDerivativeBound] with point derivativeBound
    calc
      ‖L point • fderiv ℝ field point‖
          = |L point| * ‖fderiv ℝ field point‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖L‖ * ‖point‖) * (A : ℝ) := by
        gcongr
        · rw [← Real.norm_eq_abs]
          exact L.le_opNorm point
      _ = control point := rfl
  have timeDerivativeTermTends :
      Tendsto
        (fun point : X => L point • fderiv ℝ field point)
        (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Eventually.of_forall fun point => norm_nonneg _)
      timeDerivativeTermBound controlTends
  have valueTermTends :
      Tendsto
        (fun point : X => L.smulRight (field point))
        (𝓝 0) (𝓝 (L.smulRight (field 0))) := by
    exact
      (ContinuousLinearMap.smulRightL ℝ X E L).continuous.continuousAt
        |>.tendsto.comp fieldContinuous
  have candidateTends :
      Tendsto
        (fun point : X =>
          L point • fderiv ℝ field point + L.smulRight (field point))
        (𝓝 0) (𝓝 (L.smulRight (field 0))) := by
    simpa using timeDerivativeTermTends.add valueTermTends
  have derivativeEventuallyEq :
      (fun point : X =>
        fderiv ℝ (fun candidate => L candidate • field candidate) point) =ᶠ[𝓝 0]
      (fun point : X =>
        L point • fderiv ℝ field point + L.smulRight (field point)) := by
    filter_upwards [fieldEventuallyDifferentiable] with point differentiable
    have generated :=
      L.hasFDerivAt.smul differentiable.hasFDerivAt
    exact generated.fderiv
  rw [ContinuousAt, derivativeZero]
  exact candidateTends.congr' derivativeEventuallyEq.symm

/-- The canonical first primitive of a locally `C¹` profile has a continuous
full ambient first derivative at the common occurrence.  No zero-value
assumption is needed: the normalized average controls the value term, while
the time coordinate suppresses its uniformly bounded derivative term. -/
theorem canonicalTimePrimitive_continuousAt_fderiv_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ContinuousAt (fderiv ℝ (canonicalTimePrimitive profile)) 0 := by
  obtain ⟨A, domain, domainOpen, zero_mem, averageLipschitz⟩ :=
    normalizedFirstAverage_exists_local_lipschitzOnWith profile regular
  have averageEventuallyDifferentiable :=
    normalizedFirstAverage_eventually_differentiableAt profile regular
  have generated :=
    linear_smul_lipschitz_continuousAt_fderiv
      canonicalTimeProjection (normalizedFirstAverage profile)
      domainOpen zero_mem averageLipschitz averageEventuallyDifferentiable
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point • normalizedFirstAverage profile point) =
        canonicalTimePrimitive profile := by
    funext point
    exact (canonicalTimePrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
