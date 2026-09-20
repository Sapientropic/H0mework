import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.Physics.JointVariation.GeneratedProfiles
import H0mework.Physics.GaugeAction.P286ActionConnectionVelocity

/-!
# Global temporal development of the complete joint action

The complete-joint occurrence profile supplies action-generated matter and
adjoint velocities together with the scalar acceleration.  A local contact
germ preserves its origin value, so a family of such germs cannot be glued by
declaring every origin value to be the old field value.  This module instead
uses the canonical Cauchy foliation and its fixed zero slice to integrate the
generated response into one four-dimensional field.

The operator consumes only `(source,current)`.  Its integration base, time
axis, and subtraction of the current raw velocity are canonical; no residual,
support coordinate, target field, branch, boundary parameter, or equation
receipt is accepted.  P286 and gravity integrability remain separate
action-owned coordinates of the eventual common write and are not fabricated
here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineJointActionCanonicalPhasePathLaw
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open Filter Asymptotics MeasureTheory Set
open scoped Interval Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- `HasDerivAt` with the additive, scalar, and topology structures inherited
from one normed-space instance.  This avoids the non-definitional `PiLp`
instance diamond while retaining the standard calculus proposition. -/
abbrev NormedHasDerivAt
    {E : Type*}
    [group : NormedAddCommGroup E]
    [space : NormedSpace ℝ E]
    [smul : ContinuousSMul ℝ E]
    (field : ℝ → E)
    (derivative : E)
    (point : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance E group.toAddCommGroup space.toModule
    group.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    smul field derivative point

/-! ## Canonical source-free time primitives -/

/-- Integrate a spacetime profile along the canonical time line through the
point's own spatial coordinate, anchored at the distinguished zero slice. -/
def canonicalTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) : E :=
  ∫ time in (0 : ℝ)..canonicalTimeProjection point,
    profile
      (canonicalCauchySlicePoint time (canonicalSpatialProjection point))

/-- The twice-integrated profile used by a second-order scalar action. -/
def canonicalTimeSecondPrimitive
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) : E :=
  ∫ outerTime in (0 : ℝ)..canonicalTimeProjection point,
    ∫ innerTime in (0 : ℝ)..outerTime,
      profile
        (canonicalCauchySlicePoint innerTime
          (canonicalSpatialProjection point))

@[simp] theorem canonicalTimePrimitive_zeroSlice
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint) :
    canonicalTimePrimitive profile (canonicalCauchySlicePoint 0 space) = 0 := by
  simp [canonicalTimePrimitive]

@[simp] theorem canonicalTimeSecondPrimitive_zeroSlice
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint) :
    canonicalTimeSecondPrimitive profile
        (canonicalCauchySlicePoint 0 space) =
      0 := by
  simp [canonicalTimeSecondPrimitive]

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

/-- A continuous spacetime response has the expected ambient derivative at
the canonical zero slice after source-free temporal integration.  The proof
keeps both the time and spatial dependence of the response: it rewrites the
primitive as the time projection multiplied by a jointly continuous
unit-interval average.

This is an analytic readout of the already generated primitive.  It does not
add a boundary value, response profile, or differentiability receipt to the
producer. -/
theorem canonicalTimePrimitive_hasFDerivAt_zero_of_continuous
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (continuous : Continuous profile) :
    HasFDerivAt (canonicalTimePrimitive profile)
      (canonicalTimeProjection.smulRight (profile 0)) 0 := by
  let normalizedProfile : BasePoint → ℝ → E := fun point parameter =>
    profile
      (canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point))
  let average : BasePoint → E := fun point =>
    ∫ parameter in (0 : ℝ)..1, normalizedProfile point parameter
  have timeSingle (time : ℝ) :
      EuclideanSpace.single canonicalLorentzianTimeDirection time =
        time • coordinateDirection canonicalLorentzianTimeDirection := by
    ext direction
    fin_cases direction <;>
      simp [coordinateDirection, canonicalLorentzianTimeDirection]
  have normalizedProfileContinuous :
      Continuous normalizedProfile.uncurry := by
    dsimp [normalizedProfile, Function.uncurry]
    apply continuous.comp
    have sliceForm :
      (fun point : BasePoint × ℝ =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection point.1 * point.2)
          (canonicalSpatialProjection point.1)) =
        fun point =>
          (canonicalTimeProjection point.1 * point.2) •
              coordinateDirection canonicalLorentzianTimeDirection +
            canonicalSpatialInclusion
              (canonicalSpatialProjection point.1) := by
      funext point
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion, timeSingle]
    rw [sliceForm]
    exact
      (((canonicalTimeProjection.continuous.comp continuous_fst).mul
          continuous_snd).smul continuous_const).add
        (canonicalSpatialInclusion.continuous.comp
          (canonicalSpatialProjection.continuous.comp continuous_fst))
  have averageContinuous : Continuous average := by
    simpa [average] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) normalizedProfileContinuous 0 1)
  have averageZero : average 0 = profile 0 := by
    have sliceZero :
        canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint,
          canonicalLorentzianTimeDirection, Fin.sum_univ_three]
    simp [average, normalizedProfile, sliceZero]
  have scaleIdentity (point : BasePoint) :
      canonicalTimePrimitive profile point =
        canonicalTimeProjection point • average point := by
    simpa [canonicalTimePrimitive, average, normalizedProfile] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun time =>
          profile
            (canonicalCauchySlicePoint time
              (canonicalSpatialProjection point)))
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (canonicalTimeProjection point)).symm
  have generated :=
    clm_smul_continuousAt_hasFDerivAt_zero
      canonicalTimeProjection average averageContinuous.continuousAt
  have transported :=
    generated.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun point => scaleIdentity point)
  simpa [averageZero] using transported

private theorem normalizedCanonicalTimeSlice_tendsto_zero :
    Tendsto
      (fun joint : BasePoint × ℝ =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection joint.1 * joint.2)
          (canonicalSpatialProjection joint.1))
      (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
      (𝓝 0) := by
  have parameterBounded :
      IsBoundedUnder (· ≤ ·)
        (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
        (norm ∘ fun joint : BasePoint × ℝ => joint.2) := by
    have parameterIn :
        ∀ᶠ joint : BasePoint × ℝ in
            (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)),
          joint.2 ∈ Icc (0 : ℝ) 1 :=
      (tendsto_snd : Tendsto
        (fun joint : BasePoint × ℝ => joint.2)
        (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
        (𝓟 (Icc (0 : ℝ) 1))) (by simp)
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [parameterIn] with joint hjoint
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg hjoint.1] using hjoint.2
  have timeTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalTimeProjection joint.1)
        (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
        (𝓝 0) := by
    change Tendsto
      (canonicalTimeProjection ∘
        (fun joint : BasePoint × ℝ => joint.1))
      (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)) (𝓝 0)
    simpa only [map_zero] using
      canonicalTimeProjection.continuous.continuousAt.tendsto.comp
        (tendsto_fst :
          Tendsto (fun joint : BasePoint × ℝ => joint.1)
            (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)) (𝓝 0))
  have scaledTimeTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalTimeProjection joint.1 * joint.2)
        (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
        (𝓝 0) :=
    timeTends.zero_mul_isBoundedUnder_le parameterBounded
  have spaceTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalSpatialProjection joint.1)
        (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1))
        (𝓝 0) := by
    change Tendsto
      (canonicalSpatialProjection ∘
        (fun joint : BasePoint × ℝ => joint.1))
      (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)) (𝓝 0)
    simpa only [map_zero] using
      canonicalSpatialProjection.continuous.continuousAt.tendsto.comp
        (tendsto_fst :
          Tendsto (fun joint : BasePoint × ℝ => joint.1)
            (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)) (𝓝 0))
  have timeSingle (time : ℝ) :
      EuclideanSpace.single canonicalLorentzianTimeDirection time =
        time • coordinateDirection canonicalLorentzianTimeDirection := by
    ext direction
    fin_cases direction <;>
      simp [coordinateDirection, canonicalLorentzianTimeDirection]
  have sliceForm :
      (fun joint : BasePoint × ℝ =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection joint.1 * joint.2)
          (canonicalSpatialProjection joint.1)) =
        fun joint =>
          (canonicalTimeProjection joint.1 * joint.2) •
              coordinateDirection canonicalLorentzianTimeDirection +
            canonicalSpatialInclusion
              (canonicalSpatialProjection joint.1) := by
    funext joint
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion, timeSingle]
  rw [sliceForm]
  simpa only [Function.comp_apply, map_zero, zero_smul, zero_add] using
    (scaledTimeTends.smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)).add
      (canonicalSpatialInclusion.continuous.continuousAt.tendsto.comp
        spaceTends)

/-- Local continuity on a neighborhood of the common occurrence is enough
to differentiate the canonical first primitive in the full ambient spacetime
carrier.

The proof rescales every shrinking time segment to the fixed unit interval.
The normalized slices approach the common occurrence uniformly in that
interval, so local regularity supplies both measurability and one integrable
dominating bound.  This is an analytic readout of an already generated
profile; no regularity certificate is accepted by the temporal producer. -/
theorem canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 0 profile 0) :
    HasFDerivAt (canonicalTimePrimitive profile)
      (canonicalTimeProjection.smulRight (profile 0)) 0 := by
  let normalizedProfile : BasePoint → ℝ → E := fun point parameter =>
    profile
      (canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point))
  let average : BasePoint → E := fun point =>
    ∫ parameter in (0 : ℝ)..1, normalizedProfile point parameter
  have sliceZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  have normalizedAtZero (parameter : ℝ) :
      normalizedProfile 0 parameter = profile 0 := by
    simp [normalizedProfile, sliceZero]
  have normalizedContinuousAt (parameter : ℝ) :
      ContinuousAt (fun point => normalizedProfile point parameter) 0 := by
    have innerContinuous :
        ContinuousAt
          (fun point : BasePoint =>
            canonicalCauchySlicePoint
              (canonicalTimeProjection point * parameter)
              (canonicalSpatialProjection point)) 0 := by
      have timeSingle (time : ℝ) :
          EuclideanSpace.single canonicalLorentzianTimeDirection time =
            time • coordinateDirection canonicalLorentzianTimeDirection := by
        ext direction
        fin_cases direction <;>
          simp [coordinateDirection, canonicalLorentzianTimeDirection]
      have sliceForm :
          (fun point : BasePoint =>
            canonicalCauchySlicePoint
              (canonicalTimeProjection point * parameter)
              (canonicalSpatialProjection point)) =
            fun point =>
              (canonicalTimeProjection point * parameter) •
                  coordinateDirection canonicalLorentzianTimeDirection +
                canonicalSpatialInclusion
                  (canonicalSpatialProjection point) := by
        funext point
        rw [canonicalCauchySlicePoint_eq_const_add_inclusion, timeSingle]
      rw [sliceForm]
      exact
        ((canonicalTimeProjection.continuous.continuousAt.mul
            continuousAt_const).smul continuousAt_const).add
          (canonicalSpatialInclusion.continuous.continuousAt.comp'
            canonicalSpatialProjection.continuous.continuousAt)
    change ContinuousAt
      (profile ∘ fun point : BasePoint =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection point * parameter)
          (canonicalSpatialProjection point)) 0
    have outer :
        ContinuousAt profile
          (canonicalCauchySlicePoint
            (canonicalTimeProjection (0 : BasePoint) * parameter)
            (canonicalSpatialProjection (0 : BasePoint))) := by
      simpa [sliceZero] using regular.continuousAt
    exact ContinuousAt.comp'
      (f := fun point : BasePoint =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection point * parameter)
          (canonicalSpatialProjection point))
      outer innerContinuous
  obtain ⟨localSet, localSetNhd, profileContinuousOn⟩ :=
    (contDiffAt_zero.mp (regular.of_le (by norm_num)))
  have normalizedEventuallyInLocal :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)),
        canonicalCauchySlicePoint
            (canonicalTimeProjection joint.1 * joint.2)
            (canonicalSpatialProjection joint.1) ∈
          localSet :=
    normalizedCanonicalTimeSlice_tendsto_zero.eventually localSetNhd
  obtain ⟨pointSet, pointSetNhd, parameterSet, parameterSetPrincipal,
      productSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyInLocal
  have intervalSubsetParameter : Icc (0 : ℝ) 1 ⊆ parameterSet := by
    simpa only [mem_principal] using parameterSetPrincipal
  have measurableEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        AEStronglyMeasurable (normalizedProfile point)
          (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [pointSetNhd] with point pointIn
    have continuousOn :
        ContinuousOn (normalizedProfile point) (Icc (0 : ℝ) 1) := by
      have innerContinuous :
          Continuous fun parameter : ℝ =>
            canonicalCauchySlicePoint
              (canonicalTimeProjection point * parameter)
              (canonicalSpatialProjection point) := by
        have timeSingle (time : ℝ) :
            EuclideanSpace.single canonicalLorentzianTimeDirection time =
              time • coordinateDirection canonicalLorentzianTimeDirection := by
          ext direction
          fin_cases direction <;>
            simp [coordinateDirection, canonicalLorentzianTimeDirection]
        have sliceForm :
            (fun parameter : ℝ =>
              canonicalCauchySlicePoint
                (canonicalTimeProjection point * parameter)
                (canonicalSpatialProjection point)) =
              fun parameter =>
                (canonicalTimeProjection point * parameter) •
                    coordinateDirection canonicalLorentzianTimeDirection +
                  canonicalSpatialInclusion
                    (canonicalSpatialProjection point) := by
          funext parameter
          rw [canonicalCauchySlicePoint_eq_const_add_inclusion, timeSingle]
        rw [sliceForm]
        exact
          ((continuous_const.mul continuous_id).smul
              continuous_const).add
            (canonicalSpatialInclusion.continuous.comp continuous_const)
      have composed :=
        profileContinuousOn.comp innerContinuous.continuousOn
          (fun parameter parameterIn => by
            have pairIn :
                (point, parameter) ∈ pointSet ×ˢ parameterSet :=
              ⟨pointIn, intervalSubsetParameter parameterIn⟩
            exact productSubset pairIn)
      simpa [normalizedProfile, Function.comp_def] using composed
    have intervalSubset :
        Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
      intro parameter parameterIn
      have actual := uIoc_subset_uIcc parameterIn
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    exact
      (continuousOn.mono intervalSubset).aestronglyMeasurable
        measurableSet_uIoc
  have profileNormBounded :
      IsBoundedUnder (· ≤ ·) (𝓝 (0 : BasePoint))
        (norm ∘ profile) :=
    regular.continuousAt.norm.isBoundedUnder_le
  obtain ⟨bound, profileEventuallyBounded⟩ :=
    profileNormBounded.eventually_le
  have normalizedEventuallyBounded :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Icc (0 : ℝ) 1)),
        ‖normalizedProfile joint.1 joint.2‖ ≤ bound := by
    exact normalizedCanonicalTimeSlice_tendsto_zero.eventually
      profileEventuallyBounded
  obtain ⟨boundPointSet, boundPointSetNhd, boundParameterSet,
      boundParameterPrincipal, boundProductSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyBounded
  have intervalSubsetBoundParameter : Icc (0 : ℝ) 1 ⊆
      boundParameterSet := by
    simpa only [mem_principal] using boundParameterPrincipal
  have boundEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        ∀ᵐ parameter ∂MeasureTheory.volume,
          parameter ∈ Ι (0 : ℝ) 1 →
            ‖normalizedProfile point parameter‖ ≤ bound := by
    filter_upwards [boundPointSetNhd] with point pointIn
    filter_upwards [] with parameter
    intro parameterIn
    have intervalMembership : parameter ∈ Icc (0 : ℝ) 1 := by
      have actual := uIoc_subset_uIcc parameterIn
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    have pairIn :
        (point, parameter) ∈ boundPointSet ×ˢ boundParameterSet :=
      ⟨pointIn, intervalSubsetBoundParameter intervalMembership⟩
    exact boundProductSubset pairIn
  have boundIntegrable :
      IntervalIntegrable (fun _ : ℝ => bound)
        MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have averageContinuous : ContinuousAt average 0 := by
    unfold average
    exact
      intervalIntegral.continuousAt_of_dominated_interval
        measurableEventually boundEventually boundIntegrable
        (MeasureTheory.ae_of_all _ fun parameter _ =>
          normalizedContinuousAt parameter)
  have averageZero : average 0 = profile 0 := by
    simp [average, normalizedAtZero]
  have scaleIdentity (point : BasePoint) :
      canonicalTimePrimitive profile point =
        canonicalTimeProjection point • average point := by
    simpa [canonicalTimePrimitive, average, normalizedProfile] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun time =>
          profile
            (canonicalCauchySlicePoint time
              (canonicalSpatialProjection point)))
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (canonicalTimeProjection point)).symm
  have generated :=
    clm_smul_continuousAt_hasFDerivAt_zero
      canonicalTimeProjection average averageContinuous
  have transported :=
    generated.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun point => scaleIdentity point)
  simpa [averageZero] using transported

/-- Backward-compatible `C¹` mouth for existing temporal producers. -/
theorem canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    HasFDerivAt (canonicalTimePrimitive profile)
      (canonicalTimeProjection.smulRight (profile 0)) 0 :=
  canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero profile
    (regular.of_le (by norm_num))

/-- Local fundamental theorem for the canonical first primitive on one
physical time line.

Unlike the global convenience theorem below, this mouth only asks for the
integration and endpoint data actually used by the FTC.  It is therefore the
right interface for a source-generated nondegenerate time domain. -/
theorem canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (integrable :
      IntervalIntegrable
        (fun candidateTime =>
          profile (canonicalCauchySlicePoint candidateTime space))
        MeasureTheory.volume 0 time)
    (measurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          profile (canonicalCauchySlicePoint candidateTime space))
        (nhds time) MeasureTheory.volume)
    (continuousAt :
      ContinuousAt
        (fun candidateTime =>
          profile (canonicalCauchySlicePoint candidateTime space))
        time) :
    HasDerivAt
      (fun candidateTime =>
        canonicalTimePrimitive profile
          (canonicalCauchySlicePoint candidateTime space))
      (profile (canonicalCauchySlicePoint time space))
      time := by
  simpa [canonicalTimePrimitive] using
    intervalIntegral.integral_hasDerivAt_right
      integrable measurableAt continuousAt

/-- Global-continuity convenience form of the canonical FTC. -/
theorem canonicalTimePrimitive_timeLine_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (continuous :
      Continuous fun candidateTime =>
        profile (canonicalCauchySlicePoint candidateTime space)) :
    HasDerivAt
      (fun candidateTime =>
        canonicalTimePrimitive profile
          (canonicalCauchySlicePoint candidateTime space))
      (profile (canonicalCauchySlicePoint time space))
      time :=
  canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
    profile space time
    (continuous.intervalIntegrable 0 time)
    (continuous.stronglyMeasurableAtFilter MeasureTheory.volume (nhds time))
    continuous.continuousAt

/-- The first derivative of the canonical second primitive is the canonical
first primitive of the same action profile. -/
theorem canonicalTimeSecondPrimitive_timeLine_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (continuous :
      Continuous fun candidateTime =>
        profile (canonicalCauchySlicePoint candidateTime space)) :
    HasDerivAt
      (fun candidateTime =>
        canonicalTimeSecondPrimitive profile
          (canonicalCauchySlicePoint candidateTime space))
      (canonicalTimePrimitive profile
        (canonicalCauchySlicePoint time space))
      time := by
  have innerContinuous :
      Continuous fun outerTime =>
        ∫ innerTime in (0 : ℝ)..outerTime,
          profile (canonicalCauchySlicePoint innerTime space) :=
    (intervalIntegral.differentiable_integral_of_continuous continuous
      ).continuous
  simpa [canonicalTimeSecondPrimitive, canonicalTimePrimitive] using
    (innerContinuous.integral_hasStrictDerivAt 0 time).hasDerivAt

/-- At the canonical zero slice, the twice-integrated profile has zero
temporal derivative without any regularity premise on the raw profile.

On each side of zero, either the profile is interval-integrable on some
nontrivial segment, in which case its first primitive is continuous there, or
no such segment exists, in which case the interval integral is definitionally
zero on that side.  Thus the first primitive is always continuous at the
common anchor and the outer fundamental theorem applies. -/
theorem canonicalTimeSecondPrimitive_timeLine_hasDerivAt_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint) :
    HasDerivAt
      (fun candidateTime =>
        canonicalTimeSecondPrimitive profile
          (canonicalCauchySlicePoint candidateTime space))
      0 0 := by
  let line : ℝ → E := fun time =>
    profile (canonicalCauchySlicePoint time space)
  let firstPrimitive : ℝ → E := fun time =>
    ∫ innerTime in (0 : ℝ)..time, line innerTime
  have firstPrimitiveContinuousNearZero :
      ∃ left right : ℝ,
        left < 0 ∧ 0 < right ∧
          ContinuousOn firstPrimitive (Set.Icc left right) := by
    by_cases leftIntegrable :
        ∃ left : ℝ,
          left < 0 ∧
            IntervalIntegrable line MeasureTheory.volume left 0
    · obtain ⟨left, leftNegative, lineIntegrableLeft⟩ :=
        leftIntegrable
      have continuousLeft :
          ContinuousOn firstPrimitive (Set.Icc left 0) := by
        have primitiveContinuous :=
          intervalIntegral.continuousOn_primitive_interval'
            lineIntegrableLeft (a := (0 : ℝ))
            Set.right_mem_uIcc
        simpa [firstPrimitive, Set.uIcc_of_le leftNegative.le] using
          primitiveContinuous
      by_cases rightIntegrable :
          ∃ right : ℝ,
            0 < right ∧
              IntervalIntegrable line MeasureTheory.volume 0 right
      · obtain ⟨right, rightPositive, lineIntegrableRight⟩ :=
          rightIntegrable
        have continuousRight :
            ContinuousOn firstPrimitive (Set.Icc 0 right) := by
          have primitiveContinuous :=
            intervalIntegral.continuousOn_primitive_interval'
              lineIntegrableRight (a := (0 : ℝ))
              Set.left_mem_uIcc
          simpa [firstPrimitive, Set.uIcc_of_le rightPositive.le] using
            primitiveContinuous
        refine ⟨left, right, leftNegative, rightPositive, ?_⟩
        rw [← Set.Icc_union_Icc_eq_Icc leftNegative.le rightPositive.le]
        exact continuousLeft.union_of_isClosed continuousRight
          isClosed_Icc isClosed_Icc
      · have continuousRight :
            ContinuousOn firstPrimitive (Set.Icc 0 1) := by
          apply (continuousOn_const (c := (0 : E))).congr
          intro time timeMem
          dsimp [firstPrimitive]
          by_cases timeZero : time = 0
          · simp [timeZero]
          · apply intervalIntegral.integral_undef
            intro intervalIntegrable
            exact rightIntegrable
              ⟨time, lt_of_le_of_ne timeMem.1 (Ne.symm timeZero),
                intervalIntegrable⟩
        refine ⟨left, 1, leftNegative, by norm_num, ?_⟩
        rw [← Set.Icc_union_Icc_eq_Icc leftNegative.le (by norm_num)]
        exact continuousLeft.union_of_isClosed continuousRight
          isClosed_Icc isClosed_Icc
    · have continuousLeft :
          ContinuousOn firstPrimitive (Set.Icc (-1) 0) := by
        apply (continuousOn_const (c := (0 : E))).congr
        intro time timeMem
        dsimp [firstPrimitive]
        by_cases timeZero : time = 0
        · simp [timeZero]
        · apply intervalIntegral.integral_undef
          intro intervalIntegrable
          exact leftIntegrable
            ⟨time, lt_of_le_of_ne timeMem.2 timeZero,
              intervalIntegrable.symm⟩
      by_cases rightIntegrable :
          ∃ right : ℝ,
            0 < right ∧
              IntervalIntegrable line MeasureTheory.volume 0 right
      · obtain ⟨right, rightPositive, lineIntegrableRight⟩ :=
          rightIntegrable
        have continuousRight :
            ContinuousOn firstPrimitive (Set.Icc 0 right) := by
          have primitiveContinuous :=
            intervalIntegral.continuousOn_primitive_interval'
              lineIntegrableRight (a := (0 : ℝ))
              Set.left_mem_uIcc
          simpa [firstPrimitive, Set.uIcc_of_le rightPositive.le] using
            primitiveContinuous
        refine ⟨-1, right, by norm_num, rightPositive, ?_⟩
        rw [← Set.Icc_union_Icc_eq_Icc (by norm_num) rightPositive.le]
        exact continuousLeft.union_of_isClosed continuousRight
          isClosed_Icc isClosed_Icc
      · have continuousRight :
            ContinuousOn firstPrimitive (Set.Icc 0 1) := by
          apply (continuousOn_const (c := (0 : E))).congr
          intro time timeMem
          dsimp [firstPrimitive]
          by_cases timeZero : time = 0
          · simp [timeZero]
          · apply intervalIntegral.integral_undef
            intro intervalIntegrable
            exact rightIntegrable
              ⟨time, lt_of_le_of_ne timeMem.1 (Ne.symm timeZero),
                intervalIntegrable⟩
        refine ⟨-1, 1, by norm_num, by norm_num, ?_⟩
        rw [← Set.Icc_union_Icc_eq_Icc
          (a := (-1 : ℝ)) (b := 0) (c := 1)
          (by norm_num) (by norm_num)]
        exact continuousLeft.union_of_isClosed continuousRight
          isClosed_Icc isClosed_Icc
  obtain ⟨left, right, leftNegative, rightPositive,
      firstPrimitiveContinuous⟩ :=
    firstPrimitiveContinuousNearZero
  have firstPrimitiveContinuousAt :
      ContinuousAt firstPrimitive 0 :=
    firstPrimitiveContinuous.continuousAt
      (Icc_mem_nhds leftNegative rightPositive)
  have firstPrimitiveStronglyMeasurableAt :
      StronglyMeasurableAtFilter firstPrimitive (nhds 0)
        MeasureTheory.volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (firstPrimitiveContinuous.mono Set.Ioo_subset_Icc_self)
      0 ⟨leftNegative, rightPositive⟩
  have outerDerivative :=
    intervalIntegral.integral_hasDerivAt_right
      (f := firstPrimitive) (a := (0 : ℝ)) (b := (0 : ℝ))
      IntervalIntegrable.refl firstPrimitiveStronglyMeasurableAt
      firstPrimitiveContinuousAt
  simpa [canonicalTimeSecondPrimitive, firstPrimitive, line] using
    outerDerivative

private theorem canonicalTimeLine_hasDerivAt
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    HasDerivAt
      (fun candidateTime => canonicalCauchySlicePoint candidateTime space)
      (coordinateDirection canonicalLorentzianTimeDirection)
      time := by
  have curveEq :
      (fun candidateTime =>
        canonicalCauchySlicePoint candidateTime space) =
      fun candidateTime =>
        canonicalCauchySlicePoint 0 space +
          candidateTime •
            coordinateDirection canonicalLorentzianTimeDirection := by
    funext candidateTime
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection]
  rw [curveEq]
  exact
    hasDerivAt_const_add_time_smul
      (canonicalCauchySlicePoint 0 space)
      (coordinateDirection canonicalLorentzianTimeDirection)
      time

/-- A genuine spacetime derivative is the derivative of its canonical time
restriction. -/
theorem field_timeLine_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    NormedHasDerivAt
      (fun candidateTime =>
        field (canonicalCauchySlicePoint candidateTime space))
      (fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space)
        canonicalLorentzianTimeDirection)
      time := by
  simpa [fieldDirectionalDerivative, Function.comp_def] using
    differentiable.hasFDerivAt.comp_hasDerivAt time
      (canonicalTimeLine_hasDerivAt space time)

private theorem fderiv_canonicalCauchySlicePoint_spatial
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection direction) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space) direction.succ := by
  have derivative :=
    differentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-! ## Source/current-only action profiles -/

private abbrev CompleteProfiles
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    CompleteJointGeneratedProfiles :=
  sourceActionGeneratedDiracDualCompleteJointProfiles source current point

/-- Faithful finite coordinates of the difference between the action-selected
total matter velocity and the raw velocity already carried by the current. -/
def completeJointMatterTemporalCoordinateCorrection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
      (CompleteProfiles source current point).matterVelocity -
    fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv (current.matter candidate))
      point canonicalLorentzianTimeDirection

/-- Faithful finite coordinates of the adjoint temporal correction. -/
def completeJointAdjointTemporalCoordinateCorrection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterDualCoordinates
      (CompleteProfiles source current point).adjointVelocity -
    fieldDirectionalDerivative
      (holonomicConjugateMatterCoordinates current) point
      canonicalLorentzianTimeDirection

/-- The scalar local writer supplies an additive second-order action response,
so its generated profile is integrated twice without subtracting a prior
acceleration. -/
def completeJointScalarAccelerationProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  (CompleteProfiles source current point).scalarAcceleration

/-! ## One global temporal write -/

/-- The global M/S temporal part of the complete-joint action write.

All three fields are advanced together from the same occurrence-native action
profile and the same zero-slice anchor.  Every other primitive field is
retained for the later P286/gravity integrability step of the common write. -/
def sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    scalar := fun point =>
      current.scalar point +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile source current) point
    matter := fun point =>
      current.matter point +
        matterCoordinateEquiv.symm
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection source current)
            point)
    conjugateMatter := fun point =>
      current.conjugateMatter point +
        matterDualOfCoordinates
          (canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection source current)
            point) }

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current).conjugateMatter =
      fun point =>
        current.conjugateMatter point +
          matterDualOfCoordinates
            (canonicalTimePrimitive
              (completeJointAdjointTemporalCoordinateCorrection source current)
              point) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current).scalar (canonicalCauchySlicePoint 0 space) =
      current.scalar (canonicalCauchySlicePoint 0 space) := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current).matter (canonicalCauchySlicePoint 0 space) =
      current.matter (canonicalCauchySlicePoint 0 space) := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      current.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]

/-- Every spatial first jet on the generated zero slice is inherited from
the supplied current.  The theorem asks only for differentiability at the
single occurrence being read; it does not promote an arbitrary current to a
globally smooth field. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative current.scalar
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  rw [← fderiv_canonicalCauchySlicePoint_spatial
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).scalar 0 space direction generatedDifferentiable,
    ← fderiv_canonicalCauchySlicePoint_spatial current.scalar 0 space direction
      currentDifferentiable]
  have sliceEquality :
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar ∘
          canonicalCauchySlicePoint 0 =
        current.scalar ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        source current candidateSpace
  rw [sliceEquality]

/-- The integrated matter field realizes the total occurrence-native action
velocity, rather than adding that velocity a second time. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_timeLine_hasDerivAt_of_intervalIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (currentDifferentiable :
      DifferentiableAt ℝ
        (fun point => matterCoordinateEquiv (current.matter point))
        (canonicalCauchySlicePoint time space))
    (correctionIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointMatterTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointMatterTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointMatterTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        time) :
    NormedHasDerivAt
      (fun candidateTime =>
        matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter
            (canonicalCauchySlicePoint candidateTime space)) index)
      (matterCoordinateEquiv
        (CompleteProfiles source current
          (canonicalCauchySlicePoint time space)).matterVelocity index)
      time := by
  have currentDerivative :=
    field_timeLine_hasDerivAt
      (fun point => matterCoordinateEquiv (current.matter point)) space time
      currentDifferentiable
  have correctionDerivative :=
    canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
      (completeJointMatterTemporalCoordinateCorrection source current)
      space time correctionIntervalIntegrable correctionMeasurableAt
      correctionContinuousAt
  have total := currentDerivative.add correctionDerivative
  let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index
      ).restrictScalars ℝ
  have projected :=
    projection.hasFDerivAt.comp_hasDerivAt time total
  convert projected using 1 <;>
    simp [projection,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
      completeJointMatterTemporalCoordinateCorrection, Function.comp_def]

/-- Global-continuity convenience form of the integrated matter velocity. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_timeLine_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (currentDifferentiable :
      DifferentiableAt ℝ
        (fun point => matterCoordinateEquiv (current.matter point))
        (canonicalCauchySlicePoint time space))
    (correctionContinuous :
      Continuous fun candidateTime =>
        completeJointMatterTemporalCoordinateCorrection source current
          (canonicalCauchySlicePoint candidateTime space)) :
    NormedHasDerivAt
      (fun candidateTime =>
        matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter
            (canonicalCauchySlicePoint candidateTime space)) index)
      (matterCoordinateEquiv
        (CompleteProfiles source current
          (canonicalCauchySlicePoint time space)).matterVelocity index)
      time :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_timeLine_hasDerivAt_of_intervalIntegrable
    source current space time index currentDifferentiable
    (correctionContinuous.intervalIntegrable 0 time)
    (correctionContinuous.stronglyMeasurableAtFilter
      MeasureTheory.volume (nhds time))
    correctionContinuous.continuousAt

/-- The adjoint field is advanced by the same canonical integral law. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_adjoint_timeLine_hasDerivAt_of_intervalIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (currentDifferentiable :
      DifferentiableAt ℝ (holonomicConjugateMatterCoordinates current)
        (canonicalCauchySlicePoint time space))
    (correctionIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointAdjointTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointAdjointTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointAdjointTemporalCoordinateCorrection source current
            (canonicalCauchySlicePoint candidateTime space))
        time) :
    NormedHasDerivAt
      (fun candidateTime =>
        matterDualCoordinates
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).conjugateMatter
            (canonicalCauchySlicePoint candidateTime space)) index)
      (matterDualCoordinates
        (CompleteProfiles source current
          (canonicalCauchySlicePoint time space)).adjointVelocity index)
      time := by
  have currentDerivative :=
    field_timeLine_hasDerivAt
      (holonomicConjugateMatterCoordinates current) space time
      currentDifferentiable
  have correctionDerivative :=
    canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
      (completeJointAdjointTemporalCoordinateCorrection source current)
      space time correctionIntervalIntegrable correctionMeasurableAt
      correctionContinuousAt
  have total := currentDerivative.add correctionDerivative
  let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index
      ).restrictScalars ℝ
  have projected :=
    projection.hasFDerivAt.comp_hasDerivAt time total
  convert projected using 1 <;>
    simp [projection,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
      completeJointAdjointTemporalCoordinateCorrection,
      holonomicConjugateMatterCoordinates, matterDualCoordinates_add,
      Function.comp_def]

/-- Global-continuity convenience form of the integrated adjoint velocity. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_adjoint_timeLine_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (currentDifferentiable :
      DifferentiableAt ℝ (holonomicConjugateMatterCoordinates current)
        (canonicalCauchySlicePoint time space))
    (correctionContinuous :
      Continuous fun candidateTime =>
        completeJointAdjointTemporalCoordinateCorrection source current
          (canonicalCauchySlicePoint candidateTime space)) :
    NormedHasDerivAt
      (fun candidateTime =>
        matterDualCoordinates
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).conjugateMatter
            (canonicalCauchySlicePoint candidateTime space)) index)
      (matterDualCoordinates
        (CompleteProfiles source current
          (canonicalCauchySlicePoint time space)).adjointVelocity index)
      time :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_adjoint_timeLine_hasDerivAt_of_intervalIntegrable
    source current space time index currentDifferentiable
    (correctionContinuous.intervalIntegrable 0 time)
    (correctionContinuous.stronglyMeasurableAtFilter
      MeasureTheory.volume (nhds time))
    correctionContinuous.continuousAt

/-- The scalar second primitive has the correct first derivative; a second
application of the fundamental theorem yields the generated acceleration. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_timeLine_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint time space))
    (accelerationContinuous :
      Continuous fun candidateTime =>
        completeJointScalarAccelerationProfile source current
          (canonicalCauchySlicePoint candidateTime space)) :
    NormedHasDerivAt
      (fun candidateTime =>
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
          (canonicalCauchySlicePoint candidateTime space))
      (fieldDirectionalDerivative current.scalar
          (canonicalCauchySlicePoint time space)
          canonicalLorentzianTimeDirection +
        canonicalTimePrimitive
          (completeJointScalarAccelerationProfile source current)
          (canonicalCauchySlicePoint time space))
      time := by
  exact
    (field_timeLine_hasDerivAt current.scalar space time
      currentDifferentiable).add
      (canonicalTimeSecondPrimitive_timeLine_hasDerivAt
        (completeJointScalarAccelerationProfile source current) space time
        accelerationContinuous)

/-- At the zero slice the scalar second primitive also preserves the temporal
first jet.  Its derivative contribution is the first primitive at time zero,
hence vanishes canonically. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_temporalDirectionalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative current.scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection := by
  have generatedLine :=
    field_timeLine_hasDerivAt
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).scalar
      space 0 generatedDifferentiable
  have actionLine :
      NormedHasDerivAt
        (fun candidateTime =>
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).scalar
            (canonicalCauchySlicePoint candidateTime space))
        (fieldDirectionalDerivative current.scalar
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection)
        0 := by
    convert
      (field_timeLine_hasDerivAt current.scalar space 0
          currentDifferentiable).add
        (canonicalTimeSecondPrimitive_timeLine_hasDerivAt_zero
          (completeJointScalarAccelerationProfile source current) space)
      using 1 <;>
        simp [
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          ] <;>
        funext candidateTime <;>
        rfl
  have derivativeEquality := generatedLine.unique actionLine
  simpa using derivativeEquality

/-- The complete scalar first jet on the generated zero slice is therefore
the first jet of the same supplied current. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    ∀ direction : LorentzianIndex,
      fieldDirectionalDerivative
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).scalar
          (canonicalCauchySlicePoint 0 space) direction =
        fieldDirectionalDerivative current.scalar
          (canonicalCauchySlicePoint 0 space) direction := by
  intro direction
  fin_cases direction
  · exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_temporalDirectionalDerivative_zeroSlice
        source current space currentDifferentiable generatedDifferentiable
  · simpa using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
        source current space 0 currentDifferentiable generatedDifferentiable
  · simpa using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
        source current space 1 currentDifferentiable generatedDifferentiable
  · simpa using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
        source current space 2 currentDifferentiable generatedDifferentiable

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
