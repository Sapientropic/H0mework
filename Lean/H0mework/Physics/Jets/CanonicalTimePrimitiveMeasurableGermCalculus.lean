import H0mework.Physics.JointVariation.TemporalDevelopmentOperator

/-!
# Canonical time-primitive measurable-germ calculus

This module supplies the generic analytic bridge used by source-generated
canonical time writes: local `C⁰` regularity yields a globally strongly
measurable proof-side germ representative, and that representative validates
the ambient derivative of the original canonical primitive.

The representative is an integration adapter only; it is never installed
into a source or physical current.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCanonicalTimePrimitiveMeasurableGermCalculus

open Asymptotics Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff Interval Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem clm_smul_continuousAt_hasFDerivAt_zero_probe
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

private theorem normalizedCanonicalTimeSlice_tendsto_zero_probe :
    Tendsto
      (fun joint : BasePoint × ℝ =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection joint.1 * joint.2)
          (canonicalSpatialProjection joint.1))
      (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
      (𝓝 0) := by
  have parameterBounded :
      IsBoundedUnder (· ≤ ·)
        (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
        (norm ∘ fun joint : BasePoint × ℝ => joint.2) := by
    have parameterIn :
        ∀ᶠ joint : BasePoint × ℝ in
            (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)),
          joint.2 ∈ Set.Icc (0 : ℝ) 1 :=
      (tendsto_snd : Tendsto
        (fun joint : BasePoint × ℝ => joint.2)
        (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
        (𝓟 (Set.Icc (0 : ℝ) 1))) (by simp)
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [parameterIn] with joint hjoint
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg hjoint.1] using hjoint.2
  have timeTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalTimeProjection joint.1)
        (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
        (𝓝 0) := by
    change Tendsto
      (canonicalTimeProjection ∘
        (fun joint : BasePoint × ℝ => joint.1))
      (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)) (𝓝 0)
    simpa only [map_zero] using
      canonicalTimeProjection.continuous.continuousAt.tendsto.comp
        (tendsto_fst :
          Tendsto (fun joint : BasePoint × ℝ => joint.1)
            (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)) (𝓝 0))
  have scaledTimeTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalTimeProjection joint.1 * joint.2)
        (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
        (𝓝 0) :=
    timeTends.zero_mul_isBoundedUnder_le parameterBounded
  have spaceTends :
      Tendsto
        (fun joint : BasePoint × ℝ =>
          canonicalSpatialProjection joint.1)
        (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1))
        (𝓝 0) := by
    change Tendsto
      (canonicalSpatialProjection ∘
        (fun joint : BasePoint × ℝ => joint.1))
      (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)) (𝓝 0)
    simpa only [map_zero] using
      canonicalSpatialProjection.continuous.continuousAt.tendsto.comp
        (tendsto_fst :
          Tendsto (fun joint : BasePoint × ℝ => joint.1)
            (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)) (𝓝 0))
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

/-- Local continuity of an action profile is preserved by the canonical
temporal primitive near the common occurrence.

The normalized time segments of every sufficiently small spacetime point
stay in one neighborhood on which the supplied profile is continuous.  The
interval integral is therefore continuous on one common point neighborhood;
no global measurability or global coframe nondegeneracy is required. -/
theorem canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 0 profile 0) :
    ContDiffAt ℝ 0 (canonicalTimePrimitive profile) 0 := by
  let normalizedProfile : BasePoint → ℝ → E := fun point parameter =>
    profile
      (canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point))
  let average : BasePoint → E := fun point =>
    ∫ parameter in (0 : ℝ)..1, normalizedProfile point parameter
  obtain ⟨localSet, localSetNhd, profileContinuousOn⟩ :=
    contDiffAt_zero.mp regular
  have normalizedEventuallyInLocal :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)),
        canonicalCauchySlicePoint
            (canonicalTimeProjection joint.1 * joint.2)
            (canonicalSpatialProjection joint.1) ∈
          localSet :=
    normalizedCanonicalTimeSlice_tendsto_zero_probe.eventually localSetNhd
  obtain ⟨pointSet, pointSetNhd, parameterSet, parameterSetPrincipal,
      productSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyInLocal
  have intervalSubsetParameter :
      Set.Icc (0 : ℝ) 1 ⊆ parameterSet := by
    simpa only [Filter.mem_principal] using parameterSetPrincipal
  have profileNormBounded :
      IsBoundedUnder (· ≤ ·) (𝓝 (0 : BasePoint))
        (norm ∘ profile) :=
    regular.continuousAt.norm.isBoundedUnder_le
  obtain ⟨bound, profileEventuallyBounded⟩ :=
    profileNormBounded.eventually_le
  have normalizedEventuallyBounded :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)),
        ‖normalizedProfile joint.1 joint.2‖ ≤ bound := by
    exact normalizedCanonicalTimeSlice_tendsto_zero_probe.eventually
      profileEventuallyBounded
  obtain ⟨boundPointSet, boundPointSetNhd, boundParameterSet,
      boundParameterPrincipal, boundProductSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyBounded
  have intervalSubsetBoundParameter :
      Set.Icc (0 : ℝ) 1 ⊆ boundParameterSet := by
    simpa only [Filter.mem_principal] using boundParameterPrincipal
  let domain : Set BasePoint := pointSet ∩ boundPointSet
  have domainNhd : domain ∈ 𝓝 (0 : BasePoint) := by
    exact inter_mem pointSetNhd boundPointSetNhd
  have normalizedContinuousOn
      (parameter : ℝ)
      (parameterIn : parameter ∈ Set.Icc (0 : ℝ) 1) :
      ContinuousOn (fun point => normalizedProfile point parameter)
        domain := by
    have innerContinuous :
        Continuous fun point : BasePoint =>
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
        ((canonicalTimeProjection.continuous.mul
            continuous_const).smul continuous_const).add
          (canonicalSpatialInclusion.continuous.comp
            canonicalSpatialProjection.continuous)
    apply profileContinuousOn.comp innerContinuous.continuousOn
    intro point pointIn
    have pairIn :
        (point, parameter) ∈ pointSet ×ˢ parameterSet := by
      exact
        ⟨pointIn.1, intervalSubsetParameter parameterIn⟩
    exact productSubset pairIn
  have normalizedMeasurable
      (point : BasePoint)
      (pointIn : point ∈ domain) :
      AEStronglyMeasurable (normalizedProfile point)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    have continuousOn :
        ContinuousOn (normalizedProfile point) (Set.Icc (0 : ℝ) 1) := by
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
              continuous_const).add continuous_const
      have composed :=
        profileContinuousOn.comp innerContinuous.continuousOn
          (fun parameter parameterIn => by
            have pairIn :
                (point, parameter) ∈ pointSet ×ˢ parameterSet :=
              ⟨pointIn.1, intervalSubsetParameter parameterIn⟩
            exact productSubset pairIn)
      simpa [normalizedProfile, Function.comp_def] using composed
    have intervalSubset :
        Ι (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      intro parameter parameterIn
      have actual := Set.uIoc_subset_uIcc parameterIn
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    exact
      (continuousOn.mono intervalSubset).aestronglyMeasurable
        measurableSet_uIoc
  have normalizedBounded
      (point : BasePoint)
      (pointIn : point ∈ domain) :
      ∀ᵐ parameter ∂MeasureTheory.volume,
        parameter ∈ Ι (0 : ℝ) 1 →
          ‖normalizedProfile point parameter‖ ≤ bound := by
    filter_upwards [] with parameter
    intro parameterIn
    have intervalMembership : parameter ∈ Set.Icc (0 : ℝ) 1 := by
      have actual := Set.uIoc_subset_uIcc parameterIn
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    have pairIn :
        (point, parameter) ∈ boundPointSet ×ˢ boundParameterSet :=
      ⟨pointIn.2,
        intervalSubsetBoundParameter intervalMembership⟩
    exact boundProductSubset pairIn
  have boundIntegrable :
      IntervalIntegrable (fun _ : ℝ => bound)
        MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have averageContinuousOn : ContinuousOn average domain := by
    intro point pointIn
    unfold average
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
    · filter_upwards [self_mem_nhdsWithin] with candidate candidateIn
      exact normalizedMeasurable candidate candidateIn
    · filter_upwards [self_mem_nhdsWithin] with candidate candidateIn
      exact normalizedBounded candidate candidateIn
    · exact boundIntegrable
    · filter_upwards [] with parameter parameterIn
      have intervalMembership : parameter ∈ Set.Icc (0 : ℝ) 1 := by
        have actual := Set.uIoc_subset_uIcc parameterIn
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      exact
        (normalizedContinuousOn parameter intervalMembership) point pointIn
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
  rw [contDiffAt_zero]
  refine ⟨domain, domainNhd, ?_⟩
  rw [show canonicalTimePrimitive profile =
      fun point => canonicalTimeProjection point • average point by
    funext point
    exact scaleIdentity point]
  exact canonicalTimeProjection.continuous.continuousOn.smul
    averageContinuousOn

/-- Every locally continuous finite-dimensional field germ has a globally
strongly measurable representative that agrees with it on one open
neighborhood of the base point.

This is a proof-side integration adapter only.  The representative is cut to
zero outside the selected neighborhood and is never installed into a source
or physical current. -/
theorem exists_stronglyMeasurable_eventuallyEq_of_contDiffAt_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [MeasurableSpace E]
    [BorelSpace E]
    [SecondCountableTopology E]
    (field : BasePoint → E)
    (regular : ContDiffAt ℝ 0 field 0) :
    ∃ representative : BasePoint → E,
      StronglyMeasurable representative ∧
    field =ᶠ[𝓝 0] representative := by
  classical
  obtain ⟨localSet, localSetNhd, fieldContinuousOn⟩ :=
    contDiffAt_zero.mp regular
  obtain ⟨domain, domainSubset, domainOpen, zeroMem⟩ :=
    mem_nhds_iff.mp localSetNhd
  let representative : BasePoint → E :=
    domain.piecewise field 0
  have representativeMeasurable : Measurable representative := by
    exact
      (fieldContinuousOn.mono domainSubset).measurable_piecewise
        continuous_const.continuousOn domainOpen.measurableSet
  refine
    ⟨representative, representativeMeasurable.stronglyMeasurable, ?_⟩
  filter_upwards [domainOpen.mem_nhds zeroMem] with point pointIn
  simp [representative, pointIn]

/-- A locally continuous, globally strongly measurable action profile gives
the expected ambient derivative of its canonical temporal primitive.  The
measurability hypothesis is the exact integration seam absent from a bare
`ContinuousAt` statement. -/
theorem canonicalTimePrimitive_hasFDerivAt_zero_of_continuousAt_of_stronglyMeasurable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (profileContinuous : ContinuousAt profile 0)
    (profileMeasurable : StronglyMeasurable profile) :
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
      simpa [sliceZero] using profileContinuous
    exact ContinuousAt.comp'
      (f := fun point : BasePoint =>
        canonicalCauchySlicePoint
          (canonicalTimeProjection point * parameter)
          (canonicalSpatialProjection point))
      outer innerContinuous
  have measurableEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        AEStronglyMeasurable (normalizedProfile point)
          (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [] with point
    have innerMeasurable :
        Measurable fun parameter : ℝ =>
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
        (((continuous_const.mul continuous_id).smul
            continuous_const).add continuous_const).measurable
    exact
      (profileMeasurable.comp_measurable innerMeasurable).aestronglyMeasurable
        |>.restrict
  have profileNormBounded :
      IsBoundedUnder (· ≤ ·) (𝓝 (0 : BasePoint))
        (norm ∘ profile) :=
    profileContinuous.norm.isBoundedUnder_le
  obtain ⟨bound, profileEventuallyBounded⟩ :=
    profileNormBounded.eventually_le
  have normalizedEventuallyBounded :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)),
        ‖normalizedProfile joint.1 joint.2‖ ≤ bound := by
    exact normalizedCanonicalTimeSlice_tendsto_zero_probe.eventually
      profileEventuallyBounded
  obtain ⟨boundPointSet, boundPointSetNhd, boundParameterSet,
      boundParameterPrincipal, boundProductSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyBounded
  have intervalSubsetBoundParameter : Set.Icc (0 : ℝ) 1 ⊆
      boundParameterSet := by
    simpa only [Filter.mem_principal] using boundParameterPrincipal
  have boundEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        ∀ᵐ parameter ∂MeasureTheory.volume,
          parameter ∈ Ι (0 : ℝ) 1 →
            ‖normalizedProfile point parameter‖ ≤ bound := by
    filter_upwards [boundPointSetNhd] with point pointIn
    filter_upwards [] with parameter
    intro parameterIn
    have intervalMembership : parameter ∈ Set.Icc (0 : ℝ) 1 := by
      have actual := Set.uIoc_subset_uIcc parameterIn
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
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
    clm_smul_continuousAt_hasFDerivAt_zero_probe
      canonicalTimeProjection average averageContinuous
  have transported :=
    generated.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun point => scaleIdentity point)
  simpa [averageZero] using transported

/-- A globally measurable representative may be used to discharge the local
integration seam when it agrees pointwise with the generated profile on one
neighborhood of the common occurrence.

The representative is not a producer input.  Uniform convergence of all
normalized shrinking time segments transports the pointwise germ equality to
the two canonical primitives, after which the derivative generated from the
measurable representative is transferred back to the original profile. -/
theorem
    canonicalTimePrimitive_hasFDerivAt_zero_of_continuousAt_of_eventuallyEq_stronglyMeasurable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile representative : BasePoint → E)
    (profileContinuous : ContinuousAt profile 0)
    (representativeMeasurable : StronglyMeasurable representative)
    (germEq : profile =ᶠ[𝓝 0] representative) :
    HasFDerivAt (canonicalTimePrimitive profile)
      (canonicalTimeProjection.smulRight (profile 0)) 0 := by
  have representativeContinuous : ContinuousAt representative 0 :=
    profileContinuous.congr_of_eventuallyEq germEq.symm
  have generated :=
    canonicalTimePrimitive_hasFDerivAt_zero_of_continuousAt_of_stronglyMeasurable
      representative representativeContinuous representativeMeasurable
  have normalizedEventuallyEq :
      ∀ᶠ joint : BasePoint × ℝ in
          (𝓝 0 ×ˢ 𝓟 (Set.Icc (0 : ℝ) 1)),
        profile
            (canonicalCauchySlicePoint
              (canonicalTimeProjection joint.1 * joint.2)
              (canonicalSpatialProjection joint.1)) =
          representative
            (canonicalCauchySlicePoint
              (canonicalTimeProjection joint.1 * joint.2)
              (canonicalSpatialProjection joint.1)) :=
    normalizedCanonicalTimeSlice_tendsto_zero_probe.eventually germEq
  obtain ⟨pointSet, pointSetNhd, parameterSet, parameterSetPrincipal,
      productSubset⟩ :=
    Filter.mem_prod_iff.mp normalizedEventuallyEq
  have intervalSubsetParameter :
      Set.Icc (0 : ℝ) 1 ⊆ parameterSet := by
    simpa only [Filter.mem_principal] using parameterSetPrincipal
  have scaleIdentity
      (field : BasePoint → E)
      (point : BasePoint) :
      canonicalTimePrimitive field point =
        canonicalTimeProjection point •
          ∫ parameter in (0 : ℝ)..1,
            field
              (canonicalCauchySlicePoint
                (canonicalTimeProjection point * parameter)
                (canonicalSpatialProjection point)) := by
    simpa [canonicalTimePrimitive] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun time =>
          field
            (canonicalCauchySlicePoint time
              (canonicalSpatialProjection point)))
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (canonicalTimeProjection point)).symm
  have primitiveGermEq :
      canonicalTimePrimitive profile =ᶠ[𝓝 0]
        canonicalTimePrimitive representative := by
    filter_upwards [pointSetNhd] with point pointIn
    rw [scaleIdentity profile point, scaleIdentity representative point]
    congr 1
    apply intervalIntegral.integral_congr
    intro parameter parameterIn
    have intervalMembership : parameter ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using parameterIn
    have parameterInSet : parameter ∈ parameterSet :=
      intervalSubsetParameter intervalMembership
    have pairIn :
        (point, parameter) ∈ pointSet ×ˢ parameterSet :=
      ⟨pointIn, parameterInSet⟩
    exact productSubset pairIn
  have transported :=
    generated.congr_of_eventuallyEq primitiveGermEq
  have valueEq : profile 0 = representative 0 :=
    germEq.self_of_nhds
  simpa [valueEq] using transported

/-- A locally continuous finite-dimensional profile already supplies the
complete proof-side integration seam for its canonical temporal primitive.
The measurable representative is generated from the germ and is never
installed in the physical current. -/
theorem canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    [MeasurableSpace E]
    [BorelSpace E]
    [SecondCountableTopology E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 0 profile 0) :
    HasFDerivAt (canonicalTimePrimitive profile)
      (canonicalTimeProjection.smulRight (profile 0)) 0 := by
  obtain ⟨representative, representativeMeasurable, germEq⟩ :=
    exists_stronglyMeasurable_eventuallyEq_of_contDiffAt_zero profile regular
  exact
    canonicalTimePrimitive_hasFDerivAt_zero_of_continuousAt_of_eventuallyEq_stronglyMeasurable
      profile representative regular.continuousAt representativeMeasurable
        germEq

theorem canonicalTimePrimitive_stronglyMeasurable_of_stronglyMeasurable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (profileMeasurable : StronglyMeasurable profile) :
    StronglyMeasurable (canonicalTimePrimitive profile) := by
  let normalizedProfile : BasePoint × ℝ → E := fun joint =>
    profile
      (canonicalCauchySlicePoint
        (canonicalTimeProjection joint.1 * joint.2)
        (canonicalSpatialProjection joint.1))
  have normalizedMeasurable : StronglyMeasurable normalizedProfile := by
    apply profileMeasurable.comp_measurable
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
    fun_prop
  let average : BasePoint → E := fun point =>
    ∫ parameter in (0 : ℝ)..1, normalizedProfile (point, parameter)
  have averageMeasurable : StronglyMeasurable average := by
    have fixedIntegral :=
      normalizedMeasurable.integral_prod_right'
        (ν := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
    rw [show average =
        fun point =>
          ∫ parameter in Set.Ioc (0 : ℝ) 1,
            normalizedProfile (point, parameter) by
      funext point
      exact intervalIntegral.integral_of_le (by norm_num)]
    exact fixedIntegral
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
  have productMeasurable : StronglyMeasurable
      (fun point =>
        canonicalTimeProjection point • average point) := by
    fun_prop
  rw [show canonicalTimePrimitive profile =
      fun point =>
        canonicalTimeProjection point • average point by
    funext point
    exact scaleIdentity point]
  exact productMeasurable

theorem canonicalTimeSecondPrimitive_stronglyMeasurable_of_stronglyMeasurable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (profileMeasurable : StronglyMeasurable profile) :
    StronglyMeasurable (canonicalTimeSecondPrimitive profile) := by
  have firstMeasurable :=
    canonicalTimePrimitive_stronglyMeasurable_of_stronglyMeasurable
      profile profileMeasurable
  have secondMeasurable :=
    canonicalTimePrimitive_stronglyMeasurable_of_stronglyMeasurable
      (canonicalTimePrimitive profile) firstMeasurable
  have iteratedEq :
      canonicalTimePrimitive (canonicalTimePrimitive profile) =
        canonicalTimeSecondPrimitive profile := by
    funext point
    simp [canonicalTimePrimitive, canonicalTimeSecondPrimitive]
  rwa [iteratedEq] at secondMeasurable

end

end
  SaturationMonoid.PhysicsCore.StageNineCanonicalTimePrimitiveMeasurableGermCalculus
