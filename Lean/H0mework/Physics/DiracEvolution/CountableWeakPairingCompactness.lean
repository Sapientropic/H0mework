import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

/-!
# Countable weak-pairing compactness

Arzelà--Ascoli is applied once for each member of a countable test family and
then to the compact product of all resulting closures.  The selected strict
subsequence therefore works simultaneously for every test.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCountableWeakPairingCompactness

open Filter MeasureTheory Metric Set
open scoped BoundedContinuousFunction Interval

noncomputable section

set_option autoImplicit false

/-- Countably many uniformly bounded, equi-Lipschitz observables have one
strict subsequence converging uniformly for every observable. -/
theorem exists_commonUniformSubsequence_of_lipschitz
    {Time : Type*} [MetricSpace Time] [CompactSpace Time]
    (pairing : ℕ → ℕ → Time →ᵇ ℝ)
    (lipschitzConstant : ℕ → NNReal)
    (rangeRadius : ℕ → ℝ)
    (pairingLipschitz : ∀ approximation test,
      LipschitzWith (lipschitzConstant test) (pairing approximation test))
    (pairingBounded : ∀ approximation test time,
      ‖pairing approximation test time‖ ≤ rangeRadius test) :
    ∃ limit : ℕ → Time →ᵇ ℝ,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ∀ test, Filter.Tendsto
            (fun approximation ↦ pairing (subsequence approximation) test)
            Filter.atTop (nhds (limit test)) := by
  let candidate : ℕ → Set (Time →ᵇ ℝ) := fun test ↦
    Set.range (fun approximation ↦ pairing approximation test)
  have candidateCompact (test : ℕ) :
      IsCompact (closure (candidate test)) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (closedBall (0 : ℝ) (rangeRadius test))
      (isCompact_closedBall (0 : ℝ) (rangeRadius test))
    · intro observable time observableMem
      obtain ⟨approximation, rfl⟩ := observableMem
      simpa [mem_closedBall, dist_zero_right] using
        pairingBounded approximation test time
    · let family : candidate test → Time → ℝ :=
        fun observable ↦ observable.1
      have familyLipschitz : ∀ observable,
          LipschitzWith (lipschitzConstant test) (family observable) := by
        rintro ⟨observable, approximation, rfl⟩
        exact pairingLipschitz approximation test
      exact (LipschitzWith.uniformEquicontinuous family
        (lipschitzConstant test) familyLipschitz).equicontinuous
  let CompactCandidate := fun test : ℕ ↦ ↥(closure (candidate test))
  letI candidateCompactSpace (test : ℕ) : CompactSpace (CompactCandidate test) :=
    isCompact_iff_compactSpace.mp (candidateCompact test)
  let bundled : ℕ → ∀ test, CompactCandidate test :=
    fun approximation test ↦
      ⟨pairing approximation test,
        subset_closure ⟨approximation, rfl⟩⟩
  obtain ⟨bundledLimit, subsequence, subsequenceStrict, bundledConvergence⟩ :=
    CompactSpace.tendsto_subseq bundled
  refine ⟨fun test ↦ (bundledLimit test).1, subsequence,
    subsequenceStrict, ?_⟩
  intro test
  have componentConvergence : Tendsto
      (fun approximation ↦ bundled (subsequence approximation) test)
      atTop (nhds (bundledLimit test)) :=
    (continuous_apply test).continuousAt.tendsto.comp bundledConvergence
  exact continuous_subtype_val.continuousAt.tendsto.comp componentConvergence

/-- If the uniform estimates for the `test`th observable start only after its
entry index, one common strict subsequence still converges for every test. -/
theorem exists_commonUniformSubsequence_of_eventually_lipschitz
    {Time : Type*} [MetricSpace Time] [CompactSpace Time]
    (pairing : ℕ → ℕ → Time →ᵇ ℝ)
    (entry : ℕ → ℕ)
    (lipschitzConstant : ℕ → NNReal)
    (rangeRadius : ℕ → ℝ)
    (pairingLipschitz : ∀ approximation test,
      entry test ≤ approximation →
        LipschitzWith (lipschitzConstant test) (pairing approximation test))
    (pairingBounded : ∀ approximation test,
      entry test ≤ approximation → ∀ time,
        ‖pairing approximation test time‖ ≤ rangeRadius test) :
    ∃ limit : ℕ → Time →ᵇ ℝ,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ∀ test, Filter.Tendsto
            (fun approximation ↦ pairing (subsequence approximation) test)
            Filter.atTop (nhds (limit test)) := by
  let stabilized : ℕ → ℕ → Time →ᵇ ℝ :=
    fun approximation test ↦
      if entry test ≤ approximation then pairing approximation test
      else pairing (entry test) test
  have stabilizedLipschitz (approximation test : ℕ) :
      LipschitzWith (lipschitzConstant test)
        (stabilized approximation test) := by
    by_cases tail : entry test ≤ approximation
    · simpa [stabilized, tail] using pairingLipschitz approximation test tail
    · simpa [stabilized, tail] using
        pairingLipschitz (entry test) test le_rfl
  have stabilizedBounded (approximation test : ℕ) (time : Time) :
      ‖stabilized approximation test time‖ ≤ rangeRadius test := by
    by_cases tail : entry test ≤ approximation
    · simpa [stabilized, tail] using pairingBounded approximation test tail time
    · simpa [stabilized, tail] using
        pairingBounded (entry test) test le_rfl time
  obtain ⟨limit, subsequence, subsequenceStrict, convergence⟩ :=
    exists_commonUniformSubsequence_of_lipschitz stabilized
      lipschitzConstant rangeRadius stabilizedLipschitz stabilizedBounded
  refine ⟨limit, subsequence, subsequenceStrict, ?_⟩
  intro test
  apply (convergence test).congr'
  have eventuallyTail : Filter.Eventually
      (fun approximation : ℕ ↦ entry test ≤ subsequence approximation)
      atTop :=
    subsequenceStrict.tendsto_atTop (eventually_ge_atTop (entry test))
  filter_upwards [eventuallyTail] with approximation tail
  simp [stabilized, tail]

/-- Uniform convergence of compact-time primitives transports every exact
weighted rate identity to the distributional identity of the limit. -/
theorem weightedRateIntegral_tendsto_of_boundedContinuousPairing
    {Index : Type*}
    {indexFilter : Filter Index}
    [indexFilter.IsCountablyGenerated]
    {timeStart timeEnd : ℝ}
    (timeOrder : timeStart ≤ timeEnd)
    (pairing : Index → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (rate : Index → ℝ → ℝ)
    (limit : (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (pairingConvergence : Tendsto pairing indexFilter (nhds limit))
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (finiteWeightedEquation : ∀ index,
      (∫ time in timeStart..timeEnd, weight time * rate index time) =
        weight timeEnd * pairing index
            ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
          weight timeStart * pairing index
            ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
          ∫ time in timeStart..timeEnd,
            deriv weight time *
              pairing index (projIcc timeStart timeEnd timeOrder time)) :
    Tendsto
      (fun index ↦ ∫ time in timeStart..timeEnd,
        weight time * rate index time)
      indexFilter
      (nhds (weight timeEnd *
          limit ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
        weight timeStart *
          limit ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
        ∫ time in timeStart..timeEnd, deriv weight time *
          limit (projIcc timeStart timeEnd timeOrder time))) := by
  let derivativeWeight : (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun time ↦ deriv weight time.1,
        (weightRegular.continuous_deriv le_rfl).comp continuous_subtype_val⟩
  have weightedConvergence : Tendsto
      (fun index ↦ derivativeWeight * pairing index)
      indexFilter (nhds (derivativeWeight * limit)) :=
    tendsto_const_nhds.mul pairingConvergence
  have pairingUniform :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      pairingConvergence
  have weightedUniform :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      weightedConvergence
  change TendstoUniformly
    (fun index time ↦ derivativeWeight time * pairing index time)
    (fun time ↦ derivativeWeight time * limit time)
    indexFilter at weightedUniform
  have projectedUniform : TendstoUniformlyOn
      (fun index time ↦ deriv weight time *
        pairing index (projIcc timeStart timeEnd timeOrder time))
      (fun time ↦ deriv weight time *
        limit (projIcc timeStart timeEnd timeOrder time))
      indexFilter [[timeStart, timeEnd]] := by
    rw [uIcc_of_le timeOrder,
      tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [derivativeWeight, Function.comp_def, projIcc_of_mem] using
      weightedUniform
  have weightedContinuous : ∀ᶠ index in indexFilter,
      ContinuousOn
        (fun time ↦ deriv weight time *
          pairing index (projIcc timeStart timeEnd timeOrder time))
        [[timeStart, timeEnd]] := by
    exact Filter.Eventually.of_forall fun index ↦
      ((weightRegular.continuous_deriv le_rfl).mul
        ((pairing index).continuous.comp continuous_projIcc)).continuousOn
  have integralConvergence :=
    projectedUniform.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      weightedContinuous
  have endConvergence := pairingUniform.tendsto_at
    ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩
  have startConvergence := pairingUniform.tendsto_at
    ⟨timeStart, left_mem_Icc.mpr timeOrder⟩
  have weightedEndConvergence : Tendsto
      (fun index ↦ weight timeEnd *
        pairing index ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩)
      indexFilter
      (nhds (weight timeEnd *
        limit ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩)) :=
    tendsto_const_nhds.mul endConvergence
  have weightedStartConvergence : Tendsto
      (fun index ↦ weight timeStart *
        pairing index ⟨timeStart, left_mem_Icc.mpr timeOrder⟩)
      indexFilter
      (nhds (weight timeStart *
        limit ⟨timeStart, left_mem_Icc.mpr timeOrder⟩)) :=
    tendsto_const_nhds.mul startConvergence
  have rightHandConvergence :=
    (weightedEndConvergence.sub weightedStartConvergence).sub
      integralConvergence
  apply rightHandConvergence.congr'
  exact Filter.Eventually.of_forall fun index ↦
    (finiteWeightedEquation index).symm

/-- The exact history-indexed output of one common weak-limit event.  It
records the selected strict subsequence together with both the endpoint and
time-weighted action laws; it does not choose a field representative. -/
structure CountableWeightedWeakLimitOccurrence
    {timeStart timeEnd : ℝ}
    (timeOrder : timeStart ≤ timeEnd)
    (pairing : ℕ → ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (rate : ℕ → ℕ → ℝ → ℝ)
    (_entry : ℕ → ℕ) where
  finiteEndpointEquation : ∀ approximation test time
    (timeMem : time ∈ Icc timeStart timeEnd),
    (∫ candidateTime in timeStart..time,
        rate approximation test candidateTime) =
      pairing approximation test ⟨time, timeMem⟩ -
        pairing approximation test
          ⟨timeStart, left_mem_Icc.mpr timeOrder⟩
  finiteWeightedEquation : ∀ (approximation test : ℕ)
    (weight : ℝ → ℝ), ContDiff ℝ 1 weight →
    (∫ candidateTime in timeStart..timeEnd,
        weight candidateTime * rate approximation test candidateTime) =
      weight timeEnd *
          pairing approximation test
            ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
        weight timeStart *
          pairing approximation test
            ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
        ∫ candidateTime in timeStart..timeEnd,
          deriv weight candidateTime *
            pairing approximation test
              (projIcc timeStart timeEnd timeOrder candidateTime)
  limit : ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ
  subsequence : ℕ → ℕ
  subsequenceStrict : StrictMono subsequence
  pairingConvergence : ∀ test,
    Tendsto (fun sequenceIndex ↦ pairing (subsequence sequenceIndex) test)
      atTop (nhds (limit test))
  endpointRateConvergence : ∀ test time (timeMem : time ∈ Icc timeStart timeEnd),
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in timeStart..time,
        rate (subsequence sequenceIndex) test candidateTime)
      atTop
      (nhds (limit test ⟨time, timeMem⟩ -
        limit test ⟨timeStart, left_mem_Icc.mpr timeOrder⟩))
  weightedRateConvergence : ∀ (test : ℕ) (weight : ℝ → ℝ),
    ContDiff ℝ 1 weight →
      Tendsto
        (fun sequenceIndex ↦ ∫ candidateTime in timeStart..timeEnd,
          weight candidateTime *
            rate (subsequence sequenceIndex) test candidateTime)
        atTop
        (nhds (weight timeEnd *
            limit test ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
          weight timeStart *
            limit test ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
          ∫ candidateTime in timeStart..timeEnd,
            deriv weight candidateTime *
              limit test
                (projIcc timeStart timeEnd timeOrder candidateTime)))

/-- Eventual fixed-test estimates and exact finite action laws generate one
history-indexed weak-limit occurrence. -/
theorem exists_countableWeightedWeakLimitOccurrence_of_eventually_lipschitz
    {timeStart timeEnd : ℝ}
    (timeOrder : timeStart ≤ timeEnd)
    (pairing : ℕ → ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (rate : ℕ → ℕ → ℝ → ℝ)
    (entry : ℕ → ℕ)
    (lipschitzConstant : ℕ → NNReal)
    (rangeRadius : ℕ → ℝ)
    (pairingLipschitz : ∀ approximation test,
      entry test ≤ approximation →
        LipschitzWith (lipschitzConstant test) (pairing approximation test))
    (pairingBounded : ∀ approximation test,
      entry test ≤ approximation → ∀ time,
        ‖pairing approximation test time‖ ≤ rangeRadius test)
    (finiteEndpointEquation : ∀ approximation test time
      (timeMem : time ∈ Icc timeStart timeEnd),
      (∫ candidateTime in timeStart..time,
          rate approximation test candidateTime) =
        pairing approximation test ⟨time, timeMem⟩ -
          pairing approximation test
            ⟨timeStart, left_mem_Icc.mpr timeOrder⟩)
    (finiteWeightedEquation : ∀ (approximation test : ℕ)
      (weight : ℝ → ℝ),
      ContDiff ℝ 1 weight →
        (∫ candidateTime in timeStart..timeEnd,
            weight candidateTime *
              rate approximation test candidateTime) =
          weight timeEnd *
              pairing approximation test
                ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
            weight timeStart *
              pairing approximation test
                ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
            ∫ candidateTime in timeStart..timeEnd,
              deriv weight candidateTime *
                pairing approximation test
                  (projIcc timeStart timeEnd timeOrder candidateTime)) :
    Nonempty (CountableWeightedWeakLimitOccurrence timeOrder pairing rate entry) := by
  let Time := Icc timeStart timeEnd
  letI : CompactSpace Time := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨limit, subsequence, subsequenceStrict, convergence⟩ :=
    exists_commonUniformSubsequence_of_eventually_lipschitz pairing entry
      lipschitzConstant rangeRadius pairingLipschitz pairingBounded
  refine ⟨{
    finiteEndpointEquation := finiteEndpointEquation
    finiteWeightedEquation := finiteWeightedEquation
    limit := limit
    subsequence := subsequence
    subsequenceStrict := subsequenceStrict
    pairingConvergence := convergence
    endpointRateConvergence := ?_
    weightedRateConvergence := ?_ }⟩
  · intro test time timeMem
    have uniformConvergence :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
        (convergence test)
    have endpointConvergence :=
      (uniformConvergence.tendsto_at ⟨time, timeMem⟩).sub
        (uniformConvergence.tendsto_at
          ⟨timeStart, left_mem_Icc.mpr timeOrder⟩)
    apply endpointConvergence.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦
      (finiteEndpointEquation (subsequence sequenceIndex) test time
        timeMem).symm
  · intro test weight weightRegular
    exact weightedRateIntegral_tendsto_of_boundedContinuousPairing
      timeOrder
      (fun sequenceIndex ↦ pairing (subsequence sequenceIndex) test)
      (fun sequenceIndex ↦ rate (subsequence sequenceIndex) test)
      (limit test) (convergence test) weight weightRegular
      (fun sequenceIndex ↦ finiteWeightedEquation
        (subsequence sequenceIndex) test weight weightRegular)

end

end SaturationMonoid.PhysicsCore.StageNineCountableWeakPairingCompactness
