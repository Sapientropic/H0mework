import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Generated weak-limit actualization

A bounded linear weak functional on a dense generated test carrier extends
canonically to the ambient Hilbert carrier.  Fréchet--Riesz then turns that
extension into its unique representative.  This file supplies only that
transporter and its independence receipt; it does not generate a weak
functional or a physical equation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGeneratedWeakLimitActualization

open Filter Set

noncomputable section

set_option autoImplicit false

variable {Test Hilbert : Type*}
variable [AddCommGroup Test] [Module ℝ Test]
variable [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

/-- Convergence on a countable generating family extends to its entire
algebraic span.  The output is still only the generated pointwise limit; no
ambient representative or equation is selected here. -/
theorem exists_pointwiseLimitOnSpan_of_generatorConvergence
    (generator : ℕ → Test)
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (generatorLimit : ℕ → ℝ)
    (generatorConvergence : ∀ index,
      Tendsto
        (fun sequenceIndex ↦
          functional (subsequence sequenceIndex) (generator index))
        atTop (nhds (generatorLimit index))) :
    ∃ limit : Submodule.span ℝ (Set.range generator) → ℝ,
      ∀ test,
        Tendsto
          (fun sequenceIndex ↦
            functional (subsequence sequenceIndex) test.1)
          atTop (nhds (limit test)) := by
  have limitExists : ∀ test : Test,
      test ∈ Submodule.span ℝ (Set.range generator) →
        ∃ value : ℝ,
          Tendsto
            (fun sequenceIndex ↦
              functional (subsequence sequenceIndex) test)
            atTop (nhds value) := by
    intro test testMem
    induction testMem using Submodule.span_induction with
    | mem test testMem =>
        obtain ⟨index, rfl⟩ := testMem
        exact ⟨generatorLimit index, generatorConvergence index⟩
    | zero =>
        refine ⟨0, ?_⟩
        simp
    | add first second _ _ firstLimit secondLimit =>
        obtain ⟨firstValue, firstConvergence⟩ := firstLimit
        obtain ⟨secondValue, secondConvergence⟩ := secondLimit
        refine ⟨firstValue + secondValue, ?_⟩
        simpa using firstConvergence.add secondConvergence
    | smul parameter test _ testLimit =>
        obtain ⟨value, convergence⟩ := testLimit
        refine ⟨parameter • value, ?_⟩
        simpa using convergence.const_smul parameter
  choose limit convergence using fun test :
    Submodule.span ℝ (Set.range generator) ↦ limitExists test.1 test.2
  exact ⟨limit, convergence⟩

/-- Pointwise convergence of finite linear reads on one common subsequence
produces the exact algebraic limit functional. -/
def pointwiseLimitLinearMap
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limit : Test → ℝ)
    (convergence : ∀ test,
      Filter.Tendsto
        (fun sequenceIndex ↦ functional (subsequence sequenceIndex) test)
        Filter.atTop (nhds (limit test))) : Test →ₗ[ℝ] ℝ where
  toFun := limit
  map_add' first second := by
    apply tendsto_nhds_unique (convergence (first + second))
    simpa using (convergence first).add (convergence second)
  map_smul' parameter test := by
    apply tendsto_nhds_unique (convergence (parameter • test))
    simpa using (convergence test).const_smul parameter

@[simp] theorem pointwiseLimitLinearMap_apply
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limit : Test → ℝ)
    (convergence : ∀ test,
      Filter.Tendsto
        (fun sequenceIndex ↦ functional (subsequence sequenceIndex) test)
        Filter.atTop (nhds (limit test)))
    (test : Test) :
    pointwiseLimitLinearMap functional subsequence limit convergence test =
      limit test :=
  rfl

omit [CompleteSpace Hilbert] in
/-- A uniform source-side norm estimate passes to the pointwise limit
functional. -/
theorem pointwiseLimitLinearMap_bound
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limit : Test → ℝ)
    (convergence : ∀ test,
      Filter.Tendsto
        (fun sequenceIndex ↦ functional (subsequence sequenceIndex) test)
        Filter.atTop (nhds (limit test)))
    (bound : ℝ)
    (uniformBound : ∀ approximation test,
      ‖functional approximation test‖ ≤ bound * ‖testEmbedding test‖)
    (test : Test) :
    ‖pointwiseLimitLinearMap functional subsequence limit convergence test‖ ≤
      bound * ‖testEmbedding test‖ := by
  apply le_of_tendsto (continuous_norm.tendsto _ |>.comp (convergence test))
  exact Filter.Eventually.of_forall fun sequenceIndex ↦
    uniformBound (subsequence sequenceIndex) test

/-- Canonical extension of a generated functional from its dense test
carrier to the ambient Hilbert carrier. -/
def denseTestFunctionalExtension
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ) : Hilbert →L[ℝ] ℝ :=
  functional.extendOfNorm testEmbedding

/-- Fréchet--Riesz actualization of the canonically extended weak
functional. -/
def denseTestRieszActualization
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ) : Hilbert :=
  (InnerProductSpace.toDual ℝ Hilbert).symm
    (denseTestFunctionalExtension testEmbedding functional)

/-- Canonical Hilbert representative generated directly from one common
subsequence of finite linear reads. -/
def pointwiseLimitRieszActualization
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limit : Test → ℝ)
    (convergence : ∀ test,
      Filter.Tendsto
        (fun sequenceIndex ↦ functional (subsequence sequenceIndex) test)
        Filter.atTop (nhds (limit test))) : Hilbert :=
  denseTestRieszActualization testEmbedding
    (pointwiseLimitLinearMap functional subsequence limit convergence)

/-- On every generated test, the Riesz representative reads back the exact
input functional. -/
theorem denseTestRieszActualization_pairing
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ)
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (functionalBound : ∀ test,
      ‖functional test‖ ≤ bound * ‖testEmbedding test‖)
    (test : Test) :
    inner ℝ (denseTestRieszActualization testEmbedding functional)
        (testEmbedding test) =
      functional test := by
  rw [denseTestRieszActualization,
    InnerProductSpace.toDual_symm_apply,
    denseTestFunctionalExtension,
    LinearMap.extendOfNorm_eq testDense ⟨bound, functionalBound⟩]

/-- The generated norm bound survives dense extension and Riesz
actualization. -/
theorem norm_denseTestRieszActualization_le
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ)
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (functionalBound : ∀ test,
      ‖functional test‖ ≤ bound * ‖testEmbedding test‖) :
    ‖denseTestRieszActualization testEmbedding functional‖ ≤ bound := by
  rw [denseTestRieszActualization,
    (InnerProductSpace.toDual ℝ Hilbert).symm.norm_map]
  exact LinearMap.opNorm_extendOfNorm_le testDense boundNonnegative
    functionalBound

/-- Pairing agreement on the exact dense test carrier fixes the authoritative
representative uniquely. -/
theorem denseTestRieszActualization_unique
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ)
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (functionalBound : ∀ test,
      ‖functional test‖ ≤ bound * ‖testEmbedding test‖)
    (candidate : Hilbert)
    (candidatePairing : ∀ test,
      inner ℝ candidate (testEmbedding test) = functional test) :
    candidate = denseTestRieszActualization testEmbedding functional := by
  apply testDense.eq_of_inner_left ℝ
  intro test
  rw [candidatePairing]
  exact (denseTestRieszActualization_pairing testEmbedding functional
    testDense bound functionalBound test).symm

/-- The common-subsequence limit generates one representative whose dense
test pairings are the prescribed limits, and those pairings determine it
uniquely. -/
theorem pointwiseLimitRieszActualization_spec
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limit : Test → ℝ)
    (convergence : ∀ test,
      Filter.Tendsto
        (fun sequenceIndex ↦ functional (subsequence sequenceIndex) test)
        Filter.atTop (nhds (limit test)))
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (uniformBound : ∀ approximation test,
      ‖functional approximation test‖ ≤ bound * ‖testEmbedding test‖) :
    (∀ test,
      inner ℝ
          (pointwiseLimitRieszActualization testEmbedding functional
            subsequence limit convergence)
          (testEmbedding test) =
        limit test) ∧
      ∀ candidate : Hilbert,
        (∀ test, inner ℝ candidate (testEmbedding test) = limit test) →
        candidate = pointwiseLimitRieszActualization testEmbedding functional
          subsequence limit convergence := by
  let limitFunctional :=
    pointwiseLimitLinearMap functional subsequence limit convergence
  have limitFunctionalBound : ∀ test,
      ‖limitFunctional test‖ ≤ bound * ‖testEmbedding test‖ :=
    pointwiseLimitLinearMap_bound testEmbedding functional subsequence limit
      convergence bound uniformBound
  constructor
  · intro test
    simpa [pointwiseLimitRieszActualization, limitFunctional] using
      denseTestRieszActualization_pairing testEmbedding limitFunctional
        testDense bound limitFunctionalBound test
  · intro candidate candidatePairing
    apply denseTestRieszActualization_unique testEmbedding limitFunctional
      testDense bound limitFunctionalBound candidate
    intro test
    simpa [limitFunctional] using candidatePairing test

/-- Generator-wise convergence and one span-uniform estimate directly
produce the canonical Riesz representative.  The conclusion records exact
dense-span pairings, uniqueness, and agreement with every generated limit
coordinate. -/
theorem exists_pointwiseLimitRieszActualization_of_generatorConvergence
    (generator : ℕ → Test)
    (testEmbedding :
      Submodule.span ℝ (Set.range generator) →ₗ[ℝ] Hilbert)
    (functional : ℕ → Test →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (generatorLimit : ℕ → ℝ)
    (generatorConvergence : ∀ index,
      Tendsto
        (fun sequenceIndex ↦
          functional (subsequence sequenceIndex) (generator index))
        atTop (nhds (generatorLimit index)))
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (uniformBound : ∀ approximation
        (test : Submodule.span ℝ (Set.range generator)),
      ‖functional approximation test.1‖ ≤
        bound * ‖testEmbedding test‖) :
    ∃ limit : Submodule.span ℝ (Set.range generator) → ℝ,
      ∃ convergence : ∀ test,
        Tendsto
          (fun sequenceIndex ↦
            functional (subsequence sequenceIndex) test.1)
          atTop (nhds (limit test)),
        let spanFunctional : ℕ →
            Submodule.span ℝ (Set.range generator) →ₗ[ℝ] ℝ :=
          fun approximation ↦
            (functional approximation).comp
              (Submodule.subtype (Submodule.span ℝ (Set.range generator)))
        let representative := pointwiseLimitRieszActualization
          testEmbedding spanFunctional subsequence limit convergence
        (∀ test,
          inner ℝ representative (testEmbedding test) = limit test) ∧
          (∀ candidate : Hilbert,
            (∀ test, inner ℝ candidate (testEmbedding test) = limit test) →
              candidate = representative) ∧
          ∀ index,
            limit ⟨generator index,
              Submodule.subset_span (Set.mem_range_self index)⟩ =
                generatorLimit index := by
  obtain ⟨limit, convergence⟩ :=
    exists_pointwiseLimitOnSpan_of_generatorConvergence generator functional
      subsequence generatorLimit generatorConvergence
  let spanFunctional : ℕ →
      Submodule.span ℝ (Set.range generator) →ₗ[ℝ] ℝ :=
    fun approximation ↦
      (functional approximation).comp
        (Submodule.subtype (Submodule.span ℝ (Set.range generator)))
  have spanUniformBound : ∀ approximation test,
      ‖spanFunctional approximation test‖ ≤
        bound * ‖testEmbedding test‖ := by
    intro approximation test
    exact uniformBound approximation test
  have actualizationSpec := pointwiseLimitRieszActualization_spec
    testEmbedding spanFunctional subsequence limit convergence testDense
    bound spanUniformBound
  refine ⟨limit, convergence, actualizationSpec.1, actualizationSpec.2, ?_⟩
  intro index
  apply tendsto_nhds_unique (convergence
    ⟨generator index,
      Submodule.subset_span (Set.mem_range_self index)⟩)
  exact generatorConvergence index

/-- A norm bound checked on a dense test carrier controls the ambient
Hilbert vector. -/
theorem norm_le_of_inner_bound_on_dense_range
    {Test Hilbert : Type*}
    [AddCommGroup Test] [Module ℝ Test]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert]
    (embedding : Test →ₗ[ℝ] Hilbert)
    (embeddingDense : DenseRange embedding)
    (field : Hilbert)
    (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (testBound : ∀ test,
      ‖inner ℝ field (embedding test)‖ ≤ bound * ‖embedding test‖) :
    ‖field‖ ≤ bound := by
  let functional : Test →ₗ[ℝ] ℝ :=
    (innerSL ℝ field).toLinearMap.comp embedding
  have functionalBound : ∀ test,
      ‖functional test‖ ≤ bound * ‖embedding test‖ := by
    intro test
    exact testBound test
  have extensionEq : functional.extendOfNorm embedding = innerSL ℝ field := by
    apply LinearMap.extendOfNorm_unique embeddingDense bound functionalBound
    rfl
  calc
    ‖field‖ = ‖innerSL ℝ field‖ := (innerSL_apply_norm ℝ field).symm
    _ = ‖functional.extendOfNorm embedding‖ := congrArg norm extensionEq.symm
    _ ≤ bound := LinearMap.opNorm_extendOfNorm_le embeddingDense
      boundNonnegative functionalBound

/-- Uniformly bounded Hilbert vectors that converge against one dense
generated family converge weakly against every ambient test. -/
theorem tendsto_inner_of_dense_generator_of_uniform_norm_bound
    {Hilbert : Type*}
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    (generator : ℕ → Hilbert)
    (generatorDense : DenseRange generator)
    (sequence : ℕ → Hilbert)
    (subsequence : ℕ → ℕ)
    (limit : Hilbert)
    (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (sequenceBound : ∀ index, ‖sequence (subsequence index)‖ ≤ bound)
    (generatorConvergence : ∀ generatorIndex,
      Tendsto
        (fun index ↦ inner ℝ (sequence (subsequence index))
          (generator generatorIndex))
        atTop (nhds (inner ℝ limit (generator generatorIndex)))) :
    ∀ test,
      Tendsto
        (fun index ↦ inner ℝ (sequence (subsequence index)) test)
        atTop (nhds (inner ℝ limit test)) := by
  intro test
  rw [Metric.tendsto_atTop]
  intro ε εPositive
  let scale := bound + ‖limit‖ + 1
  have scalePositive : 0 < scale := by
    dsimp [scale]
    positivity
  let δ := ε / (4 * scale)
  have δPositive : 0 < δ := by
    exact div_pos εPositive (mul_pos (by norm_num) scalePositive)
  obtain ⟨generatorIndex, generatorClose⟩ :=
    generatorDense.exists_dist_lt test δPositive
  obtain ⟨entry, generatorEventually⟩ :=
    Metric.tendsto_atTop.mp (generatorConvergence generatorIndex)
      (ε / 2) (half_pos εPositive)
  refine ⟨entry, ?_⟩
  intro index indexMem
  have middleClose := generatorEventually index indexMem
  have firstDistance :
      dist
          (inner ℝ (sequence (subsequence index)) test)
          (inner ℝ (sequence (subsequence index))
            (generator generatorIndex)) ≤
        bound * δ := by
    rw [Real.dist_eq]
    calc
      |inner ℝ (sequence (subsequence index)) test -
          inner ℝ (sequence (subsequence index))
            (generator generatorIndex)| =
          |inner ℝ (sequence (subsequence index))
            (test - generator generatorIndex)| := by
              rw [inner_sub_right]
      _ ≤ ‖sequence (subsequence index)‖ *
          ‖test - generator generatorIndex‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ bound * δ := by
        apply mul_le_mul (sequenceBound index) ?_ (norm_nonneg _) boundNonnegative
        simpa [dist_eq_norm, dist_comm] using generatorClose.le
  have lastDistance :
      dist
          (inner ℝ limit (generator generatorIndex))
          (inner ℝ limit test) ≤
        ‖limit‖ * δ := by
    rw [Real.dist_eq]
    calc
      |inner ℝ limit (generator generatorIndex) - inner ℝ limit test| =
          |inner ℝ limit (generator generatorIndex - test)| := by
            rw [inner_sub_right]
      _ ≤ ‖limit‖ * ‖generator generatorIndex - test‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖limit‖ * δ := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm, norm_sub_rev] using generatorClose.le)
          (norm_nonneg _)
  have scaleDelta : scale * δ = ε / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt scalePositive]
  have boundDelta : bound * δ ≤ ε / 4 := by
    calc
      bound * δ ≤ scale * δ :=
        mul_le_mul_of_nonneg_right
          (by dsimp [scale]; linarith [norm_nonneg limit]) δPositive.le
      _ = ε / 4 := scaleDelta
  have limitDelta : ‖limit‖ * δ ≤ ε / 4 := by
    calc
      ‖limit‖ * δ ≤ scale * δ :=
        mul_le_mul_of_nonneg_right
          (by dsimp [scale]; linarith) δPositive.le
      _ = ε / 4 := scaleDelta
  calc
    dist (inner ℝ (sequence (subsequence index)) test)
        (inner ℝ limit test) ≤
      dist
          (inner ℝ (sequence (subsequence index)) test)
          (inner ℝ (sequence (subsequence index))
            (generator generatorIndex)) +
        dist
          (inner ℝ (sequence (subsequence index))
            (generator generatorIndex))
          (inner ℝ limit (generator generatorIndex)) +
        dist (inner ℝ limit (generator generatorIndex))
          (inner ℝ limit test) := by
      calc
        _ ≤ dist
              (inner ℝ (sequence (subsequence index)) test)
              (inner ℝ (sequence (subsequence index))
                (generator generatorIndex)) +
            dist
              (inner ℝ (sequence (subsequence index))
                (generator generatorIndex))
              (inner ℝ limit test) := dist_triangle _ _ _
        _ ≤ dist
              (inner ℝ (sequence (subsequence index)) test)
              (inner ℝ (sequence (subsequence index))
                (generator generatorIndex)) +
            (dist
                (inner ℝ (sequence (subsequence index))
                  (generator generatorIndex))
                (inner ℝ limit (generator generatorIndex)) +
              dist (inner ℝ limit (generator generatorIndex))
                (inner ℝ limit test)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left (dist_triangle
              (inner ℝ (sequence (subsequence index))
                (generator generatorIndex))
              (inner ℝ limit (generator generatorIndex))
              (inner ℝ limit test))
              (dist
                (inner ℝ (sequence (subsequence index)) test)
                (inner ℝ (sequence (subsequence index))
                  (generator generatorIndex)))
        _ = _ := by ring
    _ < bound * δ + ε / 2 + ‖limit‖ * δ := by
      linarith
    _ ≤ ε / 4 + ε / 2 + ε / 4 := by
      gcongr
    _ = ε := by ring

/-- The same dense-generator principle for uniformly bounded continuous
linear functionals. -/
theorem tendsto_apply_of_dense_generator_of_uniform_opNorm_bound
    {Hilbert : Type*}
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert]
    (generator : ℕ → Hilbert)
    (generatorDense : DenseRange generator)
    (functional : ℕ → Hilbert →L[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (limitFunctional : Hilbert →L[ℝ] ℝ)
    (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (functionalBound : ∀ index,
      ‖functional (subsequence index)‖ ≤ bound)
    (generatorConvergence : ∀ generatorIndex,
      Tendsto
        (fun index ↦ functional (subsequence index)
          (generator generatorIndex))
        atTop (nhds (limitFunctional (generator generatorIndex)))) :
    ∀ test,
      Tendsto
        (fun index ↦ functional (subsequence index) test)
        atTop (nhds (limitFunctional test)) := by
  let sequence : ℕ → Hilbert := fun index ↦
    (InnerProductSpace.toDual ℝ Hilbert).symm (functional index)
  let limit : Hilbert :=
    (InnerProductSpace.toDual ℝ Hilbert).symm limitFunctional
  have sequenceBound : ∀ index, ‖sequence (subsequence index)‖ ≤ bound := by
    intro index
    simpa [sequence] using functionalBound index
  have innerConvergence : ∀ generatorIndex,
      Tendsto
        (fun index ↦ inner ℝ (sequence (subsequence index))
          (generator generatorIndex))
        atTop (nhds (inner ℝ limit (generator generatorIndex))) := by
    intro generatorIndex
    simpa [sequence, limit, InnerProductSpace.toDual_symm_apply] using
      generatorConvergence generatorIndex
  intro test
  simpa [sequence, limit, InnerProductSpace.toDual_symm_apply] using
    tendsto_inner_of_dense_generator_of_uniform_norm_bound generator
      generatorDense sequence subsequence limit bound boundNonnegative
      sequenceBound innerConvergence test

end

end SaturationMonoid.PhysicsCore.StageNineGeneratedWeakLimitActualization
