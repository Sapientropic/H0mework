import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Canonical maximal multiplication on an Lp carrier

A fixed pointwise multiplier generates a partial operator on `Lp`: its graph
contains exactly the input/output pairs satisfying the multiplication law
almost everywhere.  The graph is closed, hence determines a unique closed
and closable `LinearPMap`.  Its domain is exactly the inputs whose multiplied
representative is still in `Lp`; no boundedness premise is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace GenericFoundation
namespace Analysis
namespace MaximalLpMultiplication

open Filter MeasureTheory Set Topology

open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

abbrev Carrier (p : ℝ≥0∞) (measure : Measure α) :=
  Lp ℂ p measure

def graph (p : ℝ≥0∞) (measure : Measure α)
    (multiplier : α → ℂ) :
    Submodule ℂ (Carrier p measure × Carrier p measure) where
  carrier := {pair | ∀ᵐ x ∂measure,
    pair.2 x = multiplier x * pair.1 x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ p measure] with x zeroAt
    change ((0 : Carrier p measure) : α → ℂ) x =
      multiplier x * ((0 : Carrier p measure) : α → ℂ) x
    rw [zeroAt]
    simp
  add_mem' {first second} firstMem secondMem := by
    filter_upwards [firstMem, secondMem,
      Lp.coeFn_add first.1 second.1,
      Lp.coeFn_add first.2 second.2]
      with x firstAt secondAt inputAddAt outputAddAt
    rw [Prod.fst_add, Prod.snd_add, outputAddAt, inputAddAt,
      Pi.add_apply, Pi.add_apply, firstAt, secondAt, mul_add]
  smul_mem' scalar pair pairMem := by
    filter_upwards [pairMem, Lp.coeFn_smul scalar pair.1,
      Lp.coeFn_smul scalar pair.2]
      with x pairAt inputSmulAt outputSmulAt
    change (scalar • pair.2 : Carrier p measure) x =
      multiplier x * (scalar • pair.1 : Carrier p measure) x
    rw [outputSmulAt, inputSmulAt, Pi.smul_apply, Pi.smul_apply, pairAt]
    ring

theorem graph_vertical
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ)
    (output : Carrier p measure)
    (mem : (0, output) ∈ graph p measure multiplier) : output = 0 := by
  apply Lp.ext
  filter_upwards [mem, Lp.coeFn_zero ℂ p measure]
    with x relation zeroAt
  rw [zeroAt]
  rw [zeroAt] at relation
  simpa using relation

def operator (p : ℝ≥0∞) (measure : Measure α)
    (multiplier : α → ℂ) :
    Carrier p measure →ₗ.[ℂ] Carrier p measure :=
  (graph p measure multiplier).toLinearPMap

theorem operator_graph
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ) :
    (operator p measure multiplier).graph = graph p measure multiplier := by
  exact Submodule.toLinearPMap_graph_eq (graph p measure multiplier)
    (fun pair mem firstZero => by
      apply graph_vertical p measure multiplier pair.2
      have pairEq : pair = (0, pair.2) := Prod.ext firstZero rfl
      rw [← pairEq]
      exact mem)

theorem graph_isClosed
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (measure : Measure α) (multiplier : α → ℂ) :
    IsClosed (graph p measure multiplier :
      Set (Carrier p measure × Carrier p measure)) := by
  apply IsSeqClosed.isClosed
  intro sequence limit sequenceMem sequenceTendsto
  have inputTendsto :
      Tendsto (fun n => (sequence n).1) atTop (𝓝 limit.1) :=
    (continuous_fst.tendsto limit).comp sequenceTendsto
  have outputTendsto :
      Tendsto (fun n => (sequence n).2) atTop (𝓝 limit.2) :=
    (continuous_snd.tendsto limit).comp sequenceTendsto
  obtain ⟨inputSubsequence, inputStrict, inputAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp inputTendsto).exists_seq_tendsto_ae
  have outputAlongInput :
      Tendsto (fun n => (sequence (inputSubsequence n)).2)
        atTop (𝓝 limit.2) :=
    outputTendsto.comp inputStrict.tendsto_atTop
  obtain ⟨outputSubsequence, outputStrict, outputAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp outputAlongInput).exists_seq_tendsto_ae
  have inputDoubleAE :
      ∀ᵐ x ∂measure,
        Tendsto (fun n => (sequence
          (inputSubsequence (outputSubsequence n))).1 x)
          atTop (𝓝 (limit.1 x)) := by
    filter_upwards [inputAE] with x convergence
    exact convergence.comp outputStrict.tendsto_atTop
  have relationAE :
      ∀ᵐ x ∂measure, ∀ n : Nat,
        (sequence (inputSubsequence (outputSubsequence n))).2 x =
          multiplier x *
            (sequence (inputSubsequence (outputSubsequence n))).1 x :=
    ae_all_iff.2 fun n =>
      sequenceMem (inputSubsequence (outputSubsequence n))
  filter_upwards [inputDoubleAE, outputAE, relationAE]
    with x inputAt outputAt relationAt
  have multipliedInputAt :
      Tendsto (fun n => multiplier x *
          (sequence (inputSubsequence (outputSubsequence n))).1 x)
        atTop (𝓝 (multiplier x * limit.1 x)) :=
    tendsto_const_nhds.mul inputAt
  exact tendsto_nhds_unique outputAt
    (multipliedInputAt.congr'
      (Eventually.of_forall fun n => (relationAt n).symm))

theorem operator_isClosed
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (measure : Measure α) (multiplier : α → ℂ) :
    (operator p measure multiplier).IsClosed := by
  rw [LinearPMap.IsClosed, operator_graph]
  exact graph_isClosed p measure multiplier

theorem operator_apply_ae
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ)
    (value : (operator p measure multiplier).domain) :
    ∀ᵐ x ∂measure,
      operator p measure multiplier value x =
        multiplier x * value.1 x := by
  have graphMem := LinearPMap.mem_graph
    (operator p measure multiplier) value
  rw [operator_graph] at graphMem
  exact graphMem

theorem mem_operator_domain_iff
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ)
    (value : Carrier p measure) :
    value ∈ (operator p measure multiplier).domain ↔
      MemLp (fun x : α => multiplier x * value x) p measure := by
  constructor
  · intro mem
    let domainValue : (operator p measure multiplier).domain := ⟨value, mem⟩
    exact (memLp_congr_ae
      (operator_apply_ae p measure multiplier domainValue)).mp
      (Lp.memLp (operator p measure multiplier domainValue))
  · intro productMem
    let output : Carrier p measure :=
      productMem.toLp (fun x : α => multiplier x * value x)
    have outputAE :
        ∀ᵐ x ∂measure, output x = multiplier x * value x :=
      productMem.coeFn_toLp
    have graphMem :
        (value, output) ∈ (operator p measure multiplier).graph := by
      rw [operator_graph]
      exact outputAE
    exact LinearPMap.mem_domain_of_mem_graph graphMem

theorem not_mem_operator_domain_iff
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ)
    (value : Carrier p measure) :
    value ∉ (operator p measure multiplier).domain ↔
      ¬ MemLp (fun x : α => multiplier x * value x) p measure := by
  exact not_congr (mem_operator_domain_iff p measure multiplier value)

/-- Universal property of the maximal multiplication operator: every partial
linear map with the same almost-everywhere action law is its restriction. -/
theorem le_operator_of_apply_ae
    (p : ℝ≥0∞) (measure : Measure α) (multiplier : α → ℂ)
    (candidate : Carrier p measure →ₗ.[ℂ] Carrier p measure)
    (actionLaw : ∀ value : candidate.domain,
      ∀ᵐ x ∂measure,
        candidate value x = multiplier x * value.1 x) :
    candidate ≤ operator p measure multiplier := by
  refine ⟨?_, ?_⟩
  · intro value mem
    exact (mem_operator_domain_iff p measure multiplier value).2
      ((memLp_congr_ae (actionLaw ⟨value, mem⟩)).mp
        (Lp.memLp (candidate ⟨value, mem⟩)))
  · intro source target source_eq_target
    apply Lp.ext
    filter_upwards [actionLaw source,
      operator_apply_ae p measure multiplier target]
      with x sourceAt targetAt
    rw [sourceAt, targetAt, source_eq_target]

theorem operator_isClosable
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (measure : Measure α) (multiplier : α → ℂ) :
    (operator p measure multiplier).IsClosable :=
  (operator_isClosed p measure multiplier).isClosable

end
end MaximalLpMultiplication
end Analysis
end GenericFoundation
end SaturationMonoid
