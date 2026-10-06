import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCutoffTimeGraph
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceFamilyLinearMap

/-! Original finite-C_F retarded integrals are generated before the source-family limit. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FullYSourceFiniteTimeIntegral
open MeasureTheory Filter SourceFiniteUnitary
open scoped Topology InnerProductSpace
open FullYSourceCutoffTimeGraph

section Finite
variable {α E : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (τ : α → ℝ) (hτ : Measurable τ)
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem time_continuous : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

include hC hτ in
theorem row_memLp (x : E) : MemLp (fun t => time C (τ t) x) 2 μ :=
  MemLp.of_bound
    (((time_continuous C).comp_aestronglyMeasurable hτ.aestronglyMeasurable).apply_continuousLinearMap x)
    ‖x‖ (Filter.Eventually.of_forall (fun t => (time_norm C hC (τ t) x).le))

def rowLinear : E →ₗ[ℂ] Lp E 2 μ where
  toFun x := (row_memLp μ C hC τ hτ x).toLp (fun t => time C (τ t) x)
  map_add' x y := by
    apply Lp.ext
    filter_upwards [(row_memLp μ C hC τ hτ (x+y)).coeFn_toLp,
      (row_memLp μ C hC τ hτ x).coeFn_toLp,(row_memLp μ C hC τ hτ y).coeFn_toLp,
      Lp.coeFn_add ((row_memLp μ C hC τ hτ x).toLp _) ((row_memLp μ C hC τ hτ y).toLp _)]
      with t hxy hx hy hadd
    change ((row_memLp μ C hC τ hτ (x+y)).toLp _) t=
      (((row_memLp μ C hC τ hτ x).toLp _)+((row_memLp μ C hC τ hτ y).toLp _)) t
    rw [hxy,hadd,Pi.add_apply,hx,hy,map_add]
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [(row_memLp μ C hC τ hτ (c • x)).coeFn_toLp,
      (row_memLp μ C hC τ hτ x).coeFn_toLp,
      Lp.coeFn_smul c ((row_memLp μ C hC τ hτ x).toLp _)] with t hcx hx hsmul
    change ((row_memLp μ C hC τ hτ (c • x)).toLp _) t=
      (c • ((row_memLp μ C hC τ hτ x).toLp _)) t
    rw [hcx,hsmul,Pi.smul_apply,hx,map_smul]

theorem row_square (x : E) :
    ‖rowLinear μ C hC τ hτ x‖^2=(μ Set.univ).toReal*‖x‖^2 := by
  rw [square_integral]
  calc
    _ = ∫ _ : α, ‖x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [(row_memLp μ C hC τ hτ x).coeFn_toLp] with t ht
      change ‖((row_memLp μ C hC τ hτ x).toLp _) t‖^2=_
      rw [ht,time_norm C hC]
    _ = _ := by simp [Measure.real,smul_eq_mul]

theorem row_bound (x : E) :
    ‖rowLinear μ C hC τ hτ x‖ ≤ Real.sqrt (μ Set.univ).toReal*‖x‖ := by
  have he := row_square μ C hC τ hτ x
  have hs := Real.sq_sqrt (ENNReal.toReal_nonneg (a := μ Set.univ))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  rw [mul_pow,hs,he]

def row : E →L[ℂ] Lp E 2 μ :=
  (rowLinear μ C hC τ hτ).mkContinuous (Real.sqrt (μ Set.univ).toReal)
    (row_bound μ C hC τ hτ)

def retardedIntegral : Lp E 2 μ →L[ℂ] E := (row μ C hC τ hτ).adjoint

theorem integral_bound (ψ : Lp E 2 μ) :
    ‖retardedIntegral μ C hC τ hτ ψ‖ ≤ Real.sqrt (μ Set.univ).toReal*‖ψ‖ := by
  have hr : ‖row μ C hC τ hτ‖ ≤ Real.sqrt (μ Set.univ).toReal :=
    (row μ C hC τ hτ).opNorm_le_bound (Real.sqrt_nonneg _) (row_bound μ C hC τ hτ)
  have hi : ‖retardedIntegral μ C hC τ hτ‖ ≤ Real.sqrt (μ Set.univ).toReal := by
    change ‖(row μ C hC τ hτ).adjoint‖ ≤ _
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hr
  exact ((retardedIntegral μ C hC τ hτ).le_opNorm ψ).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg ψ))

theorem integral_pair (ψ : Lp E 2 μ) (x : E) :
    inner ℂ x (retardedIntegral μ C hC τ hτ ψ)=
      ∫ t, inner ℂ (time C (τ t) x) (ψ t) ∂μ := by
  rw [retardedIntegral,ContinuousLinearMap.adjoint_inner_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(row_memLp μ C hC τ hτ x).coeFn_toLp] with t ht
  change inner ℂ (((row_memLp μ C hC τ hτ x).toLp _) t) (ψ t)=_
  rw [ht]

include hC hτ in
theorem kernel_integrable (ψ : Lp E 2 μ) :
    Integrable (fun t => time C (-τ t) (ψ t)) μ := by
  have hm : AEStronglyMeasurable (fun t => time C (-τ t)) μ :=
    (time_continuous C).comp_aestronglyMeasurable hτ.neg.aestronglyMeasurable
  have hp : MemLp (fun t => time C (-τ t) (ψ t)) 2 μ :=
    (Lp.memLp ψ).congr_norm
      ((ContinuousLinearMap.apply ℂ E).aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable ψ) hm)
      (Filter.Eventually.of_forall (fun t => (time_norm C hC (-τ t) (ψ t)).symm))
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hp

theorem integral_return (ψ : Lp E 2 μ) :
    retardedIntegral μ C hC τ hτ ψ=∫ t, time C (-τ t) (ψ t) ∂μ := by
  apply ext_inner_left ℂ
  intro x
  rw [integral_pair,← integral_inner (𝕜 := ℂ) (kernel_integrable μ C hC τ hτ ψ) x]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have ht : (time C (τ t)).adjoint=time C (-τ t) := by
    rw [FullYSourceCutoffVolterra.time_adjoint,hC.adjoint_eq]
  change inner ℂ (time C (τ t) x) (ψ t)=inner ℂ x (time C (-τ t) (ψ t))
  rw [←ht,ContinuousLinearMap.adjoint_inner_right]

end Finite

open GaussCoreHilbert
open GaussUnitaryHistory (HistorySpace sourceFilter Index)
open SourceFamilyHilbert

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (τ : α → ℝ) (hτ : Measurable τ)

abbrev TimeSpace := Hilbert (Lp H 2 μ) sourceFilter

def sourceIntegral : TimeSpace μ →L[ℂ] HistorySpace :=
  FullYSourceFamilyLinearMap.lift sourceFilter
    (fun F => retardedIntegral μ (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) τ hτ)
    (Real.sqrt (μ Set.univ).toReal) (Real.sqrt_nonneg _)
    (fun F => integral_bound μ (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) τ hτ)

theorem source_integral_bound (ψ : TimeSpace μ) :
    ‖sourceIntegral μ τ hτ ψ‖ ≤ Real.sqrt (μ Set.univ).toReal*‖ψ‖ :=
  FullYSourceFamilyLinearMap.lift_bound _ _ _ _ _ ψ

theorem source_integral_limit (ψ : ℕ → TimeSpace μ) (y : TimeSpace μ)
    (h : Tendsto ψ atTop (𝓝 y)) :
    Tendsto (fun n => sourceIntegral μ τ hτ (ψ n)) atTop (𝓝 (sourceIntegral μ τ hτ y)) :=
  (sourceIntegral μ τ hτ).continuous.tendsto y |>.comp h

#print axioms integral_pair
#print axioms integral_return
#print axioms source_integral_bound
end LowEnergy.FullYSourceFiniteTimeIntegral
