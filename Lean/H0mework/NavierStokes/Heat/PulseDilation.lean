import H0mework.NavierStokes.SourceAction.TemporalActionCompression
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
open scoped Topology ENNReal InnerProductSpace

namespace SaturationMonoid.NavierStokes.NativeHeatPulseDilation

open Set Filter MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def scalar (rate time : ℝ) : ℝ := Real.sqrt (2 * rate) * Real.exp (-rate * time)

theorem scalar_sq (rate : ℝ) (positive : 0 < rate) (time : ℝ) :
    scalar rate time ^ 2 = (2 * rate) * Real.exp ((-2 * rate) * time) := by
  rw [scalar, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 * rate), pow_two, ← Real.exp_add]
  congr 2
  ring

theorem scalar_sq_integrable (rate : ℝ) (positive : 0 < rate) :
    IntegrableOn (fun time => scalar rate time ^ 2) (Ici (0 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  change Integrable (fun time => scalar rate time ^ 2) (volume.restrict (Ioi (0 : ℝ)))
  simp_rw [scalar_sq rate positive]
  exact (integrableOn_exp_mul_Ioi (by linarith : -2 * rate < 0) 0).const_mul (2 * rate)

theorem scalar_normalized (rate : ℝ) (positive : 0 < rate) :
    (∫ time in Ici (0 : ℝ), scalar rate time ^ 2) = 1 := by
  simp_rw [scalar_sq rate positive]
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -2 * rate < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Ambient (E : Type*) [NormedAddCommGroup E] := Lp E 2 (volume : Measure ℝ)

def causal (rate : ℝ) (value : E) : ℝ → E :=
  (Ici (0 : ℝ)).indicator (fun time => scalar rate time • value)

omit [CompleteSpace E] in
theorem pulse_paid (rate : ℝ) (positive : 0 < rate) (value : E) : MemLp (causal rate value) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Ici).mpr
  have measurable : AEStronglyMeasurable (fun time => scalar rate time • value) (volume.restrict (Ici (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold scalar
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm measurable).mpr
  have raw := (scalar_sq_integrable rate positive).mul_const (‖value‖ ^ 2)
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using raw

def lift (rate : ℝ) (positive : 0 < rate) (value : E) : Ambient E :=
  (pulse_paid rate positive value).toLp (causal rate value)

omit [CompleteSpace E] in
theorem lift_ae (rate : ℝ) (positive : 0 < rate) (value : E) :
    lift rate positive value =ᵐ[volume] causal rate value := MemLp.coeFn_toLp _

omit [CompleteSpace E] in
theorem lift_inner (rate : ℝ) (positive : 0 < rate) (left right : E) :
    inner ℂ (lift rate positive left) (lift rate positive right) = inner ℂ left right := by
  rw [L2.inner_def]
  calc
    _ = ∫ time, (Ici (0 : ℝ)).indicator (fun time => (scalar rate time ^ 2) • inner ℂ left right) time := by
      apply integral_congr_ae
      filter_upwards [lift_ae rate positive left, lift_ae rate positive right] with time leftRead rightRead
      rw [leftRead, rightRead]
      by_cases nonnegative : 0 ≤ time
      · simp only [causal, indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative), pow_two]
        rw [← IsScalarTower.algebraMap_smul ℂ (scalar rate time) left,
          ← IsScalarTower.algebraMap_smul ℂ (scalar rate time) right,
          inner_smul_real_left, inner_smul_real_right, smul_smul]
      · simp only [causal, indicator_of_notMem (show time ∉ Ici (0 : ℝ) from nonnegative), inner_zero_left]
    _ = (∫ time in Ici (0 : ℝ), scalar rate time ^ 2) • inner ℂ left right := by
      rw [integral_indicator measurableSet_Ici, integral_smul_const]
    _ = _ := by rw [scalar_normalized rate positive, one_smul]

omit [CompleteSpace E] in
theorem lift_norm (rate : ℝ) (positive : 0 < rate) (value : E) : ‖lift rate positive value‖ = ‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), lift_inner, norm_sq_eq_re_inner (𝕜 := ℂ)]

def embed (rate : ℝ) (positive : 0 < rate) : E →ₗᵢ[ℂ] Ambient E where
  toFun := lift rate positive
  map_add' left right := by
    apply Lp.ext
    filter_upwards [lift_ae rate positive (left + right), lift_ae rate positive left, lift_ae rate positive right,
      Lp.coeFn_add (lift rate positive left) (lift rate positive right)] with time total first second addition
    rw [addition, total]
    simp only [Pi.add_apply]
    rw [first, second]
    by_cases nonnegative : 0 ≤ time
    · simp only [causal, indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative), smul_add]
    · simp only [causal, indicator_of_notMem (show time ∉ Ici (0 : ℝ) from nonnegative), add_zero]
  map_smul' coefficient value := by
    apply Lp.ext
    filter_upwards [lift_ae rate positive (coefficient • value), lift_ae rate positive value,
      Lp.coeFn_smul coefficient (lift rate positive value)] with time total initial scaling
    simp only [RingHom.id_apply]
    rw [scaling, total]
    simp only [Pi.smul_apply]
    rw [initial]
    by_cases nonnegative : 0 ≤ time
    · simp only [causal, indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative)]
      exact smul_comm _ _ _
    · simp only [causal, indicator_of_notMem (show time ∉ Ici (0 : ℝ) from nonnegative), smul_zero]
  norm_map' value := lift_norm rate positive value

def read (rate : ℝ) (positive : 0 < rate) : Ambient E →L[ℂ] E :=
  (embed (E := E) rate positive).toContinuousLinearMap.adjoint

theorem read_embed (rate : ℝ) (positive : 0 < rate) (value : E) :
    read rate positive (embed rate positive value) = value :=
  congrArg (fun operator : E →L[ℂ] E => operator value) (embed (E := E) rate positive).adjoint_comp_self


theorem read_norm_le (rate : ℝ) (positive : 0 < rate) (value : Ambient E) :
    ‖read (E := E) rate positive value‖ ≤ ‖value‖ := by
  have normEq : ‖read (E := E) rate positive‖ = ‖(embed (E := E) rate positive).toContinuousLinearMap‖ :=
    ContinuousLinearMap.adjoint.norm_map ((embed (E := E) rate positive).toContinuousLinearMap)
  have operatorBound : ‖read (E := E) rate positive‖ ≤ 1 :=
    normEq.trans_le (embed (E := E) rate positive).norm_toContinuousLinearMap_le
  have bound := mul_le_mul_of_nonneg_right operatorBound (norm_nonneg value)
  simpa only [one_mul] using ((read (E := E) rate positive).le_opNorm value).trans bound

open NativeTemporalActionCompression SourceGeneratedCompressedUnitaryDefectPort

local instance : CompleteSpace (futureSpace E).toSubmodule :=
  (futureSpace E).isClosed.isComplete.completeSpace_coe

def futureEmbedding (rate : ℝ) (positive : 0 < rate) : E →ₗᵢ[ℂ] (futureSpace E).toSubmodule where
  toFun value := ⟨embed rate positive value, (mem_future_iff E _).mpr (by
    filter_upwards [lift_ae rate positive value] with time same negative
    change (lift rate positive value) time = 0
    rw [same, causal, indicator_of_notMem (show time ∉ Ici (0 : ℝ) from not_le.mpr negative)])⟩
  map_add' left right := Subtype.ext ((embed rate positive).map_add left right)
  map_smul' coefficient value := Subtype.ext ((embed rate positive).map_smul coefficient value)
  norm_map' value := (embed rate positive).norm_map value

theorem scalar_shift (rate time advance : ℝ) :
    scalar rate (time + advance) = Real.exp (-rate * advance) * scalar rate time := by
  simp only [scalar, mul_add, Real.exp_add]
  ring

theorem compression_heat (rate : ℝ) (positive : 0 < rate) (advance : ℝ) (nonnegative : 0 ≤ advance) (value : E) :
    compression (futureSpace E) (translation E advance) (futureEmbedding rate positive value) =
      futureEmbedding rate positive (Real.exp (-rate * advance) • value) := by
  apply compression_eq_next E advance
  have shifted := (measurePreserving_add_right (volume : Measure ℝ) advance).quasiMeasurePreserving.ae
    (lift_ae rate positive value)
  filter_upwards [shifted, lift_ae rate positive (Real.exp (-rate * advance) • value)] with time original target nonnegativeTime
  change (lift rate positive value) (time + advance) = (lift rate positive (Real.exp (-rate * advance) • value)) time
  rw [original, target]
  simp only [causal, indicator_of_mem (show time + advance ∈ Ici (0 : ℝ) from add_nonneg nonnegativeTime nonnegative),
    indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegativeTime), scalar_shift, smul_smul, mul_comm]

theorem read_compression (rate : ℝ) (positive : 0 < rate) (advance : ℝ) (nonnegative : 0 ≤ advance) (value : E) :
    read rate positive (compression (futureSpace E) (translation E advance) (futureEmbedding rate positive value) : Ambient E) =
      Real.exp (-rate * advance) • value := by
  rw [compression_heat rate positive advance nonnegative]
  exact read_embed rate positive _

theorem external_energy (rate : ℝ) (positive : 0 < rate) (advance : ℝ) (nonnegative : 0 ≤ advance) (value : E) :
    ‖externalDefect (futureSpace E) (translation E advance) (futureEmbedding rate positive value)‖ ^ 2 =
      (1 - Real.exp (-2 * rate * advance)) * ‖value‖ ^ 2 := by
  have account := norm_sq_compression_add_externalDefect (futureSpace E) (translation E advance)
    (futureEmbedding rate positive value)
  rw [compression_heat rate positive advance nonnegative, (futureEmbedding rate positive).norm_map,
    (futureEmbedding rate positive).norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow] at account
  have squared : Real.exp (-rate * advance) ^ 2 = Real.exp (-2 * rate * advance) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [squared] at account
  linarith

omit [CompleteSpace E] in
theorem translation_inverse (advance : ℝ) (field : Ambient E) :
    translation E (-advance) (translation E advance field) = field := by
  apply Lp.ext
  have shifted := (measurePreserving_add_right (volume : Measure ℝ) (-advance)).quasiMeasurePreserving.ae
    (translation_ae E advance field)
  filter_upwards [translation_ae E (-advance) (translation E advance field), shifted] with time outer inner
  rw [outer, inner]
  congr 1
  ring

def unitary (advance : ℝ) : Ambient E ≃ₗᵢ[ℂ] Ambient E :=
  LinearIsometryEquiv.ofLinearIsometry (translation E advance) (translation E (-advance)).toLinearMap
    (by
      apply LinearMap.ext
      intro field
      change translation E advance (translation E (-advance) field) = field
      simpa only [neg_neg] using translation_inverse (-advance) field)
    (by
      apply LinearMap.ext
      intro field
      exact translation_inverse advance field)


theorem read_external_zero (rate : ℝ) (positive : 0 < rate) (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    read rate positive (externalDefect (futureSpace E) (translation E advance) field : Ambient E) = 0 := by
  apply ext_inner_left ℂ
  intro test
  rw [inner_zero_right]
  change inner ℂ test ((embed (E := E) rate positive).toContinuousLinearMap.adjoint
    (externalDefect (futureSpace E) (translation E advance) field : Ambient E)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.inner_right_of_mem_orthogonal (futureEmbedding rate positive test).property
    (externalDefect (futureSpace E) (translation E advance) field).property

theorem read_translation (rate : ℝ) (positive : 0 < rate) (advance : ℝ) (nonnegative : 0 ≤ advance) (value : E) :
    read rate positive (translation E advance (embed rate positive value)) = Real.exp (-rate * advance) • value := by
  have whole := compression_add_externalDefect (futureSpace E) (translation E advance) (futureEmbedding rate positive value)
  have observed := congrArg (read rate positive) whole
  rw [map_add, read_compression rate positive advance nonnegative, read_external_zero, add_zero] at observed
  exact observed.symm

end
end SaturationMonoid.NavierStokes.NativeHeatPulseDilation
