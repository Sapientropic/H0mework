import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Phase
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Mean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace Topology ENNReal
local notation "μ" => (volume.restrict (symmetricInterval 1) : Measure ℝ)
local instance finiteUnit : IsFiniteMeasure μ where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)
def c (r : ℝ) : H := burnolRadiusBoundaryCosineState r

theorem sine_norm_le (r x : ℝ) : ‖sineRaw r x‖ ≤ 2 := by
  unfold sineRaw
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [Real.abs_sin_le_one (2*Real.pi*r^2*x)]
theorem sine_memLp (r : ℝ) : MemLp (sineRaw r) 2 μ :=
  (memLp_top_of_bound (by unfold sineRaw;fun_prop) 2
    (Filter.Eventually.of_forall (sine_norm_le r))).mono_exponent (by norm_num)
def s (r : ℝ) : H := (sine_memLp r).toLp (sineRaw r)
theorem c_coe (r : ℝ) : (c r : ℝ→ℂ) =ᵐ[μ] cosineRaw r := burnolRadiusBoundaryCosineState_coe r
theorem s_coe (r : ℝ) : (s r : ℝ→ℂ) =ᵐ[μ] sineRaw r := MemLp.coeFn_toLp (sine_memLp r)

def rawReaction (r : ℝ) : H →L[ℂ] H :=
  (r : ℂ) • (InnerProductSpace.rankOne ℂ (c r) (c r) - InnerProductSpace.rankOne ℂ (s r) (s r))
def centeredReaction (r : ℝ) : H →L[ℂ] H :=
  (r : ℂ) • (InnerProductSpace.rankOne ℂ (Q (c r)) (Q (c r)) - InnerProductSpace.rankOne ℂ (Q (s r)) (Q (s r)))

theorem reaction_coe (r : ℝ) (f : H) :
    (rawReaction r f : ℝ→ℂ) =ᵐ[μ] fun x => ∫ y : ℝ,
      (r : ℂ)*(cosineRaw r x*cosineRaw r y-sineRaw r x*sineRaw r y)*f y ∂μ := by
  have innerC : inner ℂ (c r) f = ∫ y : ℝ,cosineRaw r y*f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [c_coe r] with y read
    rw [read]
    simp only [RCLike.inner_apply,starRingEnd_apply,cosineRaw,burnolRadiusBoundaryCosineRaw]
    rw [Complex.star_def,Complex.conj_ofReal]
    ring
  have innerS : inner ℂ (s r) f = ∫ y : ℝ,sineRaw r y*f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [s_coe r] with y read
    rw [read]
    simp only [RCLike.inner_apply,starRingEnd_apply,sineRaw]
    rw [Complex.star_def,Complex.conj_ofReal]
    ring
  have cInt : Integrable (fun y : ℝ => cosineRaw r y*f y) μ := by
    apply ((burnolUnitState_integrable f).norm.const_mul 2).mono'
    · exact (by unfold cosineRaw burnolRadiusBoundaryCosineRaw;fun_prop : Continuous (cosineRaw r)).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (burnolRadiusBoundaryCosineRaw_norm_le_two r y) (norm_nonneg _)
  have sInt : Integrable (fun y : ℝ => sineRaw r y*f y) μ := by
    apply ((burnolUnitState_integrable f).norm.const_mul 2).mono'
    · exact (by unfold sineRaw;fun_prop : Continuous (sineRaw r)).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (sine_norm_le r y) (norm_nonneg _)
  change ((r : ℂ) • (inner ℂ (c r) f • c r - inner ℂ (s r) f • s r) : H) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul (r : ℂ) (inner ℂ (c r) f • c r-inner ℂ (s r) f • s r),
    Lp.coeFn_sub (inner ℂ (c r) f • c r) (inner ℂ (s r) f • s r),
    Lp.coeFn_smul (inner ℂ (c r) f) (c r),Lp.coeFn_smul (inner ℂ (s r) f) (s r),c_coe r,s_coe r] with x outer sub cScalar sScalar cRead sRead
  rw [outer,Pi.smul_apply,smul_eq_mul,sub,Pi.sub_apply,cScalar,sScalar]
  simp only [Pi.smul_apply,smul_eq_mul,cRead,sRead,innerC,innerS]
  rw [← integral_mul_const,← integral_mul_const]
  rw [← integral_sub (cInt.mul_const (cosineRaw r x)) (sInt.mul_const (sineRaw r x)),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

private theorem profile_continuous (raw : ℝ → ℝ → ℂ) (member : ∀ r, MemLp (raw r) 2 μ)
    (pointwise : ∀ x, Continuous (fun r : ℝ => raw r x)) (bound : ∀ r x, ‖raw r x‖ ≤ 2) :
    Continuous (fun r : ℝ => (member r).toLp (raw r)) := by
  apply continuous_iff_seqContinuous.mpr
  intro sequence radius tends
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (raw ∘ sequence) (fun n => member (sequence n)) (raw radius) (member radius)).mpr
  have squareLimit : Filter.Tendsto (fun n : Nat => ∫ x : ℝ, ‖raw (sequence n) x-raw radius x‖^2 ∂μ) Filter.atTop (𝓝 (0:ℝ)) := by
    have limit := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (16:ℝ))
      (F := fun n x => ‖raw (sequence n) x-raw radius x‖^2) (f := fun _ => (0:ℝ))
      (fun n => by
        have meas := ((member (sequence n)).aestronglyMeasurable.sub (member radius).aestronglyMeasurable).norm
        convert! meas.mul meas using 1
        funext x
        simp [pow_two])
      (integrable_const 16) ?_ ?_
    · simpa using limit
    · intro n
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have b : ‖raw (sequence n) x-raw radius x‖≤4 := (norm_sub_le _ _).trans (by linarith [bound (sequence n) x,bound radius x])
      nlinarith [norm_nonneg (raw (sequence n) x-raw radius x)]
    · filter_upwards with x
      have actual := ((pointwise x).tendsto radius).comp tends
      simpa using (actual.sub (tendsto_const_nhds (x := raw radius x))).norm.pow 2
  have rootLimit := squareLimit.rpow_const (p := (2:ℝ)⁻¹) (Or.inr (by norm_num))
  have limit := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert! limit using 1
  · funext n
    simp only [Function.comp_apply]
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) ((member (sequence n)).sub (member radius))]
    simp
  · simp

theorem c_continuous : Continuous c :=
  profile_continuous cosineRaw burnolRadiusBoundaryCosineRaw_memLp
    (fun x => by unfold cosineRaw burnolRadiusBoundaryCosineRaw;fun_prop)
    burnolRadiusBoundaryCosineRaw_norm_le_two

theorem s_continuous : Continuous s :=
  profile_continuous sineRaw sine_memLp (fun x => by unfold sineRaw;fun_prop) sine_norm_le


theorem reaction_continuous (f : H) : Continuous (fun r : ℝ => rawReaction r f) := by
  change Continuous (fun r : ℝ => (r : ℂ) •
    (inner ℂ (c r) f • c r-inner ℂ (s r) f • s r))
  have hC : Continuous (fun r : ℝ => inner ℂ (c r) f • c r) :=
    (c_continuous.inner (𝕜 := ℂ) (continuous_const (y := f))).smul c_continuous
  have hS : Continuous (fun r : ℝ => inner ℂ (s r) f • s r) :=
    (s_continuous.inner (𝕜 := ℂ) (continuous_const (y := f))).smul s_continuous
  exact Complex.continuous_ofReal.smul (hC.sub hS)

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
