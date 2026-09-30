import H0mework.Physics.LowEnergy.Quantum.FiniteCoreEvolution
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! One cofinal ultrafilter for the entire original-core compression net. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.WeakCoreEvolution
open SymmetricGraphClosure FiniteCoreEvolution Filter
open scoped InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def sourceFilter (T : E →ₗ.[ℂ] E) : Ultrafilter (Finset T.domain) := Ultrafilter.of atTop

omit [CompleteSpace E] in
theorem sourceFilter_cofinal (T : E →ₗ.[ℂ] E) : (sourceFilter T : Filter (Finset T.domain)) ≤ atTop :=
  Ultrafilter.of_le atTop

theorem pairing_bound (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y : E) (F : Finset T.domain) :
    ‖inner ℂ (evolution T F t x) y‖ ≤ ‖x‖ * ‖y‖ := by
  simpa only [evolution_norm T symmetric F] using
    norm_inner_le_norm (𝕜 := ℂ) (evolution T F t x) y

def coefficient (T : E →ₗ.[ℂ] E) (t : ℝ) (x y : E) : ℂ :=
  limUnder (sourceFilter T) (fun F => inner ℂ (evolution T F t x) y)

theorem coefficient_tendsto (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y : E) :
    Tendsto (fun F => inner ℂ (evolution T F t x) y) (sourceFilter T)
      (𝓝 (coefficient T t x y)) := by
  apply tendsto_nhds_limUnder
  let f := fun F => inner ℂ (evolution T F t x) y
  have hb : Metric.closedBall (0 : ℂ) (‖x‖*‖y‖) ∈ (sourceFilter T).map f := by
    change ∀ᶠ F in (sourceFilter T : Filter (Finset T.domain)),
      f F ∈ Metric.closedBall (0 : ℂ) (‖x‖*‖y‖)
    apply Filter.Eventually.of_forall
    intro F
    simpa only [Metric.mem_closedBall, dist_zero_right] using pairing_bound T symmetric t x y F
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) (‖x‖*‖y‖)).ultrafilter_le_nhds'
    ((sourceFilter T).map f) hb
  exact ⟨z, hz⟩

theorem coefficient_bound (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y : E) : ‖coefficient T t x y‖ ≤ ‖x‖*‖y‖ :=
  le_of_tendsto (coefficient_tendsto T symmetric t x y).norm
    (Filter.Eventually.of_forall (pairing_bound T symmetric t x y))

theorem coefficient_add_right (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y z : E) : coefficient T t x (y+z) = coefficient T t x y + coefficient T t x z := by
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric t x (y+z))
  simpa only [inner_add_right] using
    (coefficient_tendsto T symmetric t x y).add (coefficient_tendsto T symmetric t x z)

theorem coefficient_smul_right (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (c : ℂ) (x y : E) : coefficient T t x (c • y) = c * coefficient T t x y := by
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric t x (c • y))
  simpa only [inner_smul_right] using
    tendsto_const_nhds.mul (coefficient_tendsto T symmetric t x y)

theorem coefficient_add_left (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y z : E) : coefficient T t (x+y) z = coefficient T t x z + coefficient T t y z := by
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric t (x+y) z)
  simpa only [map_add, inner_add_left] using
    (coefficient_tendsto T symmetric t x z).add (coefficient_tendsto T symmetric t y z)

theorem coefficient_smul_left (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (c : ℂ) (x y : E) :
    coefficient T t (c • x) y = (starRingEnd ℂ c) * coefficient T t x y := by
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric t (c • x) y)
  simpa only [map_smul, inner_smul_left] using
    tendsto_const_nhds.mul (coefficient_tendsto T symmetric t x y)

def limitFunctional (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x : E) : E →L[ℂ] ℂ :=
  ({ toFun := coefficient T t x
     map_add' := coefficient_add_right T symmetric t x
     map_smul' := fun c y => coefficient_smul_right T symmetric t c x y } : E →ₗ[ℂ] ℂ).mkContinuous
    ‖x‖ (coefficient_bound T symmetric t x)

def rawEvolution (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T) (t : ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℂ E).symm (limitFunctional T symmetric t x)

theorem raw_evolution_pair (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y : E) : inner ℂ (rawEvolution T symmetric t x) y = coefficient T t x y :=
  InnerProductSpace.toDual_symm_apply

theorem raw_evolution_bound (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x : E) : ‖rawEvolution T symmetric t x‖ ≤ ‖x‖ := by
  rw [rawEvolution, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) (coefficient_bound T symmetric t x)

def weakEvolution (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T) (t : ℝ) : E →L[ℂ] E :=
  (show E →ₗ[ℂ] E from {
    toFun := rawEvolution T symmetric t
    map_add' := by
      intro x y
      apply ext_inner_right ℂ
      intro z
      rw [inner_add_left, raw_evolution_pair, raw_evolution_pair, raw_evolution_pair]
      exact coefficient_add_left T symmetric t x y z
    map_smul' := by
      intro c x
      apply ext_inner_right ℂ
      intro y
      rw [inner_smul_left, raw_evolution_pair, raw_evolution_pair]
      exact coefficient_smul_left T symmetric t c x y }).mkContinuous 1
    (fun x => by
      change ‖rawEvolution T symmetric t x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using raw_evolution_bound T symmetric t x)

theorem weak_evolution_pair (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x y : E) : inner ℂ (weakEvolution T symmetric t x) y = coefficient T t x y :=
  raw_evolution_pair T symmetric t x y

theorem weak_evolution_contraction (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (x : E) : ‖weakEvolution T symmetric t x‖ ≤ ‖x‖ :=
  raw_evolution_bound T symmetric t x

theorem weak_evolution_zero (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T) :
    weakEvolution T symmetric 0 = 1 := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [weak_evolution_pair]
  change coefficient T 0 x y = inner ℂ x y
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric 0 x y)
  simpa only [evolution, zero_smul, NormedSpace.exp_zero, one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset T.domain => inner ℂ x y)
      (sourceFilter T) (𝓝 (inner ℂ x y)))

theorem coefficient_core_difference (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : T.domain) (y : E) (s t : ℝ) :
    ‖coefficient T t (x : E) y-coefficient T s (x : E) y‖ ≤ ‖T x‖ * ‖t-s‖ * ‖y‖ := by
  classical
  apply le_of_tendsto ((coefficient_tendsto T symmetric t (x : E) y).sub
    (coefficient_tendsto T symmetric s (x : E) y)).norm
  apply sourceFilter_cofinal T
  refine Filter.eventually_atTop.mpr ⟨{x}, fun F hF => ?_⟩
  rw [← inner_sub_left]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ y).trans
    (mul_le_mul_of_nonneg_right (evolution_core_uniform T symmetric F x
      (mem_coreSpan T F x (hF (Finset.mem_singleton_self x))) s t) (norm_nonneg y))

theorem weak_evolution_core_uniform (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : T.domain) (s t : ℝ) :
    ‖weakEvolution T symmetric t (x : E)-weakEvolution T symmetric s (x : E)‖ ≤ ‖T x‖ * ‖t-s‖ := by
  let d := weakEvolution T symmetric t (x : E)-weakEvolution T symmetric s (x : E)
  have h : ‖inner ℂ d d‖ ≤ ‖T x‖ * ‖t-s‖ * ‖d‖ := by
    simpa only [d, inner_sub_left, weak_evolution_pair] using
      coefficient_core_difference T symmetric x d s t
  have hs : ‖d‖ ^ 2 ≤ ‖T x‖ * ‖t-s‖ * ‖d‖ := by
    simpa [inner_self_eq_norm_sq_to_K, norm_pow] using h
  change ‖d‖ ≤ ‖T x‖ * ‖t-s‖
  nlinarith [norm_nonneg d, mul_nonneg (norm_nonneg (T x)) (norm_nonneg (t-s))]

theorem weak_evolution_difference_bound (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : E) (v : T.domain) (s t : ℝ) :
    ‖weakEvolution T symmetric t x-weakEvolution T symmetric s x‖ ≤
      2*‖x-(v : E)‖ + ‖T v‖*‖t-s‖ := by
  let U := weakEvolution T symmetric
  have identity : U t x-U s x = (U t (x-(v : E))+(U t v-U s v))+ -(U s (x-(v : E))) := by
    simp only [map_sub]
    abel
  rw [identity]
  have h := (norm_add_le (U t (x-(v : E))+(U t v-U s v)) (-(U s (x-(v : E))))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_neg] at h
  have hleft := weak_evolution_contraction T symmetric t (x-(v : E))
  have hright := weak_evolution_contraction T symmetric s (x-(v : E))
  have hcore := weak_evolution_core_uniform T symmetric v s t
  dsimp only [U] at h
  linarith

theorem weak_evolution_continuous (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (dense : Dense (T.domain : Set E)) (x : E) : Continuous (fun t => weakEvolution T symmetric t x) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  obtain ⟨v, hv, near⟩ := Metric.mem_closure_iff.mp (dense x) (epsilon/4) (by positivity)
  let w : T.domain := ⟨v, hv⟩
  have constant_pos : 0 < ‖T w‖+1 := by positivity
  refine ⟨(epsilon/2)/(‖T w‖+1), by positivity, ?_⟩
  intro t ht
  have hs : ‖t-s‖*(‖T w‖+1) < epsilon/2 :=
    (lt_div_iff₀ constant_pos).mp (by simpa only [dist_eq_norm] using ht)
  have hx : ‖x-(w : E)‖ < epsilon/4 := by simpa only [dist_eq_norm] using near
  have hb := weak_evolution_difference_bound T symmetric x w s t
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (t-s)]

theorem weak_evolution_core_remainder (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : T.domain) (hTx : T x ∈ T.domain) (t h : ℝ) :
    ‖weakEvolution T symmetric (t+h) (x : E)-weakEvolution T symmetric t (x : E) -
      h • ((-Complex.I) • weakEvolution T symmetric t (T x))‖ ≤ ‖T ⟨T x, hTx⟩‖ * ‖h‖^2 := by
  classical
  let d := weakEvolution T symmetric (t+h) (x : E)-weakEvolution T symmetric t (x : E) -
      h • ((-Complex.I) • weakEvolution T symmetric t (T x))
  have bound (y : E) : ‖inner ℂ d y‖ ≤ (‖T ⟨T x, hTx⟩‖ * ‖h‖^2)*‖y‖ := by
    have convergence : Tendsto (fun F => inner ℂ
        (evolution T F (t+h) (x : E)-evolution T F t (x : E)-
          h • ((-Complex.I) • evolution T F t (T x))) y)
        (sourceFilter T) (𝓝 (inner ℂ d y)) := by
      simp only [d, inner_sub_left, inner_smul_left_eq_star_smul, weak_evolution_pair]
      exact ((coefficient_tendsto T symmetric (t+h) (x : E) y).sub
        (coefficient_tendsto T symmetric t (x : E) y)).sub
          (((coefficient_tendsto T symmetric t (T x) y).const_smul (star (-Complex.I))).const_smul (star h))
    apply le_of_tendsto convergence.norm
    apply sourceFilter_cofinal T
    refine Filter.eventually_atTop.mpr ⟨{x, ⟨T x, hTx⟩}, fun F hF => ?_⟩
    exact (norm_inner_le_norm (𝕜 := ℂ) _ y).trans
      (mul_le_mul_of_nonneg_right (evolution_core_remainder T symmetric x hTx F
        (hF (by simp)) (hF (by simp)) t h) (norm_nonneg y))
  have hb := bound d
  have hs : ‖d‖ ^ 2 ≤ (‖T ⟨T x, hTx⟩‖ * ‖h‖^2)*‖d‖ := by
    simpa [inner_self_eq_norm_sq_to_K, norm_pow] using hb
  change ‖d‖ ≤ ‖T ⟨T x, hTx⟩‖ * ‖h‖^2
  nlinarith [norm_nonneg d, mul_nonneg (norm_nonneg (T ⟨T x, hTx⟩)) (sq_nonneg ‖h‖)]

theorem weak_evolution_core_derivative (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : T.domain) (hTx : T x ∈ T.domain) (t : ℝ) :
    HasDerivAt (fun u => weakEvolution T symmetric u (x : E))
      ((-Complex.I) • weakEvolution T symmetric t (T x)) t := by
  rw [hasDerivAt_iff_tendsto]
  have hlim : Tendsto (fun u : ℝ => ‖T ⟨T x, hTx⟩‖ * ‖u-t‖) (𝓝 t) (𝓝 0) := by
    have hd : Tendsto (fun u : ℝ => u-t) (𝓝 t) (𝓝 (t-t)) :=
      (tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 t) (𝓝 t)).sub tendsto_const_nhds
    simpa only [sub_self, norm_zero, mul_zero] using
      hd.norm.const_mul ‖T ⟨T x, hTx⟩‖
  apply squeeze_zero (fun u => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun u => ?_) hlim
  have hb := weak_evolution_core_remainder T symmetric x hTx t (u-t)
  have hc := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg (u-t)))
  have identity : t+(u-t) = u := by ring
  rw [identity] at hc
  have scalar : ‖u-t‖⁻¹ * (‖T ⟨T x, hTx⟩‖ * ‖u-t‖^2) = ‖T ⟨T x, hTx⟩‖ * ‖u-t‖ := by
    by_cases hz : ‖u-t‖ = 0
    · simp [hz]
    · field_simp
  exact hc.trans_eq scalar

theorem weak_evolution_original_pairing (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x y : T.domain) (hTx : T x ∈ T.domain) (hTy : T y ∈ T.domain) (t : ℝ) :
    inner ℂ (weakEvolution T symmetric t (x : E)) (T y) =
      inner ℂ (weakEvolution T symmetric t (T x)) (y : E) := by
  classical
  rw [weak_evolution_pair, weak_evolution_pair]
  apply tendsto_nhds_unique (coefficient_tendsto T symmetric t (x : E) (T y))
  apply (coefficient_tendsto T symmetric t (T x) (y : E)).congr'
  apply sourceFilter_cofinal T
  refine Filter.eventually_atTop.mpr ⟨{x, ⟨T x, hTx⟩, y, ⟨T y, hTy⟩}, fun F hF => ?_⟩
  have hx := compression_core_exact T F x hTx (hF (by simp)) (hF (by simp))
  have hy := compression_core_exact T F y hTy (hF (by simp)) (hF (by simp))
  have hc := congrArg (fun A : E →L[ℂ] E => A (x : E)) (evolution_commute T F t)
  change evolution T F t (compression T F (x : E)) =
    compression T F (evolution T F t (x : E)) at hc
  calc
    inner ℂ (evolution T F t (T x)) (y : E) =
        inner ℂ (evolution T F t (compression T F (x : E))) (y : E) := by rw [hx]
    _ = inner ℂ (compression T F (evolution T F t (x : E))) (y : E) := by rw [hc]
    _ = inner ℂ (evolution T F t (x : E)) (compression T F (y : E)) :=
      compression_symmetric T symmetric F _ _
    _ = inner ℂ (evolution T F t (x : E)) (T y) := by rw [hy]

theorem weak_evolution_pair_derivative (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x y : T.domain) (hTx : T x ∈ T.domain) (hTy : T y ∈ T.domain) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (weakEvolution T symmetric u (x : E)) (y : E))
      (Complex.I * inner ℂ (weakEvolution T symmetric t (x : E)) (T y)) t := by
  have h := (weak_evolution_core_derivative T symmetric x hTx t).inner ℂ
    (hasDerivAt_const t (y : E))
  simpa [inner_smul_left, ← weak_evolution_original_pairing T symmetric x y hTx hTy t] using h

theorem retarded_test_identity (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (dense : Dense (T.domain : Set E)) (x y : T.domain)
    (hTx : T x ∈ T.domain) (hTy : T y ∈ T.domain)
    (eta eta' : ℝ → ℂ) (differentiable : ∀ t, HasDerivAt eta (eta' t) t)
    (derivative_continuous : Continuous eta') (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * inner ℂ (weakEvolution T symmetric t (x : E)) (y : E) +
      eta t * (Complex.I * inner ℂ (weakEvolution T symmetric t (x : E)) (T y))) =
      -eta 0 * inner ℂ (x : E) (y : E) := by
  let c := fun t => inner ℂ (weakEvolution T symmetric t (x : E)) (y : E)
  let k := fun t => inner ℂ (weakEvolution T symmetric t (x : E)) (T y)
  have hc : Continuous c := (weak_evolution_continuous T symmetric dense (x : E)).inner continuous_const
  have hk : Continuous k := (weak_evolution_continuous T symmetric dense (x : E)).inner continuous_const
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*(Complex.I*k t)) t :=
    (differentiable t).mul (weak_evolution_pair_derivative T symmetric x y hTx hTy t)
  have integrable := ((derivative_continuous.mul hc).add
    (he.mul ((continuous_const : Continuous (fun _ : ℝ => Complex.I)).mul hk))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, weak_evolution_zero, one_apply_eq_self, zero_sub,
    neg_mul] using identity

#print axioms coefficient_tendsto
#print axioms coefficient_bound
#print axioms coefficient_add_right
#print axioms weak_evolution_pair
#print axioms weak_evolution_contraction
#print axioms weak_evolution_zero
#print axioms weak_evolution_core_uniform
#print axioms weak_evolution_continuous
#print axioms weak_evolution_core_remainder
#print axioms weak_evolution_core_derivative
#print axioms weak_evolution_original_pairing
#print axioms weak_evolution_pair_derivative
#print axioms retarded_test_identity
end LowEnergy.WeakCoreEvolution
