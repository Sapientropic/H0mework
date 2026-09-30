import H0mework.Physics.LowEnergy.LightModes.Polynomial

/-! A finite source polynomial produces a nonempty interval and its unique
root by the intermediate-value theorem and a generated positive derivative. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Set Filter Topology
noncomputable section

structure RootSource where
  center : ℝ
  terms : List Term
  center_bound : |center|≤7/4

def RootSource.radius (S : RootSource) : ℝ :=
  1/(40*(1+coefficientBound S.terms+coefficientBound (differentiate S.terms)))

def RootSource.normalized (S : RootSource) (w r : ℝ) : ℝ :=
  r-S.center+w*value S.terms r w

theorem RootSource.radius_positive (S : RootSource) : 0<S.radius := by
  unfold radius
  have := coefficientBound_nonnegative S.terms
  have := coefficientBound_nonnegative (differentiate S.terms)
  positivity

theorem RootSource.radius_bounds (S : RootSource) : S.radius≤1 ∧
    S.radius*coefficientBound S.terms≤1/40 ∧
    S.radius*coefficientBound (differentiate S.terms)≤1/40 := by
  have b := coefficientBound_nonnegative S.terms
  have d := coefficientBound_nonnegative (differentiate S.terms)
  have pos : 0<40*(1+coefficientBound S.terms+coefficientBound (differentiate S.terms)) := by positivity
  unfold radius
  constructor
  · apply (div_le_iff₀ pos).mpr
    linarith
  constructor
  all_goals rw [one_div,mul_comm,← div_eq_mul_inv]
  all_goals apply (div_le_iff₀ pos).mpr
  all_goals nlinarith

theorem RootSource.window_bound (S : RootSource) (r : ℝ)
    (inside : r∈Icc (S.center-1/20) (S.center+1/20)) : |r|≤2 := by
  obtain ⟨lower,upper⟩ := abs_le.mp S.center_bound
  apply abs_le.mpr
  constructor <;> linarith [inside.1,inside.2]

theorem RootSource.error_bound (S : RootSource) (r w : ℝ) (hr : |r|≤2) (hw : |w|≤S.radius) :
    |w*value S.terms r w|≤1/40 ∧ |w*value (differentiate S.terms) r w|≤1/40 := by
  have small : |w|≤1 := hw.trans S.radius_bounds.1
  have each (terms : List Term) : |w*value terms r w|≤S.radius*coefficientBound terms := by
    rw [abs_mul]
    exact mul_le_mul hw (value_bound terms r w hr small) (abs_nonneg _) (le_of_lt S.radius_positive)
  exact ⟨(each S.terms).trans S.radius_bounds.2.1,(each (differentiate S.terms)).trans S.radius_bounds.2.2⟩

theorem RootSource.normalized_derivative (S : RootSource) (r w : ℝ) :
    HasDerivAt (S.normalized w) (1+w*value (differentiate S.terms) r w) r := by
  exact ((hasDerivAt_id r).sub_const S.center).add ((value_derivative S.terms r w).const_mul w)

theorem RootSource.normalized_continuous (S : RootSource) (w : ℝ) : Continuous (S.normalized w) := by
  have continuousValue : Continuous (fun r : ℝ => value S.terms r w) :=
    (value_continuous S.terms).comp (continuous_id.prodMk continuous_const)
  unfold normalized
  fun_prop

theorem RootSource.strictMono (S : RootSource) (w : ℝ) (small : |w|≤S.radius) :
    StrictMonoOn (S.normalized w) (Icc (S.center-1/20) (S.center+1/20)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (S.normalized_continuous w).continuousOn
  intro r inside
  rw [(S.normalized_derivative r w).deriv]
  have bound := (S.error_bound r w (S.window_bound r (interior_subset inside)) small).2
  have lower := (abs_le.mp bound).1
  linarith

theorem RootSource.exists_unique (S : RootSource) (w : ℝ) (small : |w|≤S.radius) :
    ∃! r : ℝ, r∈Icc (S.center-1/20) (S.center+1/20) ∧ S.normalized w r=0 := by
  have ordered : S.center-1/20≤S.center+1/20 := by linarith
  have left := (S.error_bound (S.center-1/20) w (S.window_bound _ (left_mem_Icc.mpr ordered)) small).1
  have right := (S.error_bound (S.center+1/20) w (S.window_bound _ (right_mem_Icc.mpr ordered)) small).1
  have signs : S.normalized w (S.center-1/20)≤0 ∧ 0≤S.normalized w (S.center+1/20) := by
    unfold normalized
    constructor <;> linarith [(abs_le.mp left).1,(abs_le.mp left).2,(abs_le.mp right).1,(abs_le.mp right).2]
  obtain ⟨r,inside,zero⟩ := intermediate_value_Icc ordered (S.normalized_continuous w).continuousOn signs
  refine ⟨r,⟨inside,zero⟩,?_⟩
  intro y hy
  exact (S.strictMono w small).injOn hy.1 inside (hy.2.trans zero.symm)

def RootSource.root (S : RootSource) (w : ℝ) : ℝ :=
  if small : |w|≤S.radius then Classical.choose (ExistsUnique.exists (S.exists_unique w small)) else S.center

theorem RootSource.root_spec (S : RootSource) (w : ℝ) (small : |w|≤S.radius) :
    S.root w∈Icc (S.center-1/20) (S.center+1/20) ∧ S.normalized w (S.root w)=0 := by
  simp only [root,dif_pos small]
  exact Classical.choose_spec (ExistsUnique.exists (S.exists_unique w small))

theorem RootSource.root_in_window (S : RootSource) (w : ℝ) :
    S.root w∈Icc (S.center-1/20) (S.center+1/20) := by
  by_cases small : |w|≤S.radius
  · exact (S.root_spec w small).1
  · simp only [root,dif_neg small,mem_Icc]
    constructor <;> linarith

theorem RootSource.root_derivative_positive (S : RootSource) (w : ℝ) (small : |w|≤S.radius) :
    0<1+w*value (differentiate S.terms) (S.root w) w := by
  have bound := (S.error_bound (S.root w) w (S.window_bound _ (S.root_in_window w)) small).2
  have lower := (abs_le.mp bound).1
  linarith

theorem RootSource.root_unique (S : RootSource) (w r : ℝ) (small : |w|≤S.radius)
    (inside : r∈Icc (S.center-1/20) (S.center+1/20)) (zero : S.normalized w r=0) : r=S.root w := by
  exact (S.strictMono w small).injOn inside (S.root_spec w small).1 (zero.trans (S.root_spec w small).2.symm)

theorem RootSource.root_estimate (S : RootSource) (w : ℝ) :
    |S.root w-S.center|≤|w| *coefficientBound S.terms := by
  by_cases small : |w|≤S.radius
  · have generated := S.root_spec w small
    have equation : S.root w-S.center= -w*value S.terms (S.root w) w := by
      have equation := generated.2
      unfold normalized at equation
      linarith
    rw [equation,abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left
      (value_bound S.terms (S.root w) w (S.window_bound _ generated.1) (small.trans S.radius_bounds.1)) (abs_nonneg w)
  · simp only [root,dif_neg small,sub_self,abs_zero]
    exact mul_nonneg (abs_nonneg w) (coefficientBound_nonnegative S.terms)

theorem RootSource.root_limit (S : RootSource) : Tendsto S.root (𝓝 0) (𝓝 S.center) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _) (fun w => by simpa only [Real.norm_eq_abs] using S.root_estimate w)
  simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const (coefficientBound S.terms)

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
