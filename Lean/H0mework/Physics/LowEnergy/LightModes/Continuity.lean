import H0mework.Physics.LowEnergy.LightModes.Native

/-! The source's unique roots form continuous branches throughout the
generated momentum interval, so the field and residue consumers share one
branch rather than pointwise unrelated choices. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Filter Topology Set
noncomputable section

theorem RootSource.distance_to_root (S : RootSource) (w r : ℝ) (small : |w|≤S.radius)
    (inside : r∈Icc (S.center-1/20) (S.center+1/20)) :
    |S.root w-r|≤2*|S.normalized w r| := by
  have differentiable : DifferentiableOn ℝ (S.normalized w) (interior (Icc (S.center-1/20) (S.center+1/20))) :=
    fun x _ => (S.normalized_derivative x w).differentiableAt.differentiableWithinAt
  have lower : ∀ x∈interior (Icc (S.center-1/20) (S.center+1/20)), (1/2 : ℝ)≤deriv (S.normalized w) x := by
    intro x hx
    rw [(S.normalized_derivative x w).deriv]
    have estimate := (S.error_bound x w (S.window_bound _ (interior_subset hx)) small).2
    linarith [(abs_le.mp estimate).1]
  have generated := (convex_Icc (S.center-1/20) (S.center+1/20)).mul_sub_le_image_sub_of_le_deriv
    (S.normalized_continuous w).continuousOn differentiable lower
  have root := S.root_spec w small
  by_cases ordered : S.root w≤r
  · have bound := generated (S.root w) root.1 r inside ordered
    rw [root.2,sub_zero] at bound
    rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    linarith [le_abs_self (S.normalized w r)]
  · have bound := generated r inside (S.root w) root.1 (le_of_not_ge ordered)
    rw [root.2,zero_sub] at bound
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge ordered))]
    linarith [neg_le_abs (S.normalized w r)]

theorem RootSource.root_continuousAt (S : RootSource) (w : ℝ) (small : |w|<S.radius) :
    ContinuousAt S.root w := by
  have near : ∀ᶠ x : ℝ in 𝓝 w, |x|<S.radius :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds small
  have valueContinuous : Continuous (fun x : ℝ => value S.terms (S.root w) x) :=
    (value_continuous S.terms).comp (continuous_const.prodMk continuous_id)
  have normalContinuous : Continuous (fun x : ℝ => S.normalized x (S.root w)) := by
    unfold normalized
    fun_prop
  have majorant : Tendsto (fun x : ℝ => 2*|S.normalized x (S.root w)|) (𝓝 w) (𝓝 0) := by
    have generated := (normalContinuous.abs.const_mul 2).tendsto w
    simpa only [(S.root_spec w small.le).2,abs_zero,mul_zero] using generated
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ majorant
  filter_upwards [near] with x hx
  simpa only [Real.norm_eq_abs] using S.distance_to_root x (S.root w) hx.le (S.root_in_window w)

theorem source_wave_continuousAt (branch : Branch) (q : ℝ) (small : |q| ≤ momentumRadius) :
    ContinuousAt (sourceWave branch) q := by
  have strictOne : momentumRadius<1 := by norm_num [momentumRadius]
  have square : |q^2|<(sourceRoot branch).radius := by
    rw [abs_pow]
    have r := source_radius branch
    have p := momentumRadius_positive
    nlinarith [abs_nonneg q]
  have qContinuous : ContinuousAt (fun x : ℝ => x^2) q := (continuous_pow 2).continuousAt
  have continuousRoot : ContinuousAt (fun x : ℝ => (sourceRoot branch).root (x^2)) q :=
    ContinuousAt.comp (f := fun x : ℝ => x^2) (x := q)
      ((sourceRoot branch).root_continuousAt (q^2) square) qContinuous
  unfold sourceWave
  split_ifs <;> fun_prop

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
