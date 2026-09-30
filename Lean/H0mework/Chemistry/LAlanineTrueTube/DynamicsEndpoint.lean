import H0mework.Chemistry.LAlanineTrueTube.DynamicsStep

set_option autoImplicit false

namespace LAlanineTrueTube.Dynamics

open Set Metric
open scoped NNReal
noncomputable section

private theorem second_lower (h : ℝ) (hh : 0 ≤ h) (w velocity : ℝ → ℝ)
    (continuous : ContinuousOn w (Icc 0 h))
    (derivative : ∀ t ∈ Ioo 0 h, HasDerivAt w (velocity t) t)
    (a : ℝ) (firstBound : ∀ t ∈ Ioo 0 h, t * a ≤ velocity t - velocity 0) :
    w 0 + h * velocity 0 + h ^ 2 / 2 * a ≤ w h := by
  let corrected := fun t => w t - t * velocity 0 - t ^ 2 / 2 * a
  have hc : ContinuousOn corrected (Icc 0 h) :=
    (continuous.sub ((continuous_id.mul continuous_const).continuousOn)).sub
      (((continuous_id.pow 2).div_const 2).mul continuous_const).continuousOn
  have hd (t : ℝ) (ht : t ∈ Ioo 0 h) :
      HasDerivAt corrected (velocity t - velocity 0 - t * a) t := by
    convert! ((derivative t ht).sub ((hasDerivAt_id t).mul_const (velocity 0))).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const a) using 1
    simp only [id_eq]
    ring
  have hm : MonotoneOn corrected (Icc 0 h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h) hc
      (f' := fun t => velocity t - velocity 0 - t * a)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      linarith [firstBound t ht]
  have bound := hm (show 0 ∈ Icc 0 h from ⟨le_rfl, hh⟩) (show h ∈ Icc 0 h from ⟨hh, le_rfl⟩) hh
  dsimp [corrected] at bound
  nlinarith

theorem scalar_second_order_bounds (h : ℝ) (hh : 0 ≤ h) (w velocity acceleration : ℝ → ℝ)
    (continuous : ContinuousOn w (Icc 0 h)) (velocityContinuous : ContinuousOn velocity (Icc 0 h))
    (derivative : ∀ t ∈ Ioo 0 h, HasDerivAt w (velocity t) t)
    (second : ∀ t ∈ Ioo 0 h, HasDerivAt velocity (acceleration t) t)
    (aLower aUpper : ℝ) (bounds : ∀ t ∈ Ioo 0 h, acceleration t ∈ Icc aLower aUpper) :
    w 0 + h * velocity 0 + h ^ 2 / 2 * aLower ≤ w h ∧
      w h ≤ w 0 + h * velocity 0 + h ^ 2 / 2 * aUpper := by
  have first (t : ℝ) (ht : t ∈ Ioo 0 h) :=
    scalar_increment_bounds h hh velocity acceleration velocityContinuous second aLower aUpper bounds
      t (Ioo_subset_Icc_self ht)
  constructor
  · exact second_lower h hh w velocity continuous derivative aLower (fun t ht => (first t ht).1)
  · have bound := second_lower h hh (fun t => -w t) (fun t => -velocity t)
      continuous.neg (fun t ht => (derivative t ht).neg) (-aUpper) (fun t ht => by
        have hi := (first t ht).2
        nlinarith)
    nlinarith

/-- The same generated path pays first-order and second-order endpoint bounds simultaneously. -/
theorem exists_step_secondOrder (lower upper initialLower initialUpper : Space) (ordered : lower ≤ upper)
    (f : Space → Space) (K : ℝ≥0) (lip : LipschitzOnWith K f (Icc lower upper))
    (gLower gUpper : Space) (bounds : ∀ x ∈ Icc lower upper, f x ∈ Icc gLower gUpper)
    (h : ℝ) (hh : 0 < h)
    (selfmap : ∀ t ∈ Icc 0 h, lower ≤ initialLower + t • gLower ∧
      initialUpper + t • gUpper ≤ upper)
    (A : Space → Space →L[ℝ] Space)
    (derivative : ∀ x ∈ Icc lower upper, HasFDerivAt f (A x) x)
    (aLower aUpper : Space)
    (acceleration : ∀ x ∈ Icc lower upper, A x (f x) ∈ Icc aLower aUpper)
    (initial : Space) (initial_mem : initial ∈ Icc initialLower initialUpper) :
    ∃ curve : ℝ → Space, curve 0 = initial ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt curve (f (curve t)) (Icc 0 h) t ∧
        curve t ∈ Icc lower upper) ∧
      (initial + h • gLower ≤ curve h ∧ curve h ≤ initial + h • gUpper) ∧
      (initial + h • f initial + (h ^ 2 / 2) • aLower ≤ curve h ∧
        curve h ≤ initial + h • f initial + (h ^ 2 / 2) • aUpper) := by
  obtain ⟨curve, starts, evolves, displacement⟩ :=
    exists_step lower upper initialLower initialUpper ordered f K lip gLower gUpper bounds h hh selfmap initial initial_mem
  have hc : ContinuousOn curve (Icc 0 h) :=
    HasDerivWithinAt.continuousOn (fun t ht => (evolves t ht).1)
  have velocityWithin (t : ℝ) (ht : t ∈ Icc 0 h) :
      HasDerivWithinAt (fun s => f (curve s)) (A (curve t) (f (curve t))) (Icc 0 h) t :=
    (derivative (curve t) (evolves t ht).2).comp_hasDerivWithinAt t (evolves t ht).1
  have hvc : ContinuousOn (fun t => f (curve t)) (Icc 0 h) :=
    HasDerivWithinAt.continuousOn velocityWithin
  have secondBound (i : Fin 3) :
      initial i + h * f initial i + h ^ 2 / 2 * aLower i ≤ curve h i ∧
        curve h i ≤ initial i + h * f initial i + h ^ 2 / 2 * aUpper i := by
    have first (t : ℝ) (ht : t ∈ Ioo 0 h) :
        HasDerivAt (fun s => curve s i) (f (curve t) i) t := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
          ((evolves t (Ioo_subset_Icc_self ht)).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    have second (t : ℝ) (ht : t ∈ Ioo 0 h) :
        HasDerivAt (fun s => f (curve s) i) (A (curve t) (f (curve t)) i) t := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
          ((velocityWithin t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    simpa only [Function.comp_apply, starts] using scalar_second_order_bounds h hh.le _ _ _
      ((continuous_apply i).comp_continuousOn hc) ((continuous_apply i).comp_continuousOn hvc)
      first second (aLower i) (aUpper i) (fun t ht =>
        ⟨(acceleration (curve t) (evolves t (Ioo_subset_Icc_self ht)).2).1 i,
         (acceleration (curve t) (evolves t (Ioo_subset_Icc_self ht)).2).2 i⟩)
  refine ⟨curve, starts, evolves, displacement h ⟨hh.le, le_rfl⟩, ?_⟩
  constructor
  · intro i
    exact (secondBound i).1
  · intro i
    exact (secondBound i).2

end
end LAlanineTrueTube.Dynamics
