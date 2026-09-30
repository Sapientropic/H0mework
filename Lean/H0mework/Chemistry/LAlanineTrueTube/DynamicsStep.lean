import H0mework.Chemistry.LAlanineTrueTube.DynamicsClip

set_option autoImplicit false

namespace LAlanineTrueTube.Dynamics

open Set Metric ODE
open scoped NNReal
noncomputable section

theorem scalar_increment_bounds (h : ℝ) (hh : 0 ≤ h) (w velocity : ℝ → ℝ)
    (continuous : ContinuousOn w (Icc 0 h))
    (derivative : ∀ t ∈ Ioo 0 h, HasDerivAt w (velocity t) t)
    (lower upper : ℝ) (bounds : ∀ t ∈ Ioo 0 h, velocity t ∈ Icc lower upper)
    (t : ℝ) (inside : t ∈ Icc 0 h) :
    t * lower ≤ w t - w 0 ∧ w t - w 0 ≤ t * upper := by
  have hd : DifferentiableOn ℝ w (interior (Icc 0 h)) := by
    intro s hs
    rw [interior_Icc] at hs
    exact (derivative s hs).differentiableAt.differentiableWithinAt
  have hl := (convex_Icc (𝕜 := ℝ) 0 h).mul_sub_le_image_sub_of_le_deriv continuous hd
    (fun s hs => by rw [interior_Icc] at hs; rw [(derivative s hs).deriv]; exact (bounds s hs).1)
    0 ⟨le_rfl, hh⟩ t inside inside.1
  have hu := (convex_Icc (𝕜 := ℝ) 0 h).image_sub_le_mul_sub_of_deriv_le continuous hd
    (fun s hs => by rw [interior_Icc] at hs; rw [(derivative s hs).deriv]; exact (bounds s hs).2)
    0 ⟨le_rfl, hh⟩ t inside inside.1
  simpa only [sub_zero, mul_comm] using And.intro hl hu

/-- The velocity bounds are local source data. The outer Picard ball is a proof-side auxiliary. -/
theorem extension_picard (lower upper : Space) (ordered : lower ≤ upper)
    (f : Space → Space) (K : ℝ≥0) (lip : LipschitzOnWith K f (Icc lower upper))
    (gLower gUpper : Space) (bounds : ∀ x ∈ Icc lower upper, f x ∈ Icc gLower gUpper)
    (h : ℝ) (hh : 0 ≤ h) (initial : Space) :
    IsPicardLindelof (fun _ => extension lower upper f)
      (⟨0, le_rfl, hh⟩ : Icc 0 h) initial
      (fieldBound gLower gUpper * ⟨h, hh⟩ + 1) 0 (fieldBound gLower gUpper) K where
  lipschitzOnWith _ _ := (extension_lipschitz lower upper ordered f K lip).lipschitzOnWith
  continuousOn _ _ := continuous_const.continuousOn
  norm_le _ _ x _ := norm_le_fieldBound gLower gUpper _ (extension_bounds lower upper ordered f gLower gUpper bounds x)
  mul_max_le := by
    change (fieldBound gLower gUpper : ℝ) * max (h - 0) (0 - 0) ≤
      ((fieldBound gLower gUpper : ℝ) * h + 1) - 0
    simp only [sub_zero, sub_self, max_eq_left hh]
    linarith

/-- A rectangular Picard image generates an actual original-field path; no curve is an input. -/
theorem exists_step (lower upper initialLower initialUpper : Space) (ordered : lower ≤ upper)
    (f : Space → Space) (K : ℝ≥0) (lip : LipschitzOnWith K f (Icc lower upper))
    (gLower gUpper : Space) (bounds : ∀ x ∈ Icc lower upper, f x ∈ Icc gLower gUpper)
    (h : ℝ) (hh : 0 < h)
    (selfmap : ∀ t ∈ Icc 0 h, lower ≤ initialLower + t • gLower ∧
      initialUpper + t • gUpper ≤ upper)
    (initial : Space) (initial_mem : initial ∈ Icc initialLower initialUpper) :
    ∃ curve : ℝ → Space, curve 0 = initial ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt curve (f (curve t)) (Icc 0 h) t ∧
        curve t ∈ Icc lower upper) ∧
      (∀ t ∈ Icc 0 h, initial + t • gLower ≤ curve t ∧ curve t ≤ initial + t • gUpper) := by
  have picard := extension_picard lower upper ordered f K lip gLower gUpper bounds h hh.le initial
  obtain ⟨curve, starts, evolves⟩ := picard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hc : ContinuousOn curve (Icc 0 h) := HasDerivWithinAt.continuousOn evolves
  have increments (t : ℝ) (ht : t ∈ Icc 0 h) (i : Fin 3) :
      t * gLower i ≤ curve t i - initial i ∧ curve t i - initial i ≤ t * gUpper i := by
    have scalarDerivative (s : ℝ) (hs : s ∈ Ioo 0 h) :
        HasDerivAt (fun u => curve u i) (extension lower upper f (curve s) i) s := by
      exact ((ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt s
        ((evolves s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)))
    have hscalar : ContinuousOn (fun u => curve u i) (Icc 0 h) :=
      (continuous_apply i).comp_continuousOn hc
    simpa only [starts] using scalar_increment_bounds h hh.le _ _ hscalar scalarDerivative
      (gLower i) (gUpper i) (fun s _ =>
        ⟨(extension_bounds lower upper ordered f gLower gUpper bounds (curve s)).1 i,
         (extension_bounds lower upper ordered f gLower gUpper bounds (curve s)).2 i⟩) t ht
  have displacement (t : ℝ) (ht : t ∈ Icc 0 h) :
      initial + t • gLower ≤ curve t ∧ curve t ≤ initial + t • gUpper := by
    constructor <;> intro i <;> have hi := increments t ht i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> linarith
  have stays (t : ℝ) (ht : t ∈ Icc 0 h) : curve t ∈ Icc lower upper := by
    constructor
    · exact (selfmap t ht).1.trans ((add_le_add initial_mem.1 le_rfl).trans (displacement t ht).1)
    · exact (displacement t ht).2.trans ((add_le_add initial_mem.2 le_rfl).trans (selfmap t ht).2)
  refine ⟨curve, starts, ?_, displacement⟩
  intro t ht
  refine ⟨?_, stays t ht⟩
  simpa only [extension, clip_eq lower upper (curve t) (stays t ht)] using evolves t ht

end
end LAlanineTrueTube.Dynamics
