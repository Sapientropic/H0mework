import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace LocalHistoryDerivative
open Set Filter MeasureTheory
open scoped Topology Interval

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

theorem duhamel_left {A U W : ℝ → B} {A0 b : B} {t : ℝ}
    (hA : ContinuousOn A (uIcc 0 t))
    (hU : ∀ s ∈ uIcc 0 t, HasDerivAt U (A s * U s) s)
    (hW : ∀ s ∈ uIcc 0 t, HasDerivAt W (-(W s * A0)) s)
    (hU0 : U 0 = 1) (hW0 : W 0 = 1) (hInv : b * W t = 1) :
    U t - b = b * ∫ s in 0..t, W s * (A s - A0) * U s := by
  have hP (s : ℝ) (hs : s ∈ uIcc 0 t) :
      HasDerivAt (fun s => W s * U s) (W s * (A s - A0) * U s) s := by
    convert (hW s hs).mul (hU s hs) using 1 <;> first | rfl | noncomm_ring
  have hcont : ContinuousOn (fun s => W s * (A s - A0) * U s) (uIcc 0 t) :=
    ((HasDerivAt.continuousOn hW).mul (hA.sub continuousOn_const)).mul
      (HasDerivAt.continuousOn hU)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hP hcont.intervalIntegrable
  rw [hFTC, hW0, hU0, one_mul, mul_sub, ← mul_assoc, hInv, one_mul, mul_one]

omit [CompleteSpace B] in
theorem tendsto_intervalIntegral_of_norm_bound
    {F : ℝ → ℝ → B} {f : ℝ → B} {t : ℝ} {l : Filter ℝ} [l.IsCountablyGenerated]
    (hcont : ∀ᶠ a in l, ContinuousOn (F a) (uIcc 0 t))
    (hbound : ∃ C : ℝ, ∀ᶠ a in l, ∀ s ∈ uIcc 0 t, ‖F a s‖ ≤ C)
    (hlim : ∀ s ∈ uIcc 0 t, Tendsto (fun a => F a s) l (𝓝 (f s))) :
    Tendsto (fun a => ∫ s in 0..t, F a s) l (𝓝 (∫ s in 0..t, f s)) := by
  have hmeas : ∀ᶠ a in l, AEStronglyMeasurable (F a) (volume.restrict (uIoc 0 t)) := by
    filter_upwards [hcont] with a ha
    exact (intervalIntegrable_iff.mp ha.intervalIntegrable).aestronglyMeasurable
  have hbound' : ∃ C : ℝ, ∀ᶠ a in l, ∀ᵐ s ∂volume.restrict (uIoc 0 t), ‖F a s‖ ≤ C := by
    obtain ⟨C, hC⟩ := hbound
    refine ⟨C, hC.mono fun a ha => ?_⟩
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact Eventually.of_forall fun s hs => ha s (uIoc_subset_uIcc hs)
  have hlim' : ∀ᵐ s ∂volume.restrict (uIoc 0 t), Tendsto (fun a => F a s) l (𝓝 (f s)) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact Eventually.of_forall fun s hs => hlim s (uIoc_subset_uIcc hs)
  have : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    simpa [uIoc] using (inferInstance :
      IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t))))
  have limit := MeasureTheory.tendsto_integral_filter_of_norm_le_const hmeas hbound' hlim'
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  exact limit.const_smul _

theorem secant_duhamel_left {A U W : ℝ → B} {A0 b : B} {t a : ℝ}
    (hA : ContinuousOn A (uIcc 0 t))
    (hU : ∀ s ∈ uIcc 0 t, HasDerivAt U (A s * U s) s)
    (hW : ∀ s ∈ uIcc 0 t, HasDerivAt W (-(W s * A0)) s)
    (hU0 : U 0 = 1) (hW0 : W 0 = 1) (hInv : b * W t = 1) :
    a⁻¹ • (U t - b) = b * ∫ s in 0..t, W s * (a⁻¹ • (A s - A0)) * U s := by
  rw [duhamel_left hA hU hW hU0 hW0 hInv]
  simp_rw [mul_smul_comm, smul_mul_assoc]
  rw [intervalIntegral.integral_smul, mul_smul_comm]

theorem parameter_hasDerivAt_left
    {A U : ℝ → ℝ → B} {W D : ℝ → B} {A0 : B} {t : ℝ}
    (hA : ∀ᶠ a in 𝓝 (0 : ℝ), ContinuousOn (A a) (uIcc 0 t))
    (hU : ∀ᶠ a in 𝓝 (0 : ℝ),
      ∀ s ∈ uIcc 0 t, HasDerivAt (U a) (A a s * U a s) s)
    (hW : ∀ s ∈ uIcc 0 t, HasDerivAt W (-(W s * A0)) s)
    (hU0 : ∀ᶠ a in 𝓝 (0 : ℝ), U a 0 = 1)
    (hW0 : W 0 = 1) (hInv : U 0 t * W t = 1)
    (hUlim : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => U a s) (𝓝 (0 : ℝ)) (𝓝 (U 0 s)))
    (hsec : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => a⁻¹ • (A a s - A0)) (𝓝[≠] (0 : ℝ)) (𝓝 (D s)))
    (hmajorant : ∃ C : ℝ, ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s ∈ uIcc 0 t,
      ‖W s * (a⁻¹ • (A a s - A0)) * U a s‖ ≤ C) :
    HasDerivAt (fun a => U a t) (U 0 t * ∫ s in 0..t, W s * D s * U 0 s) 0 := by
  have hA := hA.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hU := hU.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hU0 := hU0.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hmajorant := hmajorant.imp (fun C hC => hC.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds))
  have hUlim (s : ℝ) (hs : s ∈ uIcc 0 t) :=
    (hUlim s hs).mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  let Q (a s : ℝ) := W s * (a⁻¹ • (A a s - A0)) * U a s
  have hcont : ∀ᶠ a in 𝓝[≠] (0 : ℝ), ContinuousOn (Q a) (uIcc 0 t) := by
    filter_upwards [hA, hU] with a ha hu
    exact ((HasDerivAt.continuousOn hW).mul
      ((ha.sub continuousOn_const).const_smul a⁻¹)).mul (HasDerivAt.continuousOn hu)
  have hlim : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => Q a s) (𝓝[≠] (0 : ℝ)) (𝓝 (W s * D s * U 0 s)) := by
    intro s hs
    exact (tendsto_const_nhds.mul (hsec s hs)).mul (hUlim s hs)
  have hint := tendsto_intervalIntegral_of_norm_bound hcont hmajorant hlim
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => U 0 t)
    (𝓝[≠] (0 : ℝ)) (𝓝 (U 0 t))).mul hint
  have hEq : (fun a => a⁻¹ • (U a t - U 0 t)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun a => U 0 t * ∫ s in 0..t, Q a s) := by
    filter_upwards [hA, hU, hU0] with a ha hu hzero
    exact secant_duhamel_left ha hu hW hzero hW0 hInv
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add] using hscaled.congr' hEq.symm

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem product_majorant {W Q U : ℝ → ℝ → B} {t : ℝ} {l : Filter ℝ}
    {L M N : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (_hN : 0 ≤ N)
    (hW : ∀ᶠ a in l, ∀ s ∈ uIcc 0 t, ‖W a s‖ ≤ L)
    (hQ : ∀ᶠ a in l, ∀ s ∈ uIcc 0 t, ‖Q a s‖ ≤ M)
    (hU : ∀ᶠ a in l, ∀ s ∈ uIcc 0 t, ‖U a s‖ ≤ N) :
    ∃ C : ℝ, ∀ᶠ a in l, ∀ s ∈ uIcc 0 t, ‖W a s * Q a s * U a s‖ ≤ C := by
  refine ⟨L * M * N, ?_⟩
  filter_upwards [hW, hQ, hU] with a hw hq hu
  intro s hs
  calc
    ‖W a s * Q a s * U a s‖ ≤ ‖W a s * Q a s‖ * ‖U a s‖ := norm_mul_le _ _
    _ ≤ (‖W a s‖ * ‖Q a s‖) * ‖U a s‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ L * M * N := by gcongr <;> first | exact hw s hs | exact hq s hs | exact hu s hs

theorem duhamel_right {A V X : ℝ → B} {A0 b : B} {t : ℝ}
    (hA : ContinuousOn A (uIcc 0 t))
    (hV : ∀ s ∈ uIcc 0 t, HasDerivAt V (-(V s * A s)) s)
    (hX : ∀ s ∈ uIcc 0 t, HasDerivAt X (A0 * X s) s)
    (hV0 : V 0 = 1) (hX0 : X 0 = 1) (hInv : X t * b = 1) :
    V t - b = -(∫ s in 0..t, V s * (A s - A0) * X s) * b := by
  have hP (s : ℝ) (hs : s ∈ uIcc 0 t) :
      HasDerivAt (fun s => V s * X s) (-(V s * (A s - A0) * X s)) s := by
    convert (hV s hs).mul (hX s hs) using 1 <;> first | rfl | noncomm_ring
  have hcont : ContinuousOn (fun s => -(V s * (A s - A0) * X s)) (uIcc 0 t) :=
    (((HasDerivAt.continuousOn hV).mul (hA.sub continuousOn_const)).mul
      (HasDerivAt.continuousOn hX)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hP hcont.intervalIntegrable
  rw [← intervalIntegral.integral_neg, hFTC, hV0, hX0, one_mul,
    sub_mul, mul_assoc, hInv, mul_one, one_mul]

theorem secant_duhamel_right {A V X : ℝ → B} {A0 b : B} {t a : ℝ}
    (hA : ContinuousOn A (uIcc 0 t))
    (hV : ∀ s ∈ uIcc 0 t, HasDerivAt V (-(V s * A s)) s)
    (hX : ∀ s ∈ uIcc 0 t, HasDerivAt X (A0 * X s) s)
    (hV0 : V 0 = 1) (hX0 : X 0 = 1) (hInv : X t * b = 1) :
    a⁻¹ • (V t - b) = -(∫ s in 0..t, V s * (a⁻¹ • (A s - A0)) * X s) * b := by
  rw [duhamel_right hA hV hX hV0 hX0 hInv]
  simp_rw [mul_smul_comm, smul_mul_assoc]
  rw [intervalIntegral.integral_smul]
  simp only [neg_mul, smul_neg, smul_mul_assoc]

theorem parameter_hasDerivAt_right
    {A V : ℝ → ℝ → B} {X D : ℝ → B} {A0 : B} {t : ℝ}
    (hA : ∀ᶠ a in 𝓝 (0 : ℝ), ContinuousOn (A a) (uIcc 0 t))
    (hV : ∀ᶠ a in 𝓝 (0 : ℝ),
      ∀ s ∈ uIcc 0 t, HasDerivAt (V a) (-(V a s * A a s)) s)
    (hX : ∀ s ∈ uIcc 0 t, HasDerivAt X (A0 * X s) s)
    (hV0 : ∀ᶠ a in 𝓝 (0 : ℝ), V a 0 = 1)
    (hX0 : X 0 = 1) (hInv : X t * V 0 t = 1)
    (hVlim : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => V a s) (𝓝 (0 : ℝ)) (𝓝 (V 0 s)))
    (hsec : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => a⁻¹ • (A a s - A0)) (𝓝[≠] (0 : ℝ)) (𝓝 (D s)))
    (hmajorant : ∃ C : ℝ, ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s ∈ uIcc 0 t,
      ‖V a s * (a⁻¹ • (A a s - A0)) * X s‖ ≤ C) :
    HasDerivAt (fun a => V a t) (-(∫ s in 0..t, V 0 s * D s * X s) * V 0 t) 0 := by
  have hA := hA.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hV := hV.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hV0 := hV0.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hmajorant := hmajorant.imp (fun C hC => hC.filter_mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds))
  have hVlim (s : ℝ) (hs : s ∈ uIcc 0 t) :=
    (hVlim s hs).mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  let Q (a s : ℝ) := V a s * (a⁻¹ • (A a s - A0)) * X s
  have hcont : ∀ᶠ a in 𝓝[≠] (0 : ℝ), ContinuousOn (Q a) (uIcc 0 t) := by
    filter_upwards [hA, hV] with a ha hv
    exact ((HasDerivAt.continuousOn hv).mul
      ((ha.sub continuousOn_const).const_smul a⁻¹)).mul (HasDerivAt.continuousOn hX)
  have hlim : ∀ s ∈ uIcc 0 t,
      Tendsto (fun a => Q a s) (𝓝[≠] (0 : ℝ)) (𝓝 (V 0 s * D s * X s)) := by
    intro s hs
    exact ((hVlim s hs).mul (hsec s hs)).mul tendsto_const_nhds
  have hint := tendsto_intervalIntegral_of_norm_bound hcont hmajorant hlim
  have hscaled := hint.neg.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => V 0 t)
    (𝓝[≠] (0 : ℝ)) (𝓝 (V 0 t)))
  have hEq : (fun a => a⁻¹ • (V a t - V 0 t)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun a => -(∫ s in 0..t, Q a s) * V 0 t) := by
    filter_upwards [hA, hV, hV0] with a ha hv hzero
    exact secant_duhamel_right ha hv hX hzero hX0 hInv
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add] using hscaled.congr' hEq.symm

end LocalHistoryDerivative
