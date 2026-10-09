import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Axis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025 UnifiedOrbitals BasinRefinement SourceGaussianModel Polynomial MeasureTheory Set
open scoped BigOperators intervalIntegral Topology
noncomputable section

/-- The compactifying substitution `u ↦ t`: `u = t/√(γ+t²)` inverted as
`t = u·√γ/√(1−u²)`, mapping `(0,1)` onto `Ioi 0`. -/
noncomputable def substMap (γ : ℝ) (u : ℝ) : ℝ :=
  u * Real.sqrt γ / Real.sqrt (1 - u^2)

/-- Derivative of the substitution: `√γ/(1−u²)^{3/2}` written without rpow. -/
def substDeriv (γ : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt γ / ((1 - u^2) * Real.sqrt (1 - u^2))

private theorem substMap_deriv (γ : ℝ) (hγ : 0 < γ) (u : ℝ)
    (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (substMap γ) (substDeriv γ u) u := by
  have hw : 0 < 1 - u^2 := by nlinarith [hu.1, hu.2]
  have hsw : Real.sqrt (1 - u^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  have hinner : HasDerivAt (fun u : ℝ => 1 - u^2) (-2*u) u := by
    simpa using (hasDerivAt_pow 2 u).const_sub (1:ℝ)
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (1 - u^2))
      (-2*u/(2*Real.sqrt (1-u^2))) u := hinner.sqrt (ne_of_gt hw)
  have hnum : HasDerivAt (fun u : ℝ => u * Real.sqrt γ) (Real.sqrt γ) u := by
    simpa using (hasDerivAt_id' u).mul_const (Real.sqrt γ)
  have hdiv := hnum.div hsqrt hsw
  have hder : substDeriv γ u =
      (Real.sqrt γ * Real.sqrt (1-u^2) - u * Real.sqrt γ *
        (-2*u/(2*Real.sqrt (1-u^2)))) / (Real.sqrt (1-u^2))^2 := by
    unfold substDeriv
    have hs1 : (Real.sqrt (1-u^2))^2 = 1 - u^2 := Real.sq_sqrt hw.le
    rw [div_eq_iff (ne_of_gt (by positivity : (0:ℝ) < (1-u^2)*Real.sqrt (1-u^2)))]
    field_simp [hsw]
    nlinarith [hs1, Real.sqrt_pos.mpr hw]
  rw [hder]
  exact hdiv

private theorem substMap_inj (γ : ℝ) (hγ : 0 < γ) :
    InjOn (substMap γ) (Ioo (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hxw : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hyw : 0 < 1 - y^2 := by nlinarith [hy.1, hy.2]
  have hγs : Real.sqrt γ ≠ 0 := Real.sqrt_ne_zero'.mpr hγ
  have hsx : Real.sqrt (1 - x^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hxw
  have hsy : Real.sqrt (1 - y^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hyw
  unfold substMap at hxy
  field_simp [hsx, hsy] at hxy
  have hsq := congrArg (fun z : ℝ => z^2) hxy
  rw [mul_pow, mul_pow, Real.sq_sqrt hxw.le, Real.sq_sqrt hyw.le] at hsq
  have hxx : x^2 = y^2 := by nlinarith [hsq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxx with h | h
  · exact h
  · exfalso
    nlinarith [hx.1, hy.1]

private theorem substMap_image (γ : ℝ) (hγ : 0 < γ) :
    substMap γ '' Ioo (0:ℝ) 1 = Ioi 0 := by
  ext t
  simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨u, ⟨h0, h1⟩, rfl⟩
    have hw : 0 < 1 - u^2 := by nlinarith [h0, h1]
    unfold substMap
    positivity
  · intro ht
    refine ⟨t/Real.sqrt (γ + t^2), ⟨?_, ?_⟩, ?_⟩
    · have hγt : 0 < γ + t^2 := by positivity
      positivity
    · have hγt : 0 < γ + t^2 := by positivity
      rw [div_lt_one (Real.sqrt_pos.mpr hγt)]
      exact Real.lt_sqrt_of_sq_lt (by nlinarith [ht, hγ])
    · have hγt : 0 < γ + t^2 := by positivity
      have hst : Real.sqrt (γ + t^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hγt
      have hγs : Real.sqrt γ ≠ 0 := Real.sqrt_ne_zero'.mpr hγ
      have hw : 1 - (t/Real.sqrt (γ+t^2))^2 = γ/(γ+t^2) := by
        rw [div_pow, Real.sq_sqrt hγt.le]
        field_simp [hγt.ne']
        ring
      have hsw : Real.sqrt (1 - (t/Real.sqrt (γ+t^2))^2) =
          Real.sqrt γ/Real.sqrt (γ+t^2) := by
        rw [hw, Real.sqrt_div hγ.le]
      unfold substMap
      rw [hsw]
      field_simp [hγs, hst]

/-- Change of variables `t = u·√γ/√(1−u²)` from `Ioi 0` onto `(0,1)`:
`∫_{t>0} g = ∫_{0<u<1} g(t(u))·√γ/((1−u²)√(1−u²))`. -/
theorem subst_integral (γ : ℝ) (hγ : 0 < γ) (g : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ), g t) =
      ∫ u in Ioo (0 : ℝ) 1, g (substMap γ u) * substDeriv γ u := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun u hu => (substMap_deriv γ hγ u hu).hasDerivWithinAt)
    (substMap_inj γ hγ) g
  rw [substMap_image γ hγ] at h
  refine h.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hw : 0 < 1 - u^2 := by nlinarith [hu.1, hu.2]
  have hpos : 0 < substDeriv γ u := by
    unfold substDeriv
    positivity
  simp only [abs_of_pos hpos, smul_eq_mul]
  ring

/-- Under `t = u√γ/√(1−u²)` we have `γ + t² = γ/(1−u²)`. -/
theorem substMap_sq_add (γ : ℝ) (hγ : 0 < γ) (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    γ + (substMap γ u)^2 = γ/(1 - u^2) := by
  have hw : 0 < 1 - u^2 := by nlinarith [hu.1, hu.2]
  have hsw : Real.sqrt (1 - u^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  unfold substMap
  rw [div_pow, mul_pow, Real.sq_sqrt hw.le, Real.sq_sqrt hγ.le]
  field_simp [hw.ne']
  ring

/-- Under the substitution, `t²/(γ+t²) = u²`. -/
theorem substMap_ratio (γ : ℝ) (hγ : 0 < γ) (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (substMap γ u)^2/(γ + (substMap γ u)^2) = u^2 := by
  rw [substMap_sq_add γ hγ u hu]
  have hw : 0 < 1 - u^2 := by nlinarith [hu.1, hu.2]
  have hsw : Real.sqrt (1 - u^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  have hγt : (0:ℝ) < γ/(1-u^2) := by positivity
  unfold substMap
  rw [div_pow, mul_pow, Real.sq_sqrt hw.le, Real.sq_sqrt hγ.le]
  field_simp [hw.ne', hγt.ne']

/-- The full measure-density simplification:
`(π/(γ+t(u)²))^{3/2}·t'(u) = π^{3/2}/γ`, with `x^{3/2} = x·√x`. -/
theorem subst_density (γ : ℝ) (hγ : 0 < γ) (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (Real.sqrt (Real.pi/(γ + (substMap γ u)^2)))^3 * substDeriv γ u =
      Real.pi * Real.sqrt Real.pi/γ := by
  have hw : 0 < 1 - u^2 := by nlinarith [hu.1, hu.2]
  have hsw : Real.sqrt (1 - u^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  have hγs : Real.sqrt γ ≠ 0 := Real.sqrt_ne_zero'.mpr hγ
  rw [substMap_sq_add γ hγ u hu]
  rw [show Real.pi/(γ/(1-u^2)) = (Real.pi/γ) * (1-u^2) by
    field_simp [hγ.ne', hw.ne']]
  rw [Real.sqrt_mul (by positivity)]
  unfold substDeriv
  have hw3 : (Real.sqrt (1-u^2))^3 = (1-u^2) * Real.sqrt (1-u^2) := by
    rw [pow_succ, Real.sq_sqrt hw.le]
  rw [mul_pow, hw3]
  have hP3 : (Real.sqrt (Real.pi/γ))^3 = (Real.pi/γ)*Real.sqrt (Real.pi/γ) := by
    rw [pow_succ, Real.sq_sqrt (by positivity)]
  rw [hP3]
  have hrt : Real.sqrt (Real.pi/γ) * Real.sqrt γ = Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ Real.pi/γ by positivity)]
    congr 1
    exact div_mul_cancel₀ _ hγ.ne'
  have hD : ((1-u^2)*Real.sqrt (1-u^2)) ≠ 0 := by positivity
  rw [show Real.pi / γ * √(Real.pi / γ) * ((1-u^2) * √(1-u^2)) *
        (√γ/((1-u^2)*√(1-u^2))) =
      Real.pi / γ * √(Real.pi / γ) * √γ by
    field_simp [hD]]
  rw [mul_assoc (Real.pi/γ) _ _, hrt, div_mul_eq_mul_div]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
