import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Coupled

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
noncomputable section

theorem gaussian_first_zero (b : ℝ) :
    (∫ x : ℝ, x * Real.exp (-b*x^2)) = 0 := by
  let f : ℝ → ℝ := fun x => x * Real.exp (-b*x^2)
  have h := Measure.integral_comp_mul_left f (-1 : ℝ)
  have hsame : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    simpa only [neg_one_mul,inv_neg,inv_one,abs_neg,abs_one,one_smul] using h
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    have hs : (-x)^2 = x^2 := by ring
    rw [hs]
    ring
  simp_rw [hodd,integral_neg] at hsame
  change -(∫ x : ℝ, x * Real.exp (-b*x^2)) = _ at hsame
  linarith

theorem shifted_gaussian_first (b a c : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, (x-a) * Real.exp (-b*(x-c)^2)) =
      (c-a) * Real.sqrt (Real.pi / b) := by
  let g : ℝ → ℝ := fun y => (y+(c-a)) * Real.exp (-b*y^2)
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-c)).integral_comp
    (MeasurableEquiv.addRight (-c)).measurableEmbedding g
  have hfun (x : ℝ) : g (x-c) = (x-a) * Real.exp (-b*(x-c)^2) := by
    dsimp [g]
    have heq : (x-c)+(c-a) = x-a := by ring
    rw [heq]
  have htranslate :
      (∫ x : ℝ, (x-a) * Real.exp (-b*(x-c)^2)) = ∫ y : ℝ, g y := by
    calc
      _ = ∫ x : ℝ, g (x-c) := by congr 1; funext x; exact (hfun x).symm
      _ = _ := by simpa only [sub_eq_add_neg] using h
  rw [htranslate]
  have h1 := integrable_mul_exp_neg_mul_sq hb
  have h2 := (integrable_exp_neg_mul_sq hb).const_mul (c-a)
  calc
    (∫ y : ℝ, g y) =
        (∫ y : ℝ, y*Real.exp (-b*y^2)) +
        (∫ y : ℝ, (c-a)*Real.exp (-b*y^2)) := by
      simp only [g,add_mul]
      exact integral_add h1 h2
    _ = _ := by rw [gaussian_first_zero,integral_const_mul,integral_gaussian]; ring

theorem shifted_gaussian_first_integrable (b a : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => (x-a) * Real.exp (-b*(x-a)^2)) := by
  have h := ((measurePreserving_add_right (volume : Measure ℝ) (-a)).integrable_comp_emb
    (MeasurableEquiv.addRight (-a)).measurableEmbedding).mpr
      (integrable_mul_exp_neg_mul_sq hb)
  simpa only [Function.comp_def,sub_eq_add_neg] using h

theorem two_gaussian_first (p q A B : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ x : ℝ, (x-A) * Real.exp (-p*(x-A)^2) *
      Real.exp (-q*(x-B)^2)) =
      Real.exp (-(p*q/(p+q)*(A-B)^2)) *
        (centre p q A B - A) *
        Real.sqrt (Real.pi/(p+q)) := by
  let C := centre p q A B
  have hpq : p+q ≠ 0 := ne_of_gt (add_pos hp hq)
  have pointwise (x : ℝ) :
      (x-A) * Real.exp (-p*(x-A)^2) * Real.exp (-q*(x-B)^2) =
        Real.exp (-(p*q/(p+q)*(A-B)^2)) *
          ((x-A)*Real.exp (-(p+q)*(x-C)^2)) := by
    calc
      _ = (x-A) * (Real.exp (-p*(x-A)^2) * Real.exp (-q*(x-B)^2)) := by ring
      _ = _ := by
        rw [exponential_product p q A B x hpq]
        ring
  simp_rw [pointwise]
  rw [integral_const_mul, shifted_gaussian_first (p+q) A C (add_pos hp hq)]
  dsimp [C]
  ring

theorem coupled_axis_first (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ x : ℝ, ∫ y : ℝ, (x-A) *
      coupledAxis p q A B t x y) =
      Real.sqrt (Real.pi/(q+t^2)) *
        Real.exp (-(p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2))*(A-B)^2)) *
        (centre p (q*t^2/(q+t^2)) A B - A) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2))) := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  have hr : 0 < q*t^2/(q+t^2) := div_pos (mul_pos hq ht2) hqt
  have inner (x : ℝ) :
      (∫ y : ℝ, (x-A) *
        coupledAxis p q A B t x y) =
        (x-A) * Real.exp (-p*(x-A)^2) *
          (Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
            Real.sqrt (Real.pi/(q+t^2))) := by
    calc
      _ = ((x-A)*Real.exp (-p*(x-A)^2)) *
          (∫ y : ℝ, Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold coupledAxis
        ring
      _ = _ := by rw [two_gaussian_integral q (t^2) B x hq ht2]
  simp_rw [inner]
  calc
    (∫ x : ℝ, (x-A)*Real.exp (-p*(x-A)^2) *
      (Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) * Real.sqrt (Real.pi/(q+t^2)))) =
      Real.sqrt (Real.pi/(q+t^2)) *
        (∫ x : ℝ, (x-A)*Real.exp (-p*(x-A)^2) *
          Real.exp (-(q*t^2/(q+t^2))*(x-B)^2)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      have hs : (B-x)^2 = (x-B)^2 := by ring
      rw [hs]
      ring
    _ = _ := by rw [two_gaussian_first p (q*t^2/(q+t^2)) A B hp hr]; ring

theorem coupled_axis_first_integrable (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun z : ℝ × ℝ =>
      (z.1-A) * coupledAxis p q A B t z.1 z.2) := by
  have base := (shifted_gaussian_first_integrable p A hp).mul_prod
    (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.shifted_gaussian_integrable q B hq)
  have heatBound (z : ℝ × ℝ) :
      ‖Real.exp (-(t^2)*(z.2-z.1)^2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
        (sq_nonneg _))
  have heatMeasurable : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-(t^2)*(z.2-z.1)^2)) := by fun_prop
  have result := base.mul_bdd heatMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall heatBound)
  simpa only [Measure.volume_eq_prod,coupledAxis,mul_assoc] using result

theorem coupled_axis_first_pair (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, (z.1-A) * coupledAxis p q A B t z.1 z.2) =
      Real.sqrt (Real.pi/(q+t^2)) *
        Real.exp (-(p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2))*(A-B)^2)) *
        (centre p (q*t^2/(q+t^2)) A B - A) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2))) := by
  have h := integral_prod
    (fun z : ℝ × ℝ => (z.1-A)*coupledAxis p q A B t z.1 z.2)
    (coupled_axis_first_integrable p q A B t hp hq)
  simpa only [Measure.volume_eq_prod] using
    h.trans (coupled_axis_first p q A B t hp hq ht)

theorem coupled_axis_first_same_centre (p q A t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, (z.1-A) * coupledAxis p q A A t z.1 z.2) = 0 := by
  rw [coupled_axis_first_pair p q A A t hp hq ht]
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  have hr : 0 < q*t^2/(q+t^2) := div_pos (mul_pos hq ht2) hqt
  have hcent : centre p (q*t^2/(q+t^2)) A A = A := by
    unfold centre
    field_simp [ne_of_gt (add_pos hp hr)]
  rw [hcent]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
