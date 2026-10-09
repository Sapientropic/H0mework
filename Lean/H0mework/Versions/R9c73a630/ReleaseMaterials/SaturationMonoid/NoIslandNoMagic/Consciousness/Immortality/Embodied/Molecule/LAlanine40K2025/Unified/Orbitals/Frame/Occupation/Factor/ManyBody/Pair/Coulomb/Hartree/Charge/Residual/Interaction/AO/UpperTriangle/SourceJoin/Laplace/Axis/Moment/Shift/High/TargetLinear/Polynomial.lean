import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Gaussian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open MeasureTheory
noncomputable section

def linearMonomial (n : ℕ) (u v rate : ℝ) (y : ℝ) : ℝ :=
  u*(y^(n+1)*Real.exp (-rate*y^2)) +
    v*(y^n*Real.exp (-rate*y^2))

theorem linear_monomial_integrable (n : ℕ) (u v rate : ℝ) (hr : 0 < rate) :
    Integrable (linearMonomial n u v rate) := by
  unfold linearMonomial
  exact ((High.integrable_raw_monomial (n+1) rate hr).const_mul u).add
    ((High.integrable_raw_monomial n rate hr).const_mul v)

theorem linear_monomial_integral (n : ℕ) (u v rate : ℝ)
    (hn : n < 5) (hr : 0 < rate) :
    (∫ y : ℝ, linearMonomial n u v rate y) =
      u*rawMoment5 (n+1) rate + v*rawMoment5 n rate := by
  unfold linearMonomial
  rw [integral_add
    ((High.integrable_raw_monomial (n+1) rate hr).const_mul u)
    ((High.integrable_raw_monomial n rate hr).const_mul v),
    integral_const_mul, integral_const_mul,
    raw_moment_five (n+1) rate (by omega) hr,
    raw_moment_five n rate (by omega) hr]

def pairMomentLinear (a b : ℕ) (d e rate u v : ℝ) : ℝ :=
  ∑ kl ∈ (Finset.range (a+1)).product (Finset.range (b+1)),
    High.coeff a b d e kl *
      (u*rawMoment5 (kl.1+kl.2+1) rate +
        v*rawMoment5 (kl.1+kl.2) rate)

theorem pair_poly_linear_integral (a b : ℕ) (d e rate u v : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    (∫ y : ℝ,
      (y+d)^a * (y+e)^b * (u*y+v) * Real.exp (-rate*y^2)) =
        pairMomentLinear a b d e rate u v := by
  let domain := (Finset.range (a+1)).product (Finset.range (b+1))
  have hpoint (y : ℝ) :
      (y+d)^a * (y+e)^b * (u*y+v) * Real.exp (-rate*y^2) =
        ∑ kl ∈ domain,
          High.coeff a b d e kl *
            linearMonomial (kl.1+kl.2) u v rate y := by
    rw [High.pair_poly_identity a b d e y ha hb]
    dsimp [domain]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl _
    unfold linearMonomial
    rw [pow_succ]
    ring
  simp_rw [hpoint]
  have hint : ∀ kl ∈ domain,
      Integrable (fun y : ℝ =>
        High.coeff a b d e kl *
          linearMonomial (kl.1+kl.2) u v rate y) := by
    intro kl _
    exact (linear_monomial_integrable (kl.1+kl.2) u v rate hr).const_mul _
  rw [integral_finsetSum domain hint]
  unfold pairMomentLinear
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [integral_const_mul]
  congr 1
  have hpair := Finset.mem_product.mp hkl
  have hk : kl.1 < a+1 := Finset.mem_range.mp hpair.1
  have hl : kl.2 < b+1 := Finset.mem_range.mp hpair.2
  exact linear_monomial_integral (kl.1+kl.2) u v rate (by omega) hr

theorem shifted_pair_gaussian_linear_integral (a b : ℕ)
    (C D P rate u v : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    (∫ x : ℝ,
      (x-C)^a * (x-D)^b * (u*(x-P)+v) *
        Real.exp (-rate*(x-P)^2)) =
      pairMomentLinear a b (P-C) (P-D) rate u v := by
  let f : ℝ → ℝ := fun y =>
    (y+(P-C))^a * (y+(P-D))^b * (u*y+v) *
      Real.exp (-rate*y^2)
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-P)).integral_comp
    (MeasurableEquiv.addRight (-P)).measurableEmbedding f
  have hfun (x : ℝ) :
      f (x-P) =
        (x-C)^a * (x-D)^b * (u*(x-P)+v) *
          Real.exp (-rate*(x-P)^2) := by
    dsimp [f]
    have hC : (x-P)+(P-C) = x-C := by ring
    have hD : (x-P)+(P-D) = x-D := by ring
    rw [hC,hD]
  calc
    (∫ x : ℝ,
      (x-C)^a * (x-D)^b * (u*(x-P)+v) *
        Real.exp (-rate*(x-P)^2)) = ∫ y : ℝ, f y := by
      calc
        _ = ∫ x : ℝ, f (x-P) := by congr 1; funext x; exact (hfun x).symm
        _ = _ := by simpa only [sub_eq_add_neg] using h
    _ = _ := pair_poly_linear_integral a b (P-C) (P-D) rate u v ha hb hr

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
