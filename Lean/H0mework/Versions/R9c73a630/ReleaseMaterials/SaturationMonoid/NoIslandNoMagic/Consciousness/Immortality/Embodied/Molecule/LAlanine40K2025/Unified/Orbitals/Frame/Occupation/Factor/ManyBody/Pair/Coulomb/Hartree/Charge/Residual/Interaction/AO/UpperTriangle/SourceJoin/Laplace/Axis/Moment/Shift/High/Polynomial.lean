import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Gaussian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open MeasureTheory
noncomputable section

def coeff (a b : ℕ) (d e : ℝ) (kl : ℕ × ℕ) : ℝ :=
  (Nat.choose a kl.1 : ℝ) * (Nat.choose b kl.2 : ℝ) *
    d^(a-kl.1) * e^(b-kl.2)

theorem pair_poly_identity (a b : ℕ) (d e y : ℝ)
    (ha : a < 3) (hb : b < 3) :
    (y+d)^a * (y+e)^b =
      ∑ kl ∈ (Finset.range (a+1)).product (Finset.range (b+1)),
        coeff a b d e kl * y^(kl.1+kl.2) := by
  interval_cases a <;> interval_cases b <;>
    simp [coeff, Finset.sum_product, Finset.sum_range_succ, Nat.choose] <;> ring

def pairMomentClosed (a b : ℕ) (d e rate : ℝ) : ℝ :=
  ∑ kl ∈ (Finset.range (a+1)).product (Finset.range (b+1)),
    coeff a b d e kl * rawMoment (kl.1+kl.2) rate

theorem pair_poly_integral (a b : ℕ) (d e rate : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    (∫ y : ℝ, (y+d)^a * (y+e)^b * Real.exp (-rate*y^2)) =
      pairMomentClosed a b d e rate := by
  let domain := (Finset.range (a+1)).product (Finset.range (b+1))
  have hpoint (y : ℝ) :
      (y+d)^a * (y+e)^b * Real.exp (-rate*y^2) =
        ∑ kl ∈ domain,
          coeff a b d e kl * (y^(kl.1+kl.2)*Real.exp (-rate*y^2)) := by
    rw [pair_poly_identity a b d e y ha hb]
    dsimp [domain]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl _
    ring
  simp_rw [hpoint]
  have hint : ∀ kl ∈ domain,
      Integrable (fun y : ℝ =>
        coeff a b d e kl * (y^(kl.1+kl.2)*Real.exp (-rate*y^2))) := by
    intro kl _
    exact (integrable_raw_monomial (kl.1+kl.2) rate hr).const_mul _
  rw [integral_finsetSum domain hint]
  unfold pairMomentClosed
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [integral_const_mul]
  congr 1
  have hpair := Finset.mem_product.mp hkl
  have hk : kl.1 < a+1 := Finset.mem_range.mp hpair.1
  have hl : kl.2 < b+1 := Finset.mem_range.mp hpair.2
  exact raw_moment_integral (kl.1+kl.2) rate (by omega) hr

theorem pair_poly_integrable (a b : ℕ) (d e rate : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    Integrable (fun y : ℝ =>
      (y+d)^a * (y+e)^b * Real.exp (-rate*y^2)) := by
  let domain := (Finset.range (a+1)).product (Finset.range (b+1))
  have hpoint (y : ℝ) :
      (y+d)^a * (y+e)^b * Real.exp (-rate*y^2) =
        ∑ kl ∈ domain,
          coeff a b d e kl * (y^(kl.1+kl.2)*Real.exp (-rate*y^2)) := by
    rw [pair_poly_identity a b d e y ha hb]
    dsimp [domain]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl _
    ring
  simp_rw [hpoint]
  exact integrable_finsetSum domain (fun kl _ =>
    (integrable_raw_monomial (kl.1+kl.2) rate hr).const_mul _)

theorem shifted_pair_gaussian_integral (a b : ℕ) (C D P rate : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    (∫ x : ℝ, (x-C)^a * (x-D)^b * Real.exp (-rate*(x-P)^2)) =
      pairMomentClosed a b (P-C) (P-D) rate := by
  let f : ℝ → ℝ := fun y =>
    (y+(P-C))^a * (y+(P-D))^b * Real.exp (-rate*y^2)
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-P)).integral_comp
    (MeasurableEquiv.addRight (-P)).measurableEmbedding f
  have hfun (x : ℝ) :
      f (x-P) = (x-C)^a * (x-D)^b * Real.exp (-rate*(x-P)^2) := by
    dsimp [f]
    have hC : (x-P)+(P-C) = x-C := by ring
    have hD : (x-P)+(P-D) = x-D := by ring
    rw [hC,hD]
  calc
    (∫ x : ℝ, (x-C)^a * (x-D)^b * Real.exp (-rate*(x-P)^2)) =
        ∫ y : ℝ, f y := by
      calc
        _ = ∫ x : ℝ, f (x-P) := by congr 1; funext x; exact (hfun x).symm
        _ = _ := by simpa only [sub_eq_add_neg] using h
    _ = _ := pair_poly_integral a b (P-C) (P-D) rate ha hb hr

theorem shifted_pair_gaussian_integrable (a b : ℕ) (C D P rate : ℝ)
    (ha : a < 3) (hb : b < 3) (hr : 0 < rate) :
    Integrable (fun x : ℝ =>
      (x-C)^a * (x-D)^b * Real.exp (-rate*(x-P)^2)) := by
  let f : ℝ → ℝ := fun y =>
    (y+(P-C))^a * (y+(P-D))^b * Real.exp (-rate*y^2)
  have h := ((measurePreserving_add_right (volume : Measure ℝ) (-P)).integrable_comp_emb
    (MeasurableEquiv.addRight (-P)).measurableEmbedding).mpr
      (pair_poly_integrable a b (P-C) (P-D) rate ha hb hr)
  change Integrable (fun x : ℝ => f (x-P)) at h
  convert h using 1
  funext x
  dsimp [f]
  have hC : (x-P)+(P-C) = x-C := by ring
  have hD : (x-P)+(P-D) = x-D := by ring
  rw [hC,hD]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
