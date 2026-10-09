import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Gaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Polynomial

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open MeasureTheory
noncomputable section

def fourDomain (a b c d : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.range (a+1)).product (Finset.range (b+1))).product
    ((Finset.range (c+1)).product (Finset.range (d+1)))

def fourCoeff (a b c d : ℕ) (sC sD tE tF u : ℝ)
    (key : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  High.coeff a b sC sD key.1 *
    High.coeff c d tE tF key.2 *
      u^(key.2.1+key.2.2)

def fourMomentClosed (a b c d : ℕ) (sC sD tE tF rate u : ℝ) : ℝ :=
  ∑ key ∈ fourDomain a b c d,
    fourCoeff a b c d sC sD tE tF u key *
      rawMoment8 (key.1.1+key.1.2+key.2.1+key.2.2) rate

theorem four_poly_identity (a b c d : ℕ) (sC sD tE tF u z : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3) :
    (z+sC)^a * (z+sD)^b * (u*z+tE)^c * (u*z+tF)^d =
      ∑ key ∈ fourDomain a b c d,
        fourCoeff a b c d sC sD tE tF u key *
          z^(key.1.1+key.1.2+key.2.1+key.2.2) := by
  interval_cases a <;> interval_cases b <;>
    interval_cases c <;> interval_cases d <;>
      simp [fourDomain,fourCoeff,High.coeff,
        Finset.sum_product,Finset.sum_range_succ,Nat.choose] <;> ring

theorem four_poly_integral (a b c d : ℕ)
    (sC sD tE tF rate u : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hr : 0 < rate) :
    (∫ z : ℝ,
      (z+sC)^a * (z+sD)^b * (u*z+tE)^c * (u*z+tF)^d *
        Real.exp (-rate*z^2)) =
      fourMomentClosed a b c d sC sD tE tF rate u := by
  let domain := fourDomain a b c d
  have hpoint (z : ℝ) :
      (z+sC)^a * (z+sD)^b * (u*z+tE)^c * (u*z+tF)^d *
          Real.exp (-rate*z^2) =
        ∑ key ∈ domain,
          fourCoeff a b c d sC sD tE tF u key *
            (z^(key.1.1+key.1.2+key.2.1+key.2.2) *
              Real.exp (-rate*z^2)) := by
    rw [four_poly_identity a b c d sC sD tE tF u z ha hb hc hd]
    dsimp [domain]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro key _
    ring
  simp_rw [hpoint]
  have hint : ∀ key ∈ domain,
      Integrable (fun z : ℝ =>
        fourCoeff a b c d sC sD tE tF u key *
          (z^(key.1.1+key.1.2+key.2.1+key.2.2) *
            Real.exp (-rate*z^2))) := by
    intro key _
    exact (High.integrable_raw_monomial
      (key.1.1+key.1.2+key.2.1+key.2.2) rate hr).const_mul _
  rw [integral_finsetSum domain hint]
  unfold fourMomentClosed
  apply Finset.sum_congr rfl
  intro key hkey
  rw [integral_const_mul]
  congr 1
  have houter := Finset.mem_product.mp hkey
  have hsource := Finset.mem_product.mp houter.1
  have htarget := Finset.mem_product.mp houter.2
  have ha' : key.1.1 < a+1 := Finset.mem_range.mp hsource.1
  have hb' : key.1.2 < b+1 := Finset.mem_range.mp hsource.2
  have hc' : key.2.1 < c+1 := Finset.mem_range.mp htarget.1
  have hd' : key.2.2 < d+1 := Finset.mem_range.mp htarget.2
  exact raw_moment_eight
    (key.1.1+key.1.2+key.2.1+key.2.2) rate (by omega) hr

theorem four_poly_integrable (a b c d : ℕ)
    (sC sD tE tF rate u : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hr : 0 < rate) :
    Integrable (fun z : ℝ =>
      (z+sC)^a * (z+sD)^b * (u*z+tE)^c * (u*z+tF)^d *
        Real.exp (-rate*z^2)) := by
  let domain := fourDomain a b c d
  have hpoint (z : ℝ) :
      (z+sC)^a * (z+sD)^b * (u*z+tE)^c * (u*z+tF)^d *
          Real.exp (-rate*z^2) =
        ∑ key ∈ domain,
          fourCoeff a b c d sC sD tE tF u key *
            (z^(key.1.1+key.1.2+key.2.1+key.2.2) *
              Real.exp (-rate*z^2)) := by
    rw [four_poly_identity a b c d sC sD tE tF u z ha hb hc hd]
    dsimp [domain]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro key _
    ring
  simp_rw [hpoint]
  exact integrable_finsetSum domain (fun key _ =>
    (High.integrable_raw_monomial
      (key.1.1+key.1.2+key.2.1+key.2.2) rate hr).const_mul _)

theorem shifted_four_poly_integral (a b c d : ℕ)
    (C D P tE tF rate u : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hr : 0 < rate) :
    (∫ x : ℝ,
      (x-C)^a * (x-D)^b * (u*(x-P)+tE)^c *
        (u*(x-P)+tF)^d * Real.exp (-rate*(x-P)^2)) =
      fourMomentClosed a b c d (P-C) (P-D) tE tF rate u := by
  let f : ℝ → ℝ := fun z =>
    (z+(P-C))^a * (z+(P-D))^b * (u*z+tE)^c *
      (u*z+tF)^d * Real.exp (-rate*z^2)
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-P)).integral_comp
    (MeasurableEquiv.addRight (-P)).measurableEmbedding f
  have hfun (x : ℝ) :
      f (x-P) = (x-C)^a * (x-D)^b * (u*(x-P)+tE)^c *
        (u*(x-P)+tF)^d * Real.exp (-rate*(x-P)^2) := by
    dsimp [f]
    have hC : (x-P)+(P-C) = x-C := by ring
    have hD : (x-P)+(P-D) = x-D := by ring
    rw [hC,hD]
  calc
    (∫ x : ℝ,
      (x-C)^a * (x-D)^b * (u*(x-P)+tE)^c *
        (u*(x-P)+tF)^d * Real.exp (-rate*(x-P)^2)) =
        ∫ z : ℝ, f z := by
      calc
        _ = ∫ x : ℝ, f (x-P) := by congr 1; funext x; exact (hfun x).symm
        _ = _ := by simpa only [sub_eq_add_neg] using h
    _ = _ := four_poly_integral a b c d (P-C) (P-D) tE tF rate u
      ha hb hc hd hr

theorem shifted_four_poly_integrable (a b c d : ℕ)
    (C D P tE tF rate u : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hr : 0 < rate) :
    Integrable (fun x : ℝ =>
      (x-C)^a * (x-D)^b * (u*(x-P)+tE)^c *
        (u*(x-P)+tF)^d * Real.exp (-rate*(x-P)^2)) := by
  let f : ℝ → ℝ := fun z =>
    (z+(P-C))^a * (z+(P-D))^b * (u*z+tE)^c *
      (u*z+tF)^d * Real.exp (-rate*z^2)
  have h := ((measurePreserving_add_right (volume : Measure ℝ) (-P)).integrable_comp_emb
    (MeasurableEquiv.addRight (-P)).measurableEmbedding).mpr
      (four_poly_integrable a b c d (P-C) (P-D) tE tF rate u
        ha hb hc hd hr)
  change Integrable (fun x : ℝ => f (x-P)) at h
  convert h using 1
  funext x
  dsimp [f]
  have hC : (x-P)+(P-C) = x-C := by ring
  have hD : (x-P)+(P-D) = x-D := by ring
  rw [hC,hD]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
