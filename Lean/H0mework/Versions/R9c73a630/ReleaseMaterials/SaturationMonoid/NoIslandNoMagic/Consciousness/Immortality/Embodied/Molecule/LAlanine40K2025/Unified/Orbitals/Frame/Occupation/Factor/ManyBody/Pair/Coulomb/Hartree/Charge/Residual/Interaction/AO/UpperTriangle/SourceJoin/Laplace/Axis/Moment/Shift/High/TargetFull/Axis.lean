import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Inner

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

def targetDomain (c d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (c+1)).product (Finset.range (d+1))

def targetWeight (c d : ℕ) (rate : ℝ) (key : ℕ × ℕ) : ℝ :=
  (Nat.choose c key.1 : ℝ) * (Nat.choose d key.2 : ℝ) *
    High.rawMoment (key.1+key.2) rate

def outerMomentClosed (a b c d : ℕ)
    (C D P vE vF rateX rateY u : ℝ) : ℝ :=
  ∑ key ∈ targetDomain c d,
    targetWeight c d rateY key *
      fourMomentClosed a b (c-key.1) (d-key.2)
        (P-C) (P-D) vE vF rateX u

theorem outer_moment_integral (a b c d : ℕ)
    (C D P vE vF rateX rateY u : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hx : 0 < rateX) :
    (∫ x : ℝ,
      (x-C)^a * (x-D)^b *
        High.pairMomentClosed c d
          (u*(x-P)+vE) (u*(x-P)+vF) rateY *
        Real.exp (-rateX*(x-P)^2)) =
      outerMomentClosed a b c d C D P vE vF rateX rateY u := by
  let domain := targetDomain c d
  have hpoint (x : ℝ) :
      (x-C)^a * (x-D)^b *
        High.pairMomentClosed c d
          (u*(x-P)+vE) (u*(x-P)+vF) rateY *
        Real.exp (-rateX*(x-P)^2) =
      ∑ key ∈ domain,
        targetWeight c d rateY key *
          ((x-C)^a * (x-D)^b *
            (u*(x-P)+vE)^(c-key.1) *
            (u*(x-P)+vF)^(d-key.2) *
            Real.exp (-rateX*(x-P)^2)) := by
    unfold High.pairMomentClosed
    dsimp [domain]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro key _
    unfold High.coeff targetWeight
    ring
  simp_rw [hpoint]
  have hint : ∀ key ∈ domain,
      Integrable (fun x : ℝ =>
        targetWeight c d rateY key *
          ((x-C)^a * (x-D)^b *
            (u*(x-P)+vE)^(c-key.1) *
            (u*(x-P)+vF)^(d-key.2) *
            Real.exp (-rateX*(x-P)^2))) := by
    intro key hkey
    have hp := Finset.mem_product.mp hkey
    have hk : key.1 < c+1 := Finset.mem_range.mp hp.1
    have hl : key.2 < d+1 := Finset.mem_range.mp hp.2
    exact (shifted_four_poly_integrable a b (c-key.1) (d-key.2)
      C D P vE vF rateX u ha hb (by omega) (by omega) hx).const_mul _
  rw [integral_finsetSum domain hint]
  unfold outerMomentClosed
  apply Finset.sum_congr rfl
  intro key hkey
  rw [integral_const_mul]
  congr 1
  have hp := Finset.mem_product.mp hkey
  have hk : key.1 < c+1 := Finset.mem_range.mp hp.1
  have hl : key.2 < d+1 := Finset.mem_range.mp hp.2
  exact shifted_four_poly_integral a b (c-key.1) (d-key.2)
    C D P vE vF rateX u ha hb (by omega) (by omega) hx

def targetFullAxisClosed (a b c d : ℕ)
    (p q A B C D E F t : ℝ) : ℝ :=
  let r := q*t^2/(q+t^2)
  let P := centre p r A B
  let Q := centre q (t^2) B P
  let u := t^2/(q+t^2)
  Real.exp (-(p*r/(p+r)*(A-B)^2)) *
    outerMomentClosed a b c d C D P (Q-E) (Q-F)
      (p+r) (q+t^2) u

theorem target_full_axis_integral (a b c d : ℕ)
    (p q A B C D E F t : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ,
      targetFullAxisIntegrand a b c d p q A B C D E F t z) =
        targetFullAxisClosed a b c d p q A B C D E F t := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  let r : ℝ := q*t^2/(q+t^2)
  have hr : 0 < r := div_pos (mul_pos hq ht2) hqt
  let P : ℝ := centre p r A B
  let Q : ℝ := centre q (t^2) B P
  let u : ℝ := t^2/(q+t^2)
  have hpq : p+r ≠ 0 := ne_of_gt (add_pos hp hr)
  have hlinE (x : ℝ) :
      centre q (t^2) B x-E = u*(x-P)+(Q-E) := by
    dsimp [u,Q]
    unfold centre
    field_simp [ne_of_gt hqt]
    ring
  have hlinF (x : ℝ) :
      centre q (t^2) B x-F = u*(x-P)+(Q-F) := by
    dsimp [u,Q]
    unfold centre
    field_simp [ne_of_gt hqt]
    ring
  have hprod := integral_prod
    (targetFullAxisIntegrand a b c d p q A B C D E F t)
    (target_full_axis_integrable a b c d p q A B C D E F t
      ha hb hc hd hp hq)
  have hiter :
      (∫ z : ℝ × ℝ,
        targetFullAxisIntegrand a b c d p q A B C D E F t z) =
          ∫ x : ℝ, ∫ y : ℝ,
            targetFullAxisIntegrand a b c d p q A B C D E F t (x,y) := by
    simpa only [Measure.volume_eq_prod] using hprod
  rw [hiter]
  have inner (x : ℝ) :
      (∫ y : ℝ,
        targetFullAxisIntegrand a b c d p q A B C D E F t (x,y)) =
        ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (Real.exp (-(r*(B-x)^2)) *
            High.pairMomentClosed c d
              (centre q (t^2) B x-E)
              (centre q (t^2) B x-F) (q+t^2)) := by
    calc
      _ = ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (∫ y : ℝ,
            (y-E)^c * (y-F)^d * Real.exp (-q*(y-B)^2) *
              Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold targetFullAxisIntegrand Axis.coupledAxis
        ring
      _ = _ := by rw [target_full_inner c d q B E F t x hc hd hq ht]
  simp_rw [inner]
  have hpoint (x : ℝ) :
      ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
        (Real.exp (-(r*(B-x)^2)) *
          High.pairMomentClosed c d
            (centre q (t^2) B x-E)
            (centre q (t^2) B x-F) (q+t^2)) =
        Real.exp (-(p*r/(p+r)*(A-B)^2)) *
          ((x-C)^a * (x-D)^b *
            High.pairMomentClosed c d
              (u*(x-P)+(Q-E)) (u*(x-P)+(Q-F)) (q+t^2) *
            Real.exp (-(p+r)*(x-P)^2)) := by
    have hexp := exponential_product p r A B x hpq
    have hs : (B-x)^2 = (x-B)^2 := by ring
    rw [hs,hlinE,hlinF]
    calc
      _ = ((x-C)^a * (x-D)^b *
            High.pairMomentClosed c d
              (u*(x-P)+(Q-E)) (u*(x-P)+(Q-F)) (q+t^2)) *
            (Real.exp (-p*(x-A)^2) * Real.exp (-r*(x-B)^2)) := by ring
      _ = ((x-C)^a * (x-D)^b *
            High.pairMomentClosed c d
              (u*(x-P)+(Q-E)) (u*(x-P)+(Q-F)) (q+t^2)) *
            (Real.exp (-(p*r/(p+r)*(A-B)^2)) *
              Real.exp (-(p+r)*(x-P)^2)) := by
          dsimp [P]
          rw [hexp]
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    outer_moment_integral a b c d C D P (Q-E) (Q-F)
      (p+r) (q+t^2) u ha hb hc hd (add_pos hp hr)]
  unfold targetFullAxisClosed
  dsimp [r,P,Q,u]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
