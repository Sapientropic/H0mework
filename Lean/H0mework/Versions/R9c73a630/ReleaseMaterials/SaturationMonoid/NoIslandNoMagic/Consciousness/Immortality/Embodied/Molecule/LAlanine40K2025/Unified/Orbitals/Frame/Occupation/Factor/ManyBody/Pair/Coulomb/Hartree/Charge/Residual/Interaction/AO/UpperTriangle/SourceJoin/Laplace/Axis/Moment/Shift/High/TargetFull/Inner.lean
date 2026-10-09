import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Axis

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

theorem target_full_inner (c d : ℕ) (q B E F t x : ℝ)
    (hc : c < 3) (hd : d < 3) (hq : 0 < q) (ht : 0 < t) :
    (∫ y : ℝ,
      (y-E)^c * (y-F)^d *
        Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2)) =
      Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
        High.pairMomentClosed c d
          (centre q (t^2) B x-E)
          (centre q (t^2) B x-F) (q+t^2) := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  let Q : ℝ := centre q (t^2) B x
  have hpoint (y : ℝ) :
      (y-E)^c * (y-F)^d *
          Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2) =
        Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
          ((y-E)^c * (y-F)^d * Real.exp (-(q+t^2)*(y-Q)^2)) := by
    have hexp := exponential_product q (t^2) B x y (ne_of_gt hqt)
    calc
      _ = ((y-E)^c * (y-F)^d) *
            (Real.exp (-q*(y-B)^2) *
              Real.exp (-(t^2)*(y-x)^2)) := by ring
      _ = ((y-E)^c * (y-F)^d) *
            (Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
              Real.exp (-(q+t^2)*(y-Q)^2)) := by
          dsimp [Q]
          rw [hexp]
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  rw [High.shifted_pair_gaussian_integral c d E F Q (q+t^2)
    hc hd hqt]

def targetFullAxisIntegrand (a b c d : ℕ)
    (p q A B C D E F t : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1-C)^a * (z.1-D)^b * (z.2-E)^c * (z.2-F)^d *
    Axis.coupledAxis p q A B t z.1 z.2

theorem target_full_axis_integrable (a b c d : ℕ)
    (p q A B C D E F t : ℝ)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hp : 0 < p) (hq : 0 < q) :
    Integrable (targetFullAxisIntegrand a b c d p q A B C D E F t) := by
  have hx := High.shifted_pair_gaussian_integrable a b C D A p ha hb hp
  have hy := High.shifted_pair_gaussian_integrable c d E F B q hc hd hq
  have base := hx.mul_prod hy
  have heatBound (z : ℝ × ℝ) :
      ‖Real.exp (-(t^2)*(z.2-z.1)^2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
        (sq_nonneg _))
  have heatMeasurable : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-(t^2)*(z.2-z.1)^2)) := by fun_prop
  have result := base.mul_bdd heatMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall heatBound)
  have hfun : targetFullAxisIntegrand a b c d p q A B C D E F t =
      (fun z : ℝ × ℝ =>
        ((z.1-C)^a * (z.1-D)^b * Real.exp (-p*(z.1-A)^2)) *
          ((z.2-E)^c * (z.2-F)^d * Real.exp (-q*(z.2-B)^2)) *
          Real.exp (-(t^2)*(z.2-z.1)^2)) := by
    funext z
    dsimp [targetFullAxisIntegrand, Axis.coupledAxis]
    ring
  rw [hfun]
  simpa only [Measure.volume_eq_prod] using result

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
