import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Coupled

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

def axisPairIntegrand (a b : ℕ) (p q A B C D t : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1-C)^a * (z.1-D)^b * Axis.coupledAxis p q A B t z.1 z.2

def axisPairClosed (a b : ℕ) (p q A B C D t : ℝ) : ℝ :=
  let r := q*t^2/(q+t^2)
  Real.sqrt (Real.pi/(q+t^2)) *
    Real.exp (-(p*r/(p+r)*(A-B)^2)) *
      pairMomentClosed a b
        (centre p r A B-C) (centre p r A B-D) (p+r)

theorem axis_pair_integrable (a b : ℕ) (p q A B C D t : ℝ)
    (ha : a < 3) (hb : b < 3) (hp : 0 < p) (hq : 0 < q) :
    Integrable (axisPairIntegrand a b p q A B C D t) := by
  have base := (shifted_pair_gaussian_integrable a b C D A p ha hb hp).mul_prod
    (Axis.shifted_gaussian_integrable q B hq)
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
  have hfun : axisPairIntegrand a b p q A B C D t =
      (fun z : ℝ × ℝ =>
        (z.1-C)^a * (z.1-D)^b * Real.exp (-p*(z.1-A)^2) *
          Real.exp (-q*(z.2-B)^2) *
          Real.exp (-(t^2)*(z.2-z.1)^2)) := by
    funext z
    dsimp [axisPairIntegrand, Axis.coupledAxis]
    ring
  rw [hfun]
  simpa only [Measure.volume_eq_prod] using result

theorem axis_pair_integral (a b : ℕ) (p q A B C D t : ℝ)
    (ha : a < 3) (hb : b < 3)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, axisPairIntegrand a b p q A B C D t z) =
      axisPairClosed a b p q A B C D t := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  let r : ℝ := q*t^2/(q+t^2)
  have hr : 0 < r := div_pos (mul_pos hq ht2) hqt
  let P : ℝ := centre p r A B
  have hpq : p+r ≠ 0 := ne_of_gt (add_pos hp hr)
  have inner (x : ℝ) :
      (∫ y : ℝ,
        (x-C)^a * (x-D)^b * Axis.coupledAxis p q A B t x y) =
        ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (Real.exp (-(r*(B-x)^2)) *
            Real.sqrt (Real.pi/(q+t^2))) := by
    calc
      _ = ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
          (∫ y : ℝ, Real.exp (-q*(y-B)^2) *
            Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold Axis.coupledAxis
        ring
      _ = _ := by rw [Axis.two_gaussian_integral q (t^2) B x hq ht2]
  have hprod := integral_prod
    (axisPairIntegrand a b p q A B C D t)
    (axis_pair_integrable a b p q A B C D t ha hb hp hq)
  have hiter :
      (∫ z : ℝ × ℝ, axisPairIntegrand a b p q A B C D t z) =
        ∫ x : ℝ, ∫ y : ℝ, axisPairIntegrand a b p q A B C D t (x,y) := by
    simpa only [Measure.volume_eq_prod] using hprod
  rw [hiter]
  simp_rw [axisPairIntegrand,inner]
  have hpoint (x : ℝ) :
      ((x-C)^a * (x-D)^b * Real.exp (-p*(x-A)^2)) *
        (Real.exp (-(r*(B-x)^2)) * Real.sqrt (Real.pi/(q+t^2))) =
        Real.sqrt (Real.pi/(q+t^2)) *
          (Real.exp (-(p*r/(p+r)*(A-B)^2)) *
            ((x-C)^a * (x-D)^b * Real.exp (-(p+r)*(x-P)^2))) := by
    have hexp := exponential_product p r A B x hpq
    have hs : (B-x)^2 = (x-B)^2 := by ring
    rw [hs]
    calc
      _ = Real.sqrt (Real.pi/(q+t^2)) *
            ((x-C)^a * (x-D)^b *
              (Real.exp (-p*(x-A)^2) * Real.exp (-r*(x-B)^2))) := by ring
      _ = Real.sqrt (Real.pi/(q+t^2)) *
            ((x-C)^a * (x-D)^b *
              (Real.exp (-(p*r/(p+r)*(A-B)^2)) *
                Real.exp (-(p+r)*(x-P)^2))) := by
          dsimp [P]
          rw [hexp]
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_const_mul,
    shifted_pair_gaussian_integral a b C D P (p+r) ha hb (add_pos hp hr)]
  unfold axisPairClosed
  dsimp [r,P]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
