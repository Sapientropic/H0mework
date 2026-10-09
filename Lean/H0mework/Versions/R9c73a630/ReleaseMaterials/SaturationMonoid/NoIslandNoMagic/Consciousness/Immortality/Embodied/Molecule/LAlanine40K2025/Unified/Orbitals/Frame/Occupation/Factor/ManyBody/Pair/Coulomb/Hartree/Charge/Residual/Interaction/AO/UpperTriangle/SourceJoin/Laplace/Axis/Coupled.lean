import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Gaussian
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

noncomputable def coupledAxis (p q a b t x y : ℝ) : ℝ :=
  Real.exp (-p * (x-a)^2) * Real.exp (-q * (y-b)^2) *
    Real.exp (-(t^2) * (y-x)^2)

theorem coupled_axis_integral (p q a b t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ x : ℝ, ∫ y : ℝ, coupledAxis p q a b t x y) =
      Real.sqrt (Real.pi / (q+t^2)) *
        Real.exp (-(p * (q*t^2/(q+t^2)) /
          (p+q*t^2/(q+t^2)) * (a-b)^2)) *
        Real.sqrt (Real.pi / (p+q*t^2/(q+t^2))) := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  have hr : 0 < q*t^2/(q+t^2) := div_pos (mul_pos hq ht2) hqt
  have inner (x : ℝ) :
      (∫ y : ℝ, coupledAxis p q a b t x y) =
        Real.exp (-p*(x-a)^2) *
          (Real.exp (-(q*t^2/(q+t^2)*(b-x)^2)) *
            Real.sqrt (Real.pi/(q+t^2))) := by
    calc
      (∫ y : ℝ, coupledAxis p q a b t x y) =
          Real.exp (-p*(x-a)^2) *
            (∫ y : ℝ, Real.exp (-q*(y-b)^2) *
              Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold coupledAxis
        ring
      _ = _ := by rw [two_gaussian_integral q (t^2) b x hq ht2]
  simp_rw [inner]
  calc
    (∫ x : ℝ, Real.exp (-p * (x-a)^2) *
      (Real.exp (-(q*t^2/(q+t^2)*(b-x)^2)) *
        Real.sqrt (Real.pi/(q+t^2)))) =
      Real.sqrt (Real.pi/(q+t^2)) *
        (∫ x : ℝ, Real.exp (-p*(x-a)^2) *
          Real.exp (-(q*t^2/(q+t^2))*(x-b)^2)) := by
      calc
        _ = ∫ x : ℝ, Real.sqrt (Real.pi/(q+t^2)) *
            (Real.exp (-p*(x-a)^2) *
              Real.exp (-(q*t^2/(q+t^2))*(x-b)^2)) := by
          congr 1
          funext x
          have hsquare : (b-x)^2 = (x-b)^2 := by ring
          rw [hsquare]
          ring
        _ = _ := integral_const_mul _ _
    _ = _ := by
      rw [two_gaussian_integral p (q*t^2/(q+t^2)) a b hp hr]
      ring

theorem coupled_axis_integrable (p q a b t : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun z : ℝ × ℝ => coupledAxis p q a b t z.1 z.2) := by
  have base := (shifted_gaussian_integrable p a hp).mul_prod
    (shifted_gaussian_integrable q b hq)
  have heatBound (z : ℝ × ℝ) :
      ‖Real.exp (-(t^2)*(z.2-z.1)^2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
        (sq_nonneg _))
  have heatMeasurable : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-(t^2)*(z.2-z.1)^2)) := by fun_prop
  rw [Measure.volume_eq_prod]
  simpa only [coupledAxis] using
    base.mul_bdd heatMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall heatBound)


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
