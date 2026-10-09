import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Coupled

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

theorem coupled_axis_determinant (p q t : ℝ)
    (hq : 0 < q) :
    (q+t^2) * (p+q*t^2/(q+t^2)) = p*q+(p+q)*t^2 := by
  have hqt : q+t^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hq (sq_nonneg t))
  field_simp [hqt]
  ring

theorem coupled_axis_exponent (p q t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2)) =
      p*q*t^2/(p*q+(p+q)*t^2) := by
  have hqt : 0 < q+t^2 := add_pos hq (sq_pos_of_pos ht)
  have hpr : 0 < p+q*t^2/(q+t^2) :=
    add_pos hp (div_pos (mul_pos hq (sq_pos_of_pos ht)) hqt)
  rw [← coupled_axis_determinant p q t hq]
  field_simp [ne_of_gt hqt,ne_of_gt hpr]

theorem coupled_axis_sqrt (p q t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    Real.sqrt (Real.pi/(q+t^2)) *
      Real.sqrt (Real.pi/(p+q*t^2/(q+t^2))) =
        Real.pi / Real.sqrt (p*q+(p+q)*t^2) := by
  have hqt : 0 < q+t^2 := add_pos hq (sq_pos_of_pos ht)
  have hpr : 0 < p+q*t^2/(q+t^2) :=
    add_pos hp (div_pos (mul_pos hq (sq_pos_of_pos ht)) hqt)
  rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi/(q+t^2))]
  have fraction :
      (Real.pi/(q+t^2))*(Real.pi/(p+q*t^2/(q+t^2))) =
      Real.pi^2/(p*q+(p+q)*t^2) := by
    rw [← coupled_axis_determinant p q t hq]
    field_simp [ne_of_gt hqt,ne_of_gt hpr]
  rw [fraction,Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,
    abs_of_pos Real.pi_pos]

theorem coupled_axis_closed (p q a b t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ x : ℝ, ∫ y : ℝ, coupledAxis p q a b t x y) =
      (Real.pi / Real.sqrt (p*q+(p+q)*t^2)) *
        Real.exp (-(p*q*t^2/(p*q+(p+q)*t^2) * (a-b)^2)) := by
  rw [coupled_axis_integral p q a b t hp hq ht]
  calc
    Real.sqrt (Real.pi / (q+t^2)) *
        Real.exp (-(p * (q*t^2/(q+t^2)) /
          (p+q*t^2/(q+t^2)) * (a-b)^2)) *
        Real.sqrt (Real.pi / (p+q*t^2/(q+t^2))) =
      (Real.sqrt (Real.pi/(q+t^2)) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2)))) *
          Real.exp (-(p*(q*t^2/(q+t^2)) /
            (p+q*t^2/(q+t^2))*(a-b)^2)) := by ring
    _ = _ := by
      rw [coupled_axis_sqrt p q t hp hq ht,
        coupled_axis_exponent p q t hp hq ht]

theorem coupled_axis_pair_closed (p q a b t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, coupledAxis p q a b t z.1 z.2) =
      (Real.pi / Real.sqrt (p*q+(p+q)*t^2)) *
        Real.exp (-(p*q*t^2/(p*q+(p+q)*t^2) * (a-b)^2)) := by
  have h := integral_prod
    (fun z : ℝ × ℝ => coupledAxis p q a b t z.1 z.2)
    (coupled_axis_integrable p q a b t hp hq)
  simpa only [Measure.volume_eq_prod] using
    h.trans (coupled_axis_closed p q a b t hp hq ht)


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
