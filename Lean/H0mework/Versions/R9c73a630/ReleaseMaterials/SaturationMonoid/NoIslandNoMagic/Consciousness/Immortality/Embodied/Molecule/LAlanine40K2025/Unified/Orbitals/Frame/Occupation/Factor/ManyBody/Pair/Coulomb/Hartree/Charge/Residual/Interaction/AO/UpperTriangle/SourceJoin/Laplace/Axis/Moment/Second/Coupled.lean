import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Gaussian

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
noncomputable section

theorem coupled_axis_second (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ x : ℝ, ∫ y : ℝ, (x-A)^2 * coupledAxis p q A B t x y) =
      Real.sqrt (Real.pi/(q+t^2)) *
        Real.exp (-(p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2))*(A-B)^2)) *
        ((centre p (q*t^2/(q+t^2)) A B - A)^2 + 1/(2*(p+q*t^2/(q+t^2)))) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2))) := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hqt : 0 < q+t^2 := add_pos hq ht2
  have hr : 0 < q*t^2/(q+t^2) := div_pos (mul_pos hq ht2) hqt
  have inner (x : ℝ) :
      (∫ y : ℝ, (x-A)^2 * coupledAxis p q A B t x y) =
        (x-A)^2 * Real.exp (-p*(x-A)^2) *
          (Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) *
            Real.sqrt (Real.pi/(q+t^2))) := by
    calc
      _ = ((x-A)^2*Real.exp (-p*(x-A)^2)) *
          (∫ y : ℝ, Real.exp (-q*(y-B)^2) * Real.exp (-(t^2)*(y-x)^2)) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold coupledAxis
        ring
      _ = _ := by rw [two_gaussian_integral q (t^2) B x hq ht2]
  simp_rw [inner]
  calc
    (∫ x : ℝ, (x-A)^2*Real.exp (-p*(x-A)^2) *
      (Real.exp (-(q*t^2/(q+t^2)*(B-x)^2)) * Real.sqrt (Real.pi/(q+t^2)))) =
      Real.sqrt (Real.pi/(q+t^2)) *
        (∫ x : ℝ, (x-A)^2*Real.exp (-p*(x-A)^2) *
          Real.exp (-(q*t^2/(q+t^2))*(x-B)^2)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      have hs : (B-x)^2 = (x-B)^2 := by ring
      rw [hs]
      ring
    _ = _ := by rw [two_gaussian_second p (q*t^2/(q+t^2)) A B hp hr]; ring

theorem shifted_gaussian_second_integrable (b A : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => (x-A)^2 * Real.exp (-b*(x-A)^2)) := by
  have h := ((measurePreserving_add_right (volume : Measure ℝ) (-A)).integrable_comp_emb
    (MeasurableEquiv.addRight (-A)).measurableEmbedding).mpr
      (gaussian_second_integrable b hb)
  simpa only [Function.comp_def,sub_eq_add_neg] using h

theorem coupled_axis_second_integrable (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun z : ℝ × ℝ =>
      (z.1-A)^2 * coupledAxis p q A B t z.1 z.2) := by
  have base := (shifted_gaussian_second_integrable p A hp).mul_prod
    (shifted_gaussian_integrable q B hq)
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

theorem coupled_axis_second_pair (p q A B t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, (z.1-A)^2 * coupledAxis p q A B t z.1 z.2) =
      Real.sqrt (Real.pi/(q+t^2)) *
        Real.exp (-(p*(q*t^2/(q+t^2))/(p+q*t^2/(q+t^2))*(A-B)^2)) *
        ((centre p (q*t^2/(q+t^2)) A B - A)^2 + 1/(2*(p+q*t^2/(q+t^2)))) *
        Real.sqrt (Real.pi/(p+q*t^2/(q+t^2))) := by
  have h := integral_prod
    (fun z : ℝ × ℝ => (z.1-A)^2*coupledAxis p q A B t z.1 z.2)
    (coupled_axis_second_integrable p q A B t hp hq)
  simpa only [Measure.volume_eq_prod] using
    h.trans (coupled_axis_second p q A B t hp hq ht)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
