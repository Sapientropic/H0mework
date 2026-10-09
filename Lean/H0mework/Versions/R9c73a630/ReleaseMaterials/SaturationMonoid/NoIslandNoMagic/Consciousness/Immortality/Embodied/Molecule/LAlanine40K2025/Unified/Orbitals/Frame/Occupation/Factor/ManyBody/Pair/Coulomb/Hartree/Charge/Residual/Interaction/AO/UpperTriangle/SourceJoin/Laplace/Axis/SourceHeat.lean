import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
open BasinRefinement.GlobalSource
open BasinRefinement.SourceCoulomb
open MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open scoped BigOperators
noncomputable section

theorem heat_spatial_exp (z : Point × Point) (t : ℝ) :
    Real.exp (-(distance (z.2-z.1))^2*t^2) =
      ∏ i : Fin 3, Real.exp (-(t^2)*(z.2 i-z.1 i)^2) := by
  have hs : 0 ≤ ∑ i : Fin 3, ((z.2-z.1) i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold distance
  rw [Real.sq_sqrt hs]
  rw [← Real.exp_sum]
  congr 1
  simp only [Pi.sub_apply]
  rw [← Finset.mul_sum]
  ring

theorem original_s_heat_pointwise (z : Point × Point) (t : ℝ) :
    heatIntegrand originalS originalS originalS originalS z t =
      originalWeight^4 * (2 / Real.sqrt Real.pi) *
        spatialSCoupled (fun _ => 2*originalAlpha)
          (fun _ => 2*originalAlpha)
          originalCentre originalCentre t z := by
  unfold heatIntegrand primitiveAmplitude
  rw [original_s_pair_field z.1,original_s_pair_field z.2,
    heat_spatial_exp z t]
  unfold spatialSCoupled coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem original_s_heat_inner_closed (t : ℝ) (ht : 0 < t) :
    (∫ z : Point × Point,
      heatIntegrand originalS originalS originalS originalS z t) =
      originalWeight^4 * (2 / Real.sqrt Real.pi) *
        ∏ i : Fin 3,
          (Real.pi / Real.sqrt
            ((2*originalAlpha)*(2*originalAlpha) +
              ((2*originalAlpha)+(2*originalAlpha))*t^2)) *
            Real.exp
              (-(((2*originalAlpha)*(2*originalAlpha)*t^2) /
                ((2*originalAlpha)*(2*originalAlpha) +
                  ((2*originalAlpha)+(2*originalAlpha))*t^2) *
                (originalCentre i-originalCentre i)^2)) := by
  simp_rw [original_s_heat_pointwise]
  rw [integral_const_mul]
  have hp : ∀ i : Fin 3, 0 < (fun _ => 2*originalAlpha) i := by
    intro i
    have ha : 0 < originalAlpha := by
      unfold originalAlpha
      exact_mod_cast original_s_exponent
    exact mul_pos (by norm_num) ha
  rw [spatial_s_factor _ _ originalCentre originalCentre t hp hp ht]

theorem original_s_heat_inner_simple (t : ℝ) (ht : 0 < t) :
    (∫ z : Point × Point,
      heatIntegrand originalS originalS originalS originalS z t) =
      originalWeight^4 * (2 / Real.sqrt Real.pi) *
        (Real.pi / Real.sqrt
          ((2*originalAlpha)*(2*originalAlpha) +
            ((2*originalAlpha)+(2*originalAlpha))*t^2))^3 := by
  rw [original_s_heat_inner_closed t ht]
  simp only [sub_self,pow_succ,pow_zero,mul_zero,neg_zero,
    Real.exp_zero,mul_one]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero]
  ring


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
