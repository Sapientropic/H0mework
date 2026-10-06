import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Integral
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Charge.Consumer
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient GlobalSource MeasureTheory
open scoped Matrix BigOperators InnerProductSpace
noncomputable section

def projectedDensity (x : Point) : ℝ := 2 * (oneBodyKernel x x).re
def densityResidual (x : Point) : ℝ := sourceDensity x - projectedDensity x

theorem projected_density_norm (x : Point) :
    projectedDensity x = 2 * ‖occupiedVector x‖^2 := by
  rw [projectedDensity,kernel_inner]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem kernel_diagonal_integrable : Integrable (fun x : Point => oneBodyKernel x x) := by
  have each (i k : Basis) : Integrable (fun x : Point =>
      projector24 i k * (normalizedOrbital i x : ℂ) * (normalizedOrbital k x : ℂ)) := by
    convert ((normalized_pair_integrable i k).ofReal.const_mul (projector24 i k)) using 1
    funext x
    push_cast
    simp only [mul_assoc]
    rfl
  simp only [oneBodyKernel]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => each i k))

theorem projected_density_integrable : Integrable projectedDensity := by
  exact kernel_diagonal_integrable.re.const_mul 2

theorem kernel_diagonal_charge :
    (∫ x : Point, oneBodyKernel x x) = (24 : ℂ) := by
  have each (i k : Basis) : Integrable (fun x : Point =>
      projector24 i k * (normalizedOrbital i x : ℂ) * (normalizedOrbital k x : ℂ)) := by
    convert ((normalized_pair_integrable i k).ofReal.const_mul (projector24 i k)) using 1
    funext x
    push_cast
    simp only [mul_assoc]
    rfl
  simp only [oneBodyKernel]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => each i k))]
  calc
    (∑ i : Basis, ∫ x : Point,
        ∑ k : Basis, projector24 i k * (normalizedOrbital i x : ℂ) *
          (normalizedOrbital k x : ℂ)) =
      ∑ i : Basis, ∑ k : Basis,
        projector24 i k * ((if i = k then 1 else 0 : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum _ (fun k _ => each i k)]
          apply Finset.sum_congr rfl
          intro k _
          calc
            (∫ x : Point, projector24 i k * (normalizedOrbital i x : ℂ) *
                (normalizedOrbital k x : ℂ)) =
              ∫ x : Point, projector24 i k *
                ((normalizedOrbital i x * normalizedOrbital k x : ℝ) : ℂ) := by
                  congr 1
                  funext x
                  push_cast
                  ring
            _ = _ := by
              rw [integral_const_mul,integral_complex_ofReal,
                normalized_pair actual_gram_positive i k]
    _ = projector24.trace := by
      classical
      rw [Matrix.trace]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ k : Basis, projector24 i k *
        ((if i = k then 1 else 0 : ℝ) : ℂ)) = projector24 i i
      calc
        _ = projector24 i i * ((if i = i then 1 else 0 : ℝ) : ℂ) := by
          apply Finset.sum_eq_single i
          · intro k _ hki
            simp [Ne.symm hki]
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))
        _ = projector24 i i := by simp
    _ = 24 := projector24_trace

theorem projected_charge : (∫ x : Point, projectedDensity x) = 48 := by
  have realIntegral : (∫ x : Point, (oneBodyKernel x x).re) =
      (∫ x : Point, oneBodyKernel x x).re := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re kernel_diagonal_integrable)
  unfold projectedDensity
  rw [integral_const_mul,realIntegral,kernel_diagonal_charge]
  norm_num

theorem density_residual_integrable : Integrable densityResidual :=
  sourceDensity_integrable.sub projected_density_integrable

theorem original_D3_charge_residual :
    |∫ x : Point, densityResidual x| ≤ (1 / 10^9 : ℝ) := by
  rw [show (∫ x : Point, densityResidual x) =
      (∫ x : Point, sourceDensity x) - (∫ x : Point, projectedDensity x) from
        integral_sub sourceDensity_integrable projected_density_integrable]
  rw [projected_charge]
  exact OriginalMetric.Charge.actual_whole_space_charge

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
