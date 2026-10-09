import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Cells
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
open SourceGaussianModel GlobalSource Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
noncomputable section

def cellEnergy (i : Fin 4 × Fin 4) : ℝ :=
  (1/2 : ℝ) * ∫ z in pairCell i, realPairIntegrand z

theorem cell_energy_nonnegative (i : Fin 4 × Fin 4) : 0 ≤ cellEnergy i :=
  mul_nonneg (by norm_num)
    (setIntegral_nonneg (pairCell_measurable i)
      (fun z _ => real_pair_integrand_nonnegative z))

theorem pair_cells_integral :
    (∑ i : Fin 4 × Fin 4, ∫ z in pairCell i, realPairIntegrand z) =
      ∫ z : Point × Point, realPairIntegrand z := by
  have h := integral_iUnion_fintype (s := pairCell)
    pairCell_measurable pairCells_disjoint
    (fun _ => real_pair_integrable.integrableOn)
  rw [pairCells_cover] at h
  simpa only [setIntegral_univ] using h.symm

theorem full_energy_sixteen_cells :
    (∑ i : Fin 4 × Fin 4, cellEnergy i) = pairCoulombEnergy.re := by
  have source : pairCoulombEnergy.re =
      (1/2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z := by
    rw [pairCoulombEnergy]
    simp_rw [pair_integrand_real]
    rw [integral_complex_ofReal]
    norm_num
  calc
    (∑ i : Fin 4 × Fin 4, cellEnergy i) =
        (1/2 : ℝ) * ∑ i : Fin 4 × Fin 4, ∫ z in pairCell i, realPairIntegrand z := by
          simp only [cellEnergy,Finset.mul_sum]
    _ = (1/2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z := by
          rw [pair_cells_integral]
    _ = pairCoulombEnergy.re := source.symm

theorem original_ao_energy_sixteen_cells :
    ((∑ i : Fin 4 × Fin 4, cellEnergy i : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
      ∑ a : SourceFiniteData.Basis, ∑ b : SourceFiniteData.Basis,
        ∑ c : SourceFiniteData.Basis, ∑ d : SourceFiniteData.Basis,
          spinSummedTwoBody a b c d *
            ((∑ i : SourceFiniteData.Basis, ∑ j : SourceFiniteData.Basis,
              ∑ k : SourceFiniteData.Basis, ∑ l : SourceFiniteData.Basis,
                (normalizedSourceFrame i a * normalizedSourceFrame j c *
                  normalizedSourceFrame k b * normalizedSourceFrame l d) *
                    electronRepulsion i j k l) : ℝ) := by
  have real : (pairCoulombEnergy.re : ℂ)=pairCoulombEnergy := by
    apply Complex.ext
    · simp
    · simp [pair_energy_real_nonnegative.1]
  calc
    _ = (pairCoulombEnergy.re : ℂ) := by rw [full_energy_sixteen_cells]
    _ = pairCoulombEnergy := real
    _ = _ := pair_coulomb_energy_original_ao


theorem cell_energy_symmetric (i j : Fin 4) :
    cellEnergy (i,j)=cellEnergy (j,i) := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (zone i) (zone j) realPairIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realPairIntegrand z.swap=realPairIntegrand z :=
    real_pair_integrand_swap z
  simp_rw [hpoint] at h
  simp only [cellEnergy,pairCell_prod]
  rw [h]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
