import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity
import Mathlib.Data.Set.Pairwise.Basic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.Finite
open SourceGaussianModel GlobalSource Set MeasureTheory Function
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
noncomputable section

variable {ι : Type*} (locate : Point → ι)

def region (i : ι) : Set Point := locate ⁻¹' {i}
def pairIndex (z : Point × Point) : ι × ι := (locate z.1,locate z.2)
def pairCell (i : ι × ι) : Set (Point × Point) := pairIndex locate ⁻¹' {i}
def cellEnergy (i : ι × ι) : ℝ :=
  (1/2 : ℝ) * ∫ z in pairCell locate i, realPairIntegrand z

theorem pairCell_prod (i : ι × ι) :
    pairCell locate i=region locate i.1 ×ˢ region locate i.2 := by
  rcases i with ⟨a,b⟩
  ext z
  simp [pairCell,pairIndex,region,Prod.mk.injEq]

theorem pairCells_disjoint : Pairwise (Disjoint on pairCell locate) :=
  pairwise_disjoint_fiber (pairIndex locate)

theorem pairCells_cover [Fintype ι] : (⋃ i : ι × ι, pairCell locate i)=Set.univ := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true,pairCell,Set.mem_preimage,Set.mem_singleton_iff]
  exact ⟨pairIndex locate z,rfl⟩

theorem pairCell_measurable
    (fibers : ∀ i, MeasurableSet (region locate i)) (i : ι × ι) :
    MeasurableSet (pairCell locate i) := by
  rw [pairCell_prod]
  exact (fibers i.1).prod (fibers i.2)

theorem cell_energy_nonnegative
    (fibers : ∀ i, MeasurableSet (region locate i)) (i : ι × ι) :
    0 ≤ cellEnergy locate i :=
  mul_nonneg (by norm_num)
    (setIntegral_nonneg (pairCell_measurable locate fibers i)
      (fun z _ => real_pair_integrand_nonnegative z))

theorem pair_cells_integral [Fintype ι]
    (fibers : ∀ i, MeasurableSet (region locate i)) :
    (∑ i : ι × ι, ∫ z in pairCell locate i, realPairIntegrand z) =
      ∫ z : Point × Point, realPairIntegrand z := by
  have h := integral_iUnion_fintype (s := pairCell locate)
    (pairCell_measurable locate fibers) (pairCells_disjoint locate)
    (fun _ => real_pair_integrable.integrableOn)
  rw [pairCells_cover] at h
  simpa only [setIntegral_univ] using h.symm

theorem full_energy [Fintype ι]
    (fibers : ∀ i, MeasurableSet (region locate i)) :
    (∑ i : ι × ι, cellEnergy locate i) = pairCoulombEnergy.re := by
  have source : pairCoulombEnergy.re =
      (1/2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z := by
    rw [pairCoulombEnergy]
    simp_rw [pair_integrand_real]
    rw [integral_complex_ofReal]
    norm_num
  calc
    (∑ i : ι × ι, cellEnergy locate i) =
        (1/2 : ℝ) * ∑ i : ι × ι, ∫ z in pairCell locate i, realPairIntegrand z := by
          simp only [cellEnergy,Finset.mul_sum]
    _ = (1/2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z := by
          rw [pair_cells_integral locate fibers]
    _ = pairCoulombEnergy.re := source.symm

theorem original_ao_energy [Fintype ι]
    (fibers : ∀ i, MeasurableSet (region locate i)) :
    ((∑ i : ι × ι, cellEnergy locate i : ℝ) : ℂ) =
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
    _ = (pairCoulombEnergy.re : ℂ) := by rw [full_energy locate fibers]
    _ = pairCoulombEnergy := real
    _ = _ := pair_coulomb_energy_original_ao

theorem cell_energy_symmetric (i j : ι) :
    cellEnergy locate (i,j)=cellEnergy locate (j,i) := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (region locate i) (region locate j) realPairIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realPairIntegrand z.swap=realPairIntegrand z :=
    real_pair_integrand_swap z
  simp_rw [hpoint] at h
  simp only [cellEnergy,pairCell_prod]
  rw [h]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
