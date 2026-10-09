import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Spatial
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Integral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open SourceGaussianModel GlobalSource SourceCoulomb Set MeasureTheory Function
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped BigOperators
noncomputable section

/-- Direct (Hartree) channel energy carried by the 14×14 pair cell `ij`. -/
def directCell (ij : Option (Fin 13) × Option (Fin 13)) : ℝ :=
  ∫ z in pairCell ij, realHartreeIntegrand z

/-- Exchange channel energy carried by the 14×14 pair cell `ij`. -/
def exchangeCell (ij : Option (Fin 13) × Option (Fin 13)) : ℝ :=
  ∫ z in pairCell ij, realExchangeIntegrand z

theorem pair_integrand_direct_exchange (z : Point × Point) :
    realPairIntegrand z = 2 * realHartreeIntegrand z - 2 * realExchangeIntegrand z := by
  unfold realPairIntegrand realHartreeIntegrand realExchangeIntegrand realPairDensity
  ring

theorem cell_energy_direct_exchange (ij : Option (Fin 13) × Option (Fin 13)) :
    cellEnergy ij = directCell ij - exchangeCell ij := by
  show (1/2 : ℝ) * ∫ z in pairCell ij, realPairIntegrand z = _
  rw [setIntegral_congr_fun (all_pair_cells_measurable ij)
    (fun z _ => pair_integrand_direct_exchange z)]
  rw [integral_sub ((real_hartree_integrable.const_mul 2).integrableOn)
    ((real_exchange_integrable.const_mul 2).integrableOn)]
  rw [integral_const_mul,integral_const_mul]
  unfold directCell exchangeCell
  ring

theorem direct_cell_nonnegative (ij : Option (Fin 13) × Option (Fin 13)) :
    0 ≤ directCell ij :=
  setIntegral_nonneg (all_pair_cells_measurable ij)
    (fun z _ => hartree_integrand_nonnegative z)

theorem exchange_cell_nonnegative (ij : Option (Fin 13) × Option (Fin 13)) :
    0 ≤ exchangeCell ij :=
  setIntegral_nonneg (all_pair_cells_measurable ij)
    (fun z _ => exchange_integrand_nonnegative z)

theorem exchange_cell_bounded (ij : Option (Fin 13) × Option (Fin 13)) :
    2 * exchangeCell ij ≤ directCell ij := by
  unfold directCell exchangeCell
  rw [← integral_const_mul]
  exact setIntegral_mono_on ((real_exchange_integrable.const_mul 2).integrableOn)
    real_hartree_integrable.integrableOn (all_pair_cells_measurable ij)
    (fun z _ => exchange_integrand_bounded z)

theorem exchange_integrand_swap (z : Point × Point) :
    realExchangeIntegrand z.swap = realExchangeIntegrand z := by
  have innerNorm :
      ‖inner ℂ (occupiedVector z.1) (occupiedVector z.2)‖ =
        ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖ := by
    have hxy : inner ℂ (occupiedVector z.1) (occupiedVector z.2) =
        star (inner ℂ (occupiedVector z.2) (occupiedVector z.1)) :=
      (inner_conj_symm _ _).symm
    rw [hxy,norm_star]
  have kernelSymm : kernel (z.1-z.2)=kernel (z.2-z.1) := by
    have h : z.1-z.2=-(z.2-z.1) := by abel
    rw [h]
    simp only [kernel,distance,Pi.neg_apply,neg_sq]
  simp only [realExchangeIntegrand,Prod.swap]
  rw [innerNorm,kernelSymm]

theorem hartree_integrand_swap (z : Point × Point) :
    realHartreeIntegrand z.swap = realHartreeIntegrand z := by
  have kernelSymm : kernel (z.1-z.2)=kernel (z.2-z.1) := by
    have h : z.1-z.2=-(z.2-z.1) := by abel
    rw [h]
    simp only [kernel,distance,Pi.neg_apply,neg_sq]
  simp only [realHartreeIntegrand,Prod.swap,kernelSymm]
  ring

theorem direct_cell_symmetric (i j : Option (Fin 13)) :
    directCell (i,j) = directCell (j,i) := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (region i) (region j) realHartreeIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realHartreeIntegrand z.swap = realHartreeIntegrand z :=
    hartree_integrand_swap z
  simp_rw [hpoint] at h
  simp only [directCell]
  rw [show pairCell (i,j) = region i ×ˢ region j from Partition.Finite.pairCell_prod _ (i,j),
    show pairCell (j,i) = region j ×ˢ region i from Partition.Finite.pairCell_prod _ (j,i)]
  exact h.symm

theorem exchange_cell_symmetric (i j : Option (Fin 13)) :
    exchangeCell (i,j) = exchangeCell (j,i) := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (region i) (region j) realExchangeIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realExchangeIntegrand z.swap = realExchangeIntegrand z :=
    exchange_integrand_swap z
  simp_rw [hpoint] at h
  simp only [exchangeCell]
  rw [show pairCell (i,j) = region i ×ˢ region j from Partition.Finite.pairCell_prod _ (i,j),
    show pairCell (j,i) = region j ×ˢ region i from Partition.Finite.pairCell_prod _ (j,i)]
  exact h.symm

theorem direct_cells_integral :
    (∑ ij : Option (Fin 13) × Option (Fin 13), ∫ z in pairCell ij, realHartreeIntegrand z) =
      ∫ z : Point × Point, realHartreeIntegrand z := by
  have h := integral_iUnion_fintype (s := pairCell) all_pair_cells_measurable
    all_pair_cells_disjoint (fun _ => real_hartree_integrable.integrableOn)
  rw [all_pair_cells_cover] at h
  simpa only [setIntegral_univ] using h.symm

theorem exchange_cells_integral :
    (∑ ij : Option (Fin 13) × Option (Fin 13), ∫ z in pairCell ij, realExchangeIntegrand z) =
      ∫ z : Point × Point, realExchangeIntegrand z := by
  have h := integral_iUnion_fintype (s := pairCell) all_pair_cells_measurable
    all_pair_cells_disjoint (fun _ => real_exchange_integrable.integrableOn)
  rw [all_pair_cells_cover] at h
  simpa only [setIntegral_univ] using h.symm

theorem direct_cells_total :
    (∑ ij : Option (Fin 13) × Option (Fin 13), directCell ij) = directEnergy.re := by
  unfold directCell
  rw [direct_cells_integral, direct_energy_real_integral]
  rw [integral_complex_ofReal]
  simp

theorem exchange_cells_total :
    (∑ ij : Option (Fin 13) × Option (Fin 13), exchangeCell ij) = exchangeEnergy.re := by
  unfold exchangeCell
  rw [exchange_cells_integral, exchange_energy_real_integral]
  rw [integral_complex_ofReal]
  simp

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
