import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Source
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Source
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory SourceCoulomb
open scoped BigOperators
noncomputable section

/-- Electron–nuclear attraction of nucleus `a` integrated over zone `z`. -/
def zoneAttraction (z : Option (Fin 13)) (a : Fin 13) : ℝ :=
  ∫ x in region z, -nuclearCharge a *
    (sourceDensity x * kernel (x - nuclearPosition a))

/-- Whole-space electron–nuclear attraction of nucleus `a`. -/
def nuclearAttraction (a : Fin 13) : ℝ :=
  ∫ x, -nuclearCharge a *
    (sourceDensity x * kernel (x - nuclearPosition a))

theorem zone_attraction_integrable (a : Fin 13) :
    Integrable (fun x : Point => -nuclearCharge a *
      (sourceDensity x * kernel (x - nuclearPosition a))) :=
  source_electron_nuclear_integrable (nuclearPosition a) (nuclearCharge a)

/-- The fourteen zones exhaust the original whole-space attraction of each
    recorded nucleus. -/
theorem zone_attraction_sum (a : Fin 13) :
    ∑ z : Option (Fin 13), zoneAttraction z a = nuclearAttraction a := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable
    OneBody.regions_disjoint
    (fun _ => (zone_attraction_integrable a).integrableOn)
  rw [OneBody.regions_cover] at h
  simpa only [setIntegral_univ,zoneAttraction,nuclearAttraction] using h.symm

/-- AO matrix element of the electron–nuclear attraction over all nuclei. -/
def aoAttraction (i j : Basis) : ℝ :=
  ∑ a : Fin 13, -nuclearCharge a *
    ∫ x : Point, ao i x * ao j x * kernel (x - nuclearPosition a)

private theorem ao_attraction_integrable (a : Fin 13) (i j : Basis) :
    Integrable (fun x : Point => ao i x * ao j x *
      kernel (x - nuclearPosition a)) :=
  integrable_mul_shifted_kernel _
    (source_product_integrable i j zeroJet zeroJet)
    ((GlobalSource.sourceOrbitalBound zeroJet i : ℝ) *
      GlobalSource.sourceOrbitalBound zeroJet j)
    (fun x => source_product_bound i j zeroJet zeroJet x)
    (nuclearPosition a)

/-- The thirteen-nucleus attraction contracts exactly to the original density
    matrix over the AO attraction tensor: source density times kernel, summed
    over all recorded nuclei. -/
theorem total_attraction_original_ao :
    ∑ a : Fin 13, nuclearAttraction a =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * aoAttraction i j := by
  have expand (a : Fin 13) : nuclearAttraction a =
      -nuclearCharge a * ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        ∫ x : Point, ao i x * ao j x * kernel (x - nuclearPosition a) := by
    have hsum : (∫ x : Point, sourceDensity x *
        kernel (x - nuclearPosition a)) =
        ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
          ∫ x : Point, ao i x * ao j x * kernel (x - nuclearPosition a) := by
      have step : (fun x : Point => sourceDensity x *
          kernel (x - nuclearPosition a)) =
          fun x : Point => ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
            (ao i x * ao j x * kernel (x - nuclearPosition a)) := by
        funext x
        simp only [sourceDensity,density,bilinear]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        change (densityMatrix i j : ℝ) * ao i x * ao j x *
            SourceCoulomb.kernel (x - nuclearPosition a) =
          (densityMatrix i j : ℝ) * (ao i x * ao j x *
            SourceCoulomb.kernel (x - nuclearPosition a))
        ring
      rw [step]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (ao_attraction_integrable a i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ =>
        (ao_attraction_integrable a i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_const_mul]
    simp only [nuclearAttraction]
    rw [integral_const_mul,hsum]
  calc ∑ a : Fin 13, nuclearAttraction a
      = ∑ a : Fin 13, -nuclearCharge a * ∑ i : Basis, ∑ j : Basis,
          (densityMatrix i j : ℝ) * ∫ x : Point, ao i x * ao j x *
            kernel (x - nuclearPosition a) :=
        Finset.sum_congr rfl fun a _ => expand a
    _ = ∑ a : Fin 13, ∑ i : Basis, ∑ j : Basis,
          (densityMatrix i j : ℝ) * (-nuclearCharge a *
            ∫ x : Point, ao i x * ao j x *
              kernel (x - nuclearPosition a)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i : Basis, ∑ j : Basis, ∑ a : Fin 13,
          (densityMatrix i j : ℝ) * (-nuclearCharge a *
            ∫ x : Point, ao i x * ao j x *
              kernel (x - nuclearPosition a)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
          aoAttraction i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [aoAttraction]
        rw [← Finset.mul_sum]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
