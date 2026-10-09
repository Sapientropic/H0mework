import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseTargetGeometry
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Integral

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource MeasureTheory SourceCoulomb
noncomputable section

def nuclearAttraction (a : Fin 13) : ℝ :=
  ∫ x, -nuclearCharge a *
    (sourceDensity x * kernel (x - centre a))

theorem zone_attraction_integrable (a : Fin 13) :
    Integrable (fun x : Point => -nuclearCharge a *
      (sourceDensity x * kernel (x - centre a))) :=
  source_electron_nuclear_integrable (centre a) (nuclearCharge a)

private theorem ao_integrable (a : Fin 13) (i j : Basis) :
    Integrable (fun x : Point => ao i x * ao j x *
      kernel (x - centre a)) :=
  integrable_mul_shifted_kernel _
    (source_product_integrable i j zeroJet zeroJet)
    ((GlobalSource.sourceOrbitalBound zeroJet i : ℝ) *
      GlobalSource.sourceOrbitalBound zeroJet j)
    (fun x => source_product_bound i j zeroJet zeroJet x)
    (centre a)

theorem nuclear_total_original_ao :
    ∑ a : Fin 13, nuclearAttraction a =
      UnifiedOrbitals.Attraction.Precise.totalIntegral := by
  have expand (a : Fin 13) : nuclearAttraction a =
      -nuclearCharge a * ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        ∫ x : Point, ao i x * ao j x * kernel (x - centre a) := by
    have hsum : (∫ x : Point, sourceDensity x *
        kernel (x - centre a)) =
        ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
          ∫ x : Point, ao i x * ao j x * kernel (x - centre a) := by
      have step : (fun x : Point => sourceDensity x *
          kernel (x - centre a)) =
          fun x : Point => ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
            (ao i x * ao j x * kernel (x - centre a)) := by
        funext x
        simp only [sourceDensity,density,bilinear]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        change (densityMatrix i j : ℝ) * ao i x * ao j x *
            SourceCoulomb.kernel (x - centre a) =
          (densityMatrix i j : ℝ) * (ao i x * ao j x *
            SourceCoulomb.kernel (x - centre a))
        ring
      rw [step]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (ao_integrable a i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ =>
        (ao_integrable a i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_const_mul]
    simp only [nuclearAttraction]
    rw [integral_const_mul,hsum]
  calc
    ∑ a : Fin 13, nuclearAttraction a =
      ∑ a : Fin 13, -nuclearCharge a * ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * ∫ x : Point, ao i x * ao j x *
          kernel (x - centre a) :=
      Finset.sum_congr rfl fun a _ => expand a
    _ = ∑ a : Fin 13, ∑ i : Basis, ∑ j : Basis,
      (densityMatrix i j : ℝ) * (-nuclearCharge a *
        ∫ x : Point, ao i x * ao j x * kernel (x - centre a)) := by
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
        ∫ x : Point, ao i x * ao j x * kernel (x - centre a)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = UnifiedOrbitals.Attraction.Precise.totalIntegral := by
      rw [UnifiedOrbitals.Attraction.Precise.totalIntegral]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
