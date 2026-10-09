import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.FactorBridge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix BigOperators
noncomputable section

theorem recorded_first_entry (i j : Basis) :
    Correction.recordedFirst i j = (Frame.First.retainedProduct i j : ℝ) := by
  rw [Frame.First.retainedProduct_computed]
  simp only [Correction.recordedFirst,Matrix.mul_apply,Frame.realRecorded,
    Frame.realInverse,Frame.firstProduct,Rat.cast_sum,Rat.cast_mul]

theorem recorded_d3_expansion (i j : Basis) :
    Correction.recordedD3 i j =
      ∑ k : Basis, (Frame.First.retainedProduct k i : ℝ) *
        ∑ l : Basis, (densityMatrix k l : ℝ) *
          (Frame.First.retainedProduct l j : ℝ) := by
  unfold Correction.recordedD3
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Correction.d3AO,
    Matrix.of_apply,recorded_first_entry]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
