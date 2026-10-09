import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Runtime.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable section

theorem first_defect_complex_norm_error :
    ‖complexMatrix firstDefect‖ ≤ (392 / 10^11 : ℝ) := by
  let ε : ℝ := 4 / 10^11
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num [ε])
  have each (i j : Basis) : ‖(complexMatrix firstDefect) i j‖ ≤ ε := by
    rw [complex_entry_norm]
    exact first_defect_entry_error i j
  calc
    (∑ i : Basis, ∑ j : Basis, ‖(complexMatrix firstDefect) i j‖^2) ≤
        ∑ _i : Basis, ∑ _j : Basis, ε^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (each i j) 2))
    _ = (392 / 10^11 : ℝ)^2 := by norm_num [ε,Fintype.card_fin]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
