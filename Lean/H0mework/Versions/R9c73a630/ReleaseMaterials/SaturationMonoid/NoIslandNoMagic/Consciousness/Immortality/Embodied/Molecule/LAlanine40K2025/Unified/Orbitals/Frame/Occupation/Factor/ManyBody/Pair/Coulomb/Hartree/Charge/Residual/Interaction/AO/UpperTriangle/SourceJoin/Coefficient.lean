import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Symmetry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open BasinRefinement.SourceFiniteData
noncomputable section

def sourceCoefficientAt (address : Fin 4851) : ℚ :=
  if targetLeft address.val = targetRight address.val then
    densityMatrix (targetLeft address.val) (targetRight address.val)
  else
    densityMatrix (targetLeft address.val) (targetRight address.val) +
      densityMatrix (targetRight address.val) (targetLeft address.val)

def reportCoefficientAt (address : Fin 4851) : ℚ :=
  ((targetAORow address.val)[2]! : ℚ) *
    (((targetAORow address.val)[3]! : ℚ) / 10^12)

theorem source_coefficient_report_bound (address : Fin 4851) :
    |sourceCoefficientAt address - reportCoefficientAt address| <
      (1 : ℚ) / 10^12 := by
  rcases all_target_rows_certified address with
    ⟨_,_,_,_,_,_,multiplicity,rounding⟩
  by_cases diagonal : targetLeft address.val = targetRight address.val
  · simp only [sourceCoefficientAt,reportCoefficientAt,if_pos diagonal] at *
    rw [multiplicity]
    norm_num at *
    linarith
  · have symmetric := original_D3_AO_symmetric
      (targetLeft address.val) (targetRight address.val)
    simp only [sourceCoefficientAt,reportCoefficientAt,if_neg diagonal] at *
    rw [multiplicity]
    rw [← symmetric]
    norm_num only [Int.cast_ofNat]
    have algebra (d q : ℚ) : d + d - 2 * q = 2 * (d - q) := by ring
    rw [algebra,abs_mul,abs_of_pos (by norm_num : (0 : ℚ) < 2)]
    nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
