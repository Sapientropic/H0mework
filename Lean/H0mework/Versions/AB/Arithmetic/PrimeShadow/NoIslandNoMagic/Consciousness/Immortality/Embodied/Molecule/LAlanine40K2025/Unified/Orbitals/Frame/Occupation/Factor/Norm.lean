import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Entry
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Gram.All
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Gamma.All
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsMatrixFrobeniusOperatorBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator BigOperators

private theorem complex_bound (r s : Int) :
    ‖(r : ℂ) + Complex.I * (s : ℂ)‖ ≤ ((|r| + |s| : Int) : ℝ) := by
  have h := norm_add_le (r : ℂ) (Complex.I * (s : ℂ))
  simpa [norm_mul,Complex.norm_I,Int.cast_add] using h

theorem gram_entry_norm (a b : OccupiedSlot) :
    ‖(gram - 1) a b‖ ≤ (gramEntryBound : ℝ) / (factorScale : ℝ)^2 := by
  have source := Gram.all_entry_bound a b
  have cast : (((|gramRealError a b| + |gramImagError a b| : Int) : ℝ) ≤
      (gramEntryBound : ℝ)) := by exact_mod_cast source
  have upper := (complex_bound (gramRealError a b) (gramImagError a b)).trans cast
  rw [gram_entry,norm_div]
  have denom : ‖(factorScale : ℂ)^2‖ = (factorScale : ℝ)^2 := by norm_num [factorScale]
  rw [denom]
  exact div_le_div_of_nonneg_right upper (by norm_num [factorScale])

theorem gamma_entry_norm (i j : Basis) :
    ‖(rawGamma - candidateGamma) i j‖ ≤
      (gammaEntryBound : ℝ) / ((gammaScale : ℝ) * (factorScale : ℝ)^2) := by
  have source := Gamma.all_entry_bound i j
  have cast : (((|gammaRealError i j| + |gammaImagError i j| : Int) : ℝ) ≤
      (gammaEntryBound : ℝ)) := by exact_mod_cast source
  have upper := (complex_bound (gammaRealError i j) (gammaImagError i j)).trans cast
  rw [gamma_entry,norm_div]
  have denom : ‖(gammaScale : ℂ) * (factorScale : ℂ)^2‖ =
      (gammaScale : ℝ) * (factorScale : ℝ)^2 := by norm_num [gammaScale,factorScale]
  rw [denom]
  exact div_le_div_of_nonneg_right upper (by norm_num [gammaScale,factorScale])

theorem gram_norm_bound :
    ‖gram - 1‖ ≤ 24 * ((gramEntryBound : ℝ) / (factorScale : ℝ)^2) := by
  let error : ℝ := (gramEntryBound : ℝ) / (factorScale : ℝ)^2
  have nonnegative : 0 ≤ 24 * error := by norm_num [error,gramEntryBound,factorScale]
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ nonnegative
  have each (a b : OccupiedSlot) : ‖(gram - 1) a b‖ ≤ error := gram_entry_norm a b
  calc
    _ ≤ ∑ _a : OccupiedSlot, ∑ _b : OccupiedSlot, error^2 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        pow_le_pow_left₀ (norm_nonneg _) (each a b) 2))
    _ = (24 * error)^2 := by norm_num [Fintype.card_fin]; ring

theorem gamma_norm_bound :
    ‖rawGamma - candidateGamma‖ ≤
      98 * ((gammaEntryBound : ℝ) / ((gammaScale : ℝ) * (factorScale : ℝ)^2)) := by
  let error : ℝ := (gammaEntryBound : ℝ) / ((gammaScale : ℝ) * (factorScale : ℝ)^2)
  have nonnegative : 0 ≤ 98 * error := by norm_num [error,gammaEntryBound,gammaScale,factorScale]
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ nonnegative
  have each (i j : Basis) : ‖(rawGamma - candidateGamma) i j‖ ≤ error := gamma_entry_norm i j
  calc
    _ ≤ ∑ _i : Basis, ∑ _j : Basis, error^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (each i j) 2))
    _ = (98 * error)^2 := by norm_num [Fintype.card_fin]; ring

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
