import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Gibbs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.StateNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Inputs

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def referenceEnergies (a : Basis) : ℝ := (SquareRoot.Full.energy a : ℝ)
def referencePartition : ℝ := ∑ a : Basis,Real.exp (-referenceEnergies a)

theorem reference_diagonal : E=Matrix.diagonal (fun a => (referenceEnergies a : ℂ)) := by
  ext i j
  simp only [E,referenceEnergies,SquareRoot.Full.energy,Matrix.diagonal_apply]
  split_ifs
  · norm_cast
  · rfl

theorem reference_first_energy : referenceEnergies 0 ≤ -18 := by
  have source : SquareRoot.Full.energy 0 ≤ (-18 : ℚ) := by decide +kernel
  change (SquareRoot.Full.energy 0 : ℝ) ≤ -18
  exact_mod_cast source

theorem exp_eighteen_lower : (60000000 : ℝ) ≤ Real.exp 18 := by
  have paid := Real.sum_le_exp_of_nonneg (x := (18 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ,Nat.factorial] at paid
  linarith

theorem reference_partition_lower : (60000000 : ℝ) ≤ referencePartition := by
  have first : Real.exp 18 ≤ Real.exp (-referenceEnergies 0) :=
    Real.exp_le_exp.mpr (by linarith [reference_first_energy])
  have included : Real.exp (-referenceEnergies 0) ≤ ∑ a : Basis,Real.exp (-referenceEnergies a) :=
    Finset.single_le_sum (fun a _ => (Real.exp_pos (-referenceEnergies a)).le) (Finset.mem_univ (0 : Basis))
  exact exp_eighteen_lower.trans (first.trans included)

theorem reference_exponential_trace : (NormedSpace.exp (-E)).trace=(referencePartition : ℂ) := by
  rw [reference_diagonal,diagonal_exponential,Matrix.trace_diagonal,← Complex.ofReal_sum]
  rfl

theorem reference_gibbs_lawful : (normalizedExponential E).PosSemidef ∧ (normalizedExponential E).trace=1 := by
  rw [reference_diagonal,diagonal_normalized_exponential]
  constructor
  · exact Matrix.posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr ENNReal.toReal_nonneg)
  · rw [Matrix.trace_diagonal,← Complex.ofReal_sum,Population.pmf_sum_toReal]
    rfl

theorem reference_gibbs_norm : ‖normalizedExponential E‖ ≤ 1 :=
  state_norm_le_one _ reference_gibbs_lawful.1 reference_gibbs_lawful.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
