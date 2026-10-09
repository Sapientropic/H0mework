import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Gram

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedExponential (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (NormedSpace.exp (-H)).trace⁻¹ • NormedSpace.exp (-H)

theorem exponential_conjugation (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) :
    Quantum.conjugation U (NormedSpace.exp H)=NormedSpace.exp (Quantum.conjugation U H) := by
  let phi := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp phi phi.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous H

theorem normalized_exponential_conjugation (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) :
    Quantum.conjugation U (normalizedExponential H)=normalizedExponential (Quantum.conjugation U H) := by
  have expRead := exponential_conjugation U (-H)
  rw [map_neg] at expRead
  have traceRead := Preparation.unitary_conjugation_trace U (NormedSpace.exp (-H))
  change (Quantum.conjugation U (NormedSpace.exp (-H))).trace=_ at traceRead
  rw [expRead] at traceRead
  simp only [normalizedExponential,map_smul,expRead,traceRead]

theorem diagonal_exponential (e : ι → ℝ) :
    NormedSpace.exp (-(Matrix.diagonal (fun i => (e i : ℂ))))=
      Matrix.diagonal (fun i => (Real.exp (-e i) : ℂ)) := by
  rw [Matrix.diagonal_neg,Matrix.exp_diagonal]
  congr 1
  funext i
  simp [← Complex.exp_eq_exp_ℂ]

theorem diagonal_normalized_exponential [Nonempty ι] (e : ι → ℝ) :
    normalizedExponential (Matrix.diagonal (fun i => (e i : ℂ)))=
      Matrix.diagonal (fun i => ((Population.gibbsPMF e 1 i).toReal : ℂ)) := by
  rw [normalizedExponential,diagonal_exponential,Matrix.trace_diagonal,← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Population.gibbsPMF_toReal,Population.partitionFunction,neg_one_mul,
    Pi.smul_apply,smul_eq_mul,← Complex.ofReal_sum,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

theorem original_bath_exponential : Thermal.Source.bathCurrent=normalizedExponential Thermal.Source.energyHamiltonian := by
  exact (diagonal_normalized_exponential Preparation.sourceEnergies).symm

theorem calculated_bath_exponential : Quantum.conjugation originalToCalculated Thermal.Source.bathCurrent=
    normalizedExponential transformedOriginal := by
  rw [original_bath_exponential,normalized_exponential_conjugation,same_source_Hamiltonian]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
