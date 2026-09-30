import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedElectronicFramePolar
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Observer

open Propagation.Interface
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

/-- The old-frame operator is compiled from an independent requested reader. -/
def pull (reader : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  star (Polar.matrix Source.crossMatrix) * reader * Polar.matrix Source.crossMatrix

theorem trace_commutes (held reader : Matrix Basis Basis ℂ) :
    (Source.heldStateTransport held * reader).trace = (held * pull reader).trace := by
  change ((Polar.matrix Source.crossMatrix * held * star (Polar.matrix Source.crossMatrix)) * reader).trace = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [pull, Matrix.mul_assoc]

theorem pull_hermitian (reader : Matrix Basis Basis ℂ) (hermitian : reader.IsHermitian) :
    (pull reader).IsHermitian := by
  have result := Matrix.isHermitian_mul_mul_conjTranspose
    (star (Polar.matrix Source.crossMatrix)) hermitian
  change (star (Polar.matrix Source.crossMatrix) * reader *
    star (star (Polar.matrix Source.crossMatrix))).IsHermitian at result
  simpa only [pull, star_star] using result

def currentHamiltonian : Matrix Basis Basis ℂ := activeMatrix Source.currentElectronicSource
def targetHamiltonian : Matrix Basis Basis ℂ := activeMatrix Source.targetElectronicSource

/-- An effective one-electron readout change, not a claim of total DFT energy or control work. -/
def operatorChange : Matrix Basis Basis ℂ := pull targetHamiltonian - currentHamiltonian

theorem actual_operator_change (held : Matrix Basis Basis ℂ) :
    (Source.heldStateTransport held * targetHamiltonian).trace -
      (held * currentHamiltonian).trace = (held * operatorChange).trace := by
  rw [trace_commutes]
  simp only [operatorChange, Matrix.mul_sub, Matrix.trace_sub]

theorem targetHamiltonian_hermitian : targetHamiltonian.IsHermitian :=
  Propagation.Dynamics.activeMatrix_hermitian Source.targetElectronicSource

theorem operatorChange_hermitian : operatorChange.IsHermitian :=
  (pull_hermitian targetHamiltonian targetHamiltonian_hermitian).sub
    (Propagation.Dynamics.activeMatrix_hermitian Source.currentElectronicSource)

end
end LAlanine40K2025.ElectronicFrame.Observer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
