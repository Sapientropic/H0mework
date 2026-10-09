import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Program
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def localReceivedWord (k : Sym2 Basis) : Matrix (BodyFiber k) (BodyFiber k) ℂ :=
  restrict pceOrbit k LoadExecution.receivedWord

def localBodyInput (k : Sym2 Basis) : Matrix (BodyFiber k) (BodyFiber k) ℂ :=
  restrict pceOrbit k InputProducts.bodyInput

def localBody (k : Sym2 Basis) : Matrix (BodyFiber k) (BodyFiber k) ℂ :=
  localReceivedWord k*localBodyInput k*star (localReceivedWord k)

private theorem restriction_forward {ι κ : Type*} [Fintype ι] [DecidableEq κ] {label : ι → κ}
    {A : Matrix ι ι ℂ} (kept : Preserves label A) (O : Matrix ι ι ℂ) (k : κ) :
    restrict label k (A*O*star A)=restrict label k A*restrict label k O*star (restrict label k A) := by
  rw [Matrix.star_eq_conjTranspose,restrict_mul_right (preserves_star kept),restrict_mul kept,restrict_star,Matrix.star_eq_conjTranspose]

theorem local_body_exact (k : Sym2 Basis) : restrict pceOrbit k InputProducts.body=localBody k :=
  restriction_forward received_preserves InputProducts.bodyInput k

def programEnergy (k : Sym2 Basis) : ℝ := Collision.energy (localReadout k) (localBody k)

theorem program_energy_exact : InputProducts.netGain=∑ k : Sym2 Basis, programEnergy k := by
  rw [InputProducts.netGain,energy_eq_sum_restrict net_preserves]
  apply Finset.sum_congr rfl
  intro k _
  rw [local_readout_exact,local_body_exact]
  rfl

theorem original_program_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      ∑ k : Sym2 Basis, programEnergy k| ≤ (109/10^7 : ℝ) := by
  rw [← program_energy_exact]
  exact InputProducts.original_computed_input_net_error

theorem exact_program_addresses : Fintype.card (Sym2 Basis)=4851 := source_orbit_count

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
