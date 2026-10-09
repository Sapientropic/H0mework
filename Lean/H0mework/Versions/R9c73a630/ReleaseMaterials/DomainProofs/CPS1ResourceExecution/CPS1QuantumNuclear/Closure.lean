import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Good
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Provenance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

theorem current_fields (stock : Stock frame) (generated : GoodStock stock)
    (state : CPS1ElectronicSource.State frame) (member : Species.retained (.quantum state) ∈ stock) :
    Orthonormal ℂ (CPS1ElectronicEvolution.Consumer.occupiedFields state) ∧
      CPS1ElectronicEvolution.slaterDual (CPS1ElectronicEvolution.Consumer.occupiedFields state)
        (CPS1ElectronicEvolution.slater (CPS1ElectronicEvolution.Consumer.occupiedFields state)) = 1 ∧
      state.hamiltonian.IsHermitian :=
  ⟨CPS1ElectronicEvolution.Consumer.source_fields state (generated state member),
    CPS1ElectronicEvolution.Consumer.source_slater state (generated state member),
    CPS1ElectronicSource.source_hamiltonian_hermitian state⟩

end
end CPS1QuantumNuclear
