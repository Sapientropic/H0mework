import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedReservoirFlow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem original_free_PC_flow (time : ℝ) :
    (Native.freePCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ) =
      hamiltonianFlow Powered.Producer.poweredTotalHamiltonian time :=
  original_controller_flow _ _ _ _ _ _

theorem actual_free_PC_error (time : ℝ) :
    ‖Quantum.conjugation installedPCFrame
      (Native.freePCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ)-
        hamiltonianFlow (sourcePCH E) time‖ ≤ |time| * (126/10^12 : ℝ) := by
  rw [original_free_PC_flow]
  exact actual_PC_flow_error time

theorem actual_native_PC_error :
    ‖Quantum.conjugation installedPCFrame
      (Native.freePCUnitary (Propagation.Producer.nativeClockStep : ℝ) : Matrix Load.Source.PairController Load.Source.PairController ℂ)-
        hamiltonianFlow (sourcePCH E) (Propagation.Producer.nativeClockStep : ℝ)‖ ≤ (55/10^15 : ℝ) := by
  have bound := actual_free_PC_error (Propagation.Producer.nativeClockStep : ℝ)
  apply bound.trans
  rw [Propagation.Producer.nativeClockStep_exact]
  norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
