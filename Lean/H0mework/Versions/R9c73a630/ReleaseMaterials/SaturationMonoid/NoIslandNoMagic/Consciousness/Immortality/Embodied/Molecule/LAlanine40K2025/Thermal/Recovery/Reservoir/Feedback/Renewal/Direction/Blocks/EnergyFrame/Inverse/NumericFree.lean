import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Effect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Producer Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def numericPCFree : Matrix.unitaryGroup PairController ℂ :=
  ⟨hamiltonianFlow (sourcePCH E) (nativeClockStep : ℝ),hamiltonianFlow_unitary _ numeric_PC_hermitian _⟩
def numericFree : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary numericPCFree (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))

theorem actual_free_matrix : (actualFree : LoadedJoint) =
    Matrix.kronecker (Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ))
      (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  change Quantum.conjugation installedLoadFrame (BodyKernel.bodyFree : LoadedJoint) = _
  unfold installedLoadFrame BodyKernel.bodyFree
  exact spectator_conjugation installedPCFrame _ _

theorem actual_numeric_free_error : ‖(actualFree : LoadedJoint)-(numericFree : LoadedJoint)‖ ≤ (55/10^15 : ℝ) := by
  rw [actual_free_matrix]
  have delta : Matrix.kronecker (Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ))
      (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ) : Matrix (Fin 2) (Fin 2) ℂ)-(numericFree : LoadedJoint) =
    Matrix.kronecker (Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ)-
      hamiltonianFlow (sourcePCH E) (nativeClockStep : ℝ))
      (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [numericFree,numericPCFree,Load.Quantum.localUnitary,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [delta]
  apply (kronecker_norm_le _ _).trans
  rw [CStarRing.norm_coe_unitary,mul_one]
  exact actual_native_PC_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
