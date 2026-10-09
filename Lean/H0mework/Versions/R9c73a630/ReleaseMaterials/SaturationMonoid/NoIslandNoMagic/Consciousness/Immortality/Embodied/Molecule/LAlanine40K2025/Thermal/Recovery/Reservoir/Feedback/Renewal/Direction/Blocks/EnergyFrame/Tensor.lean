import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.PairConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def spectatorFrame (U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ),Matrix.kronecker_mem_unitary U.property (one_mem _)⟩

theorem spectator_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Quantum.conjugation (spectatorFrame (κ := κ) U) (Matrix.kronecker A B) =
      Matrix.kronecker (Quantum.conjugation U A) B := by
  rw [Quantum.conjugation_apply]
  change Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ)*Matrix.kronecker A B*
    star (Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ)) = _
  simp only [Matrix.star_eq_conjTranspose,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]
  rfl

theorem one_tensor_commutes (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Commute (Matrix.kronecker A (1 : Matrix κ κ ℂ)) (Matrix.kronecker (1 : Matrix ι ι ℂ) B) := by
  show _*_ = _*_
  simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
