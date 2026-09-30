import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsSourceGeneratedPolarFrame
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Polar

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open LAlanine40K2025.Thermal.Quantum
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The already held state is an input; no fresh SCF state is read by this writer. -/
def transport (C X : Matrix ι ι ℂ) : Matrix ι ι ℂ := matrix C * X * star (matrix C)

theorem transport_hermitian (C X : Matrix ι ι ℂ) (hermitian : X.IsHermitian) :
    (transport C X).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hermitian

theorem transport_positive (C X : Matrix ι ι ℂ) (positive : X.PosSemidef) :
    (transport C X).PosSemidef := positive.mul_mul_conjTranspose_same _

theorem transport_trace (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    (transport C X).trace = X.trace := unitary_conjugate_trace X (unitary C close)

theorem transport_charpoly (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    (transport C X).charpoly = X.charpoly := by
  rw [transport, Matrix.charpoly_mul_comm, ← mul_assoc, adjoint_mul C close, one_mul]

theorem transport_spectrum (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    spectrum ℂ (transport C X) = spectrum ℂ X :=
  Unitary.spectrum_star_right_conjugate (U := unitary C close)

theorem transport_entropy (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1)
    (positive : X.PosSemidef) (normalized : X.trace = 1) :
    spectralEntropy (transport C X) (transport_positive C X positive)
      ((transport_trace C X close).trans normalized) = spectralEntropy X positive normalized :=
  spectralEntropy_unitary_conjugation X positive normalized (unitary C close)

theorem transport_faithful (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    star (matrix C) * transport C X * matrix C = X := by
  simp only [transport, mul_assoc, ← mul_assoc (star (matrix C)) (matrix C),
    adjoint_mul C close, one_mul, mul_one]

theorem transport_injective (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    Function.Injective (transport C) := by
  intro X Y same
  have read := congrArg (fun Z => star (matrix C) * Z * matrix C) same
  simpa only [transport_faithful C X close, transport_faithful C Y close] using read

end
end LAlanine40K2025.ElectronicFrame.Polar
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
