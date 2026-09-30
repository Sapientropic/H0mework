import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedElectronicFrameNorm
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransport

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Source

open Propagation.Interface
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

def sourceUnitary : Matrix.unitaryGroup Basis ℂ := Polar.unitary crossMatrix crossMatrix_close
def sourceProjectionResidual : Matrix Basis Basis ℂ := Polar.projectionResidual crossMatrix
def heldStateTransport (held : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ := Polar.transport crossMatrix held

theorem sourceUnitary_factorization :
    (sourceUnitary : Matrix Basis Basis ℂ) * CFC.abs crossMatrix = crossMatrix :=
  Polar.factorization crossMatrix crossMatrix_close

theorem sourceProjectionResidual_reconstruction :
    (sourceUnitary : Matrix Basis Basis ℂ) + sourceProjectionResidual = crossMatrix :=
  Polar.residual_reconstruction crossMatrix

theorem sourceProjectionResidual_norm : ‖sourceProjectionResidual‖ = ‖CFC.abs crossMatrix - 1‖ :=
  Polar.residual_norm crossMatrix crossMatrix_close

theorem heldStateTransport_hermitian (held : Matrix Basis Basis ℂ) (hermitian : held.IsHermitian) :
    (heldStateTransport held).IsHermitian := Polar.transport_hermitian crossMatrix held hermitian

theorem heldStateTransport_positive (held : Matrix Basis Basis ℂ) (positive : held.PosSemidef) :
    (heldStateTransport held).PosSemidef := Polar.transport_positive crossMatrix held positive

theorem heldStateTransport_trace (held : Matrix Basis Basis ℂ) :
    (heldStateTransport held).trace = held.trace := Polar.transport_trace crossMatrix held crossMatrix_close

theorem heldStateTransport_charpoly (held : Matrix Basis Basis ℂ) :
    (heldStateTransport held).charpoly = held.charpoly := Polar.transport_charpoly crossMatrix held crossMatrix_close

theorem heldStateTransport_spectrum (held : Matrix Basis Basis ℂ) :
    spectrum ℂ (heldStateTransport held) = spectrum ℂ held := Polar.transport_spectrum crossMatrix held crossMatrix_close

theorem heldStateTransport_entropy (held : Matrix Basis Basis ℂ)
    (positive : held.PosSemidef) (normalized : held.trace = 1) :
    Thermal.Quantum.spectralEntropy (heldStateTransport held) (heldStateTransport_positive held positive)
      ((heldStateTransport_trace held).trans normalized) = Thermal.Quantum.spectralEntropy held positive normalized :=
  Polar.transport_entropy crossMatrix held crossMatrix_close positive normalized

theorem heldStateTransport_faithful (held : Matrix Basis Basis ℂ) :
    star (sourceUnitary : Matrix Basis Basis ℂ) * heldStateTransport held * sourceUnitary = held :=
  Polar.transport_faithful crossMatrix held crossMatrix_close

theorem heldStateTransport_injective : Function.Injective heldStateTransport :=
  Polar.transport_injective crossMatrix crossMatrix_close

theorem crossMatrix_not_hermitian : ¬crossMatrix.IsHermitian := by
  intro hermitian
  have same := congrArg (fun matrix : Matrix Basis Basis ℂ => matrix 42 43) hermitian.eq
  change star ((crossNumerator 43 42 : ℂ) / 1000000000000000) =
    (crossNumerator 42 43 : ℂ) / 1000000000000000 at same
  have lower : crossNumerator 43 42 = -2306 := by decide
  have upper : crossNumerator 42 43 = 2305 := by decide
  rw [lower, upper] at same
  norm_num at same

theorem sourceUnitary_not_identity : (sourceUnitary : Matrix Basis Basis ℂ) ≠ 1 := by
  intro same
  have factor := sourceUnitary_factorization
  rw [same, one_mul] at factor
  apply crossMatrix_not_hermitian
  rw [← factor]
  exact (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg crossMatrix)).isHermitian

end
end LAlanine40K2025.ElectronicFrame.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
