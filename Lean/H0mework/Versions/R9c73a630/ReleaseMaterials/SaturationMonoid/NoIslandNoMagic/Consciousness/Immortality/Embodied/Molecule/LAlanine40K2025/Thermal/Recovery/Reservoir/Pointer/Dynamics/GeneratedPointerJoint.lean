import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PurePointerPreparation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerBlockReadout
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance
import H0mework.Chemistry.LAlanineEntropy.PartialTraceCovariance

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Quantum
open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def instrumentJoint (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  conjugation (dilation E positive complement) (prepared rho)

theorem instrumentJoint_positive (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) (rhoPositive : rho.PosSemidef) :
    (instrumentJoint E positive complement rho).PosSemidef :=
  conjugation_posSemidef _ _ (prepared_positive rho rhoPositive)

theorem instrumentJoint_trace (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) :
    (instrumentJoint E positive complement rho).trace = rho.trace :=
  (conjugation_trace _ _).trans (prepared_trace rho)

theorem instrumentJoint_zero (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) :
    zeroRead (instrumentJoint E positive complement rho) = Collision.energy E rho :=
  pointer_zero_read E rho positive

theorem instrumentJoint_one (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) :
    oneRead (instrumentJoint E positive complement rho) = Collision.energy (1 - E) rho :=
  pointer_one_read E rho complement

theorem instrumentJoint_backreaction (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ) :
    bodyRead (instrumentJoint E positive complement rho) =
      effectRoot E * rho * effectRoot E + complementRoot E * rho * complementRoot E :=
  bodyRead_backreaction E rho

theorem instrumentJoint_binary (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ)
    (rhoPositive : rho.PosSemidef) (normalized : rho.trace = 1) :
    0 ≤ zeroRead (instrumentJoint E positive complement rho) ∧
    0 ≤ oneRead (instrumentJoint E positive complement rho) ∧
    zeroRead (instrumentJoint E positive complement rho) + oneRead (instrumentJoint E positive complement rho) = 1 :=
  ⟨zeroRead_nonnegative _ (instrumentJoint_positive E positive complement rho rhoPositive),
    oneRead_nonnegative _ (instrumentJoint_positive E positive complement rho rhoPositive),
    pointer_binary_sum E rho positive complement normalized⟩

theorem instrumentJoint_injective (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) :
    Function.Injective (instrumentJoint E positive complement) := by
  intro left right same
  have joint := (Unitary.conjStarAlgAut ℂ _ (dilation E positive complement)).injective same
  exact congrArg Matrix.toBlocks₁₁ joint

theorem instrumentJoint_entropy (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (rho : Matrix ι ι ℂ)
    (rhoPositive : rho.PosSemidef) (normalized : rho.trace = 1) :
    spectralEntropy (instrumentJoint E positive complement rho)
      (instrumentJoint_positive E positive complement rho rhoPositive)
      ((instrumentJoint_trace E positive complement rho).trans normalized) =
    spectralEntropy rho rhoPositive normalized := by
  have invariant := spectralEntropy_unitary_conjugation (prepared rho) (prepared_positive rho rhoPositive)
    ((prepared_trace rho).trans normalized) (dilation E positive complement)
  exact invariant.trans (prepared_entropy rho rhoPositive normalized)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
