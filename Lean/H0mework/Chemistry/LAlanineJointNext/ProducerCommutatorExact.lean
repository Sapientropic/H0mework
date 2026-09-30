import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationCommutatorRowsCalculation
import H0mework.Chemistry.LAlanineJointNext.ProducerNormData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
noncomputable section

theorem commutatorMagnitude_exact : commutatorMagnitude = 861906379218130454 := by
  have bridge : commutatorMagnitude = ∑ i : Basis, ∑ j : Basis,
      (∑ k : Basis,
        (NormCalculation.hamiltonianNumerator i k * NormCalculation.gammaNumerator k j -
          NormCalculation.gammaNumerator i k * NormCalculation.hamiltonianNumerator k j)).natAbs :=
    congrArg₂ (fun H G : Matrix Basis Basis Int =>
      ∑ i : Basis, ∑ j : Basis, (∑ k : Basis, (H i k * G k j - G i k * H k j)).natAbs)
      NormCalculation.hamiltonianNumerator_eq NormCalculation.gammaNumerator_eq
  exact bridge.trans ((Finset.sum_congr rfl
    (fun i _ => NormCalculation.Commutator.sourceRow_eq_calculated i)).trans NormCalculation.Commutator.total_exact)

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
