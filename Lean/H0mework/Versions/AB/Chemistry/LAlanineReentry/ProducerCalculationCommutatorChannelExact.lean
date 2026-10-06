import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerCalculationCommutatorReal
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerCalculationCommutatorImag
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNormData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
noncomputable section

private theorem realEntry_shared (i j : Basis) : commutatorRealNumerator i j =
    ∑ k : Basis, (NormCalculation.hamiltonianNumerator i k * NormCalculation.currentRealNumerator k j -
      NormCalculation.currentRealNumerator i k * NormCalculation.hamiltonianNumerator k j) :=
  congrArg₂ (fun H G : Matrix Basis Basis Int => ∑ k : Basis, (H i k * G k j - G i k * H k j))
    NormCalculation.hamiltonianNumerator_eq NormCalculation.currentRealNumerator_eq

private theorem imagEntry_shared (i j : Basis) : commutatorImagNumerator i j =
    ∑ k : Basis, (NormCalculation.hamiltonianNumerator i k * NormCalculation.currentImagNumerator k j -
      NormCalculation.currentImagNumerator i k * NormCalculation.hamiltonianNumerator k j) :=
  congrArg₂ (fun H G : Matrix Basis Basis Int => ∑ k : Basis, (H i k * G k j - G i k * H k j))
    NormCalculation.hamiltonianNumerator_eq NormCalculation.currentImagNumerator_eq

theorem commutatorRealMagnitude_exact : commutatorRealMagnitude = 861484667138722952736 := by
  have bridge : commutatorRealMagnitude = ∑ i : Basis, ∑ j : Basis,
      (∑ k : Basis,
        (NormCalculation.hamiltonianNumerator i k * NormCalculation.currentRealNumerator k j -
          NormCalculation.currentRealNumerator i k * NormCalculation.hamiltonianNumerator k j)).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg Int.natAbs (realEntry_shared i j)
  exact bridge.trans ((Finset.sum_congr rfl
    (fun i _ => NormCalculation.Commutator.sourceRealRow_eq_calculated i)).trans
      NormCalculation.Commutator.Real.total_exact)

theorem commutatorImagMagnitude_exact : commutatorImagMagnitude = 548077524358330748 := by
  have bridge : commutatorImagMagnitude = ∑ i : Basis, ∑ j : Basis,
      (∑ k : Basis,
        (NormCalculation.hamiltonianNumerator i k * NormCalculation.currentImagNumerator k j -
          NormCalculation.currentImagNumerator i k * NormCalculation.hamiltonianNumerator k j)).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg Int.natAbs (imagEntry_shared i j)
  exact bridge.trans ((Finset.sum_congr rfl
    (fun i _ => NormCalculation.Commutator.sourceImagRow_eq_calculated i)).trans
      NormCalculation.Commutator.Imag.total_exact)

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
