import H0mework.Chemistry.LAlanineReentry.ProducerCalculationNormCalculationSquares
import H0mework.Chemistry.LAlanineReentry.ProducerCoefficients

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
noncomputable section

def crossSquareSum : Int := ∑ i : Basis, ∑ j : Basis, crossDelta i j ^ 2
def symmetricCrossDelta (i j : Basis) : Int := crossDelta i j + crossDelta j i
def symmetricCrossSquareSum : Int := ∑ i : Basis, ∑ j : Basis, symmetricCrossDelta i j ^ 2
def targetRealDelta (i j : Basis) : Int := Source.targetRealNumerator i j - Source.currentRealNumerator i j
def targetImagDelta (i j : Basis) : Int := Source.targetImagNumerator i j - Source.currentImagNumerator i j
def targetDeltaSquareSum : Int := ∑ i : Basis, ∑ j : Basis,
  (targetRealDelta i j ^ 2 + targetImagDelta i j ^ 2)

set_option maxRecDepth 4096 in
theorem crossSquareSum_exact : crossSquareSum = 5353740603 := by
  have bridge : crossSquareSum = ∑ i : Basis, NormCalculation.Squares.crossRow i :=
    congrArg (fun C : Matrix Basis Basis Int => ∑ i : Basis, ∑ j : Basis,
      (C i j - if i = j then 1000000000000000 else 0) ^ 2) NormCalculation.crossNumerator_eq
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.crossRows_exact i)).trans
    (by decide +kernel))

set_option maxRecDepth 4096 in
theorem symmetricCrossSquareSum_exact : symmetricCrossSquareSum = 107908 := by
  have bridge : symmetricCrossSquareSum = ∑ i : Basis, NormCalculation.Squares.symmetricRow i :=
    congrArg (fun C : Matrix Basis Basis Int => ∑ i : Basis, ∑ j : Basis,
      ((C i j - if i = j then 1000000000000000 else 0) +
        (C j i - if j = i then 1000000000000000 else 0)) ^ 2) NormCalculation.crossNumerator_eq
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.symmetricRows_exact i)).trans
    (by decide +kernel))

set_option maxRecDepth 4096 in
theorem targetDeltaSquareSum_exact : targetDeltaSquareSum = 7239856514 := by
  let total (tr ti cr ci : Matrix Basis Basis Int) := ∑ i : Basis, ∑ j : Basis,
    ((tr i j - cr i j) ^ 2 + (ti i j - ci i j) ^ 2)
  have first := congrArg₂ (fun tr ti => total tr ti Source.currentRealNumerator Source.currentImagNumerator)
    NormCalculation.targetRealNumerator_eq NormCalculation.targetImagNumerator_eq
  have second := congrArg₂ (total NormCalculation.targetRealNumerator NormCalculation.targetImagNumerator)
    NormCalculation.currentRealNumerator_eq NormCalculation.currentImagNumerator_eq
  have bridge : targetDeltaSquareSum = ∑ i : Basis, NormCalculation.Squares.targetRow i := first.trans second
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.targetRows_exact i)).trans
    (by decide +kernel))

def commutatorRealNumerator (i j : Basis) : Int := ∑ k : Basis,
  (Source.hamiltonianNumerator i k * Source.currentRealNumerator k j -
    Source.currentRealNumerator i k * Source.hamiltonianNumerator k j)
def commutatorImagNumerator (i j : Basis) : Int := ∑ k : Basis,
  (Source.hamiltonianNumerator i k * Source.currentImagNumerator k j -
    Source.currentImagNumerator i k * Source.hamiltonianNumerator k j)
def commutatorRealMagnitude : Nat := ∑ i : Basis, ∑ j : Basis, (commutatorRealNumerator i j).natAbs
def commutatorImagMagnitude : Nat := ∑ i : Basis, ∑ j : Basis, (commutatorImagNumerator i j).natAbs
def commutatorMagnitude : Nat := commutatorRealMagnitude + commutatorImagMagnitude

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
