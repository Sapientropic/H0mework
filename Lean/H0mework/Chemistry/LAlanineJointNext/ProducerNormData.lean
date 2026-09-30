import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationNormCalculationSquares

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
noncomputable section

def crossSquareSum : Int := ∑ i : Basis, ∑ j : Basis, crossDelta i j ^ 2
def symmetricCrossDelta (i j : Basis) : Int := crossDelta i j + crossDelta j i
def symmetricCrossSquareSum : Int := ∑ i : Basis, ∑ j : Basis, symmetricCrossDelta i j ^ 2
def targetRealDelta (i j : Basis) : Int := Source.targetRealNumerator i j - 1000 * HeldForce.Source.gammaNumerator i j
def targetDeltaSquareSum : Int := ∑ i : Basis, ∑ j : Basis,
  (targetRealDelta i j ^ 2 + Source.targetImagNumerator i j ^ 2)

set_option maxRecDepth 4096 in
theorem crossSquareSum_exact : crossSquareSum = 1927622034 := by
  have bridge : crossSquareSum = ∑ i : Basis, NormCalculation.Squares.crossRow i :=
    congrArg (fun C : Matrix Basis Basis Int => ∑ i : Basis, ∑ j : Basis,
      (C i j - if i = j then 1000000000000000 else 0) ^ 2) NormCalculation.crossNumerator_eq
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.crossRows_exact i)).trans
    (by decide +kernel))

set_option maxRecDepth 4096 in
theorem symmetricCrossSquareSum_exact : symmetricCrossSquareSum = 328146 := by
  have bridge : symmetricCrossSquareSum = ∑ i : Basis, NormCalculation.Squares.symmetricRow i :=
    congrArg (fun C : Matrix Basis Basis Int => ∑ i : Basis, ∑ j : Basis,
      ((C i j - if i = j then 1000000000000000 else 0) +
        (C j i - if j = i then 1000000000000000 else 0)) ^ 2) NormCalculation.crossNumerator_eq
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.symmetricRows_exact i)).trans
    (by decide +kernel))

set_option maxRecDepth 4096 in
theorem targetDeltaSquareSum_exact : targetDeltaSquareSum = 2722610585 := by
  have bridge : targetDeltaSquareSum = ∑ i : Basis, NormCalculation.Squares.targetRow i := by
    unfold targetDeltaSquareSum targetRealDelta NormCalculation.Squares.targetRow
    rw [NormCalculation.targetRealNumerator_eq, NormCalculation.targetImagNumerator_eq,
      NormCalculation.gammaNumerator_eq]
  exact bridge.trans ((Finset.sum_congr rfl (fun i _ => NormCalculation.Squares.targetRows_exact i)).trans
    (by decide +kernel))

def commutatorNumerator (i j : Basis) : Int := ∑ k : Basis,
  (Source.hamiltonianNumerator i k * HeldForce.Source.gammaNumerator k j -
    HeldForce.Source.gammaNumerator i k * Source.hamiltonianNumerator k j)
def commutatorMagnitude : Nat := ∑ i : Basis, ∑ j : Basis, (commutatorNumerator i j).natAbs

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
