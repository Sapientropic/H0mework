import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationNormCalculationSharing
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.NormCalculation.Commutator

open Propagation.Interface

def dot (left right : List Int) : Int := (left.zipWith (· * ·) right).sum
def rowCalculation (leftH leftG : List Int) (columnsH columnsG : List (List Int)) : Nat :=
  (columnsH.zipWith (fun h g => (dot leftH g - dot leftG h).natAbs) columnsG).sum

theorem zipWith_ofFn {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    (List.ofFn a).zipWith f (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem dot_ofFn (a b : Basis → Int) : dot (List.ofFn a) (List.ofFn b) = ∑ i, a i * b i := by
  rw [dot, zipWith_ofFn, Fin.sum_ofFn]

def sourceRows (matrix : Matrix Basis Basis Int) (i : Basis) : List Int := List.ofFn (matrix i)
def sourceColumns (matrix : Matrix Basis Basis Int) (j : Basis) : List Int := List.ofFn (fun i => matrix i j)

theorem rowCalculation_source (H G : Matrix Basis Basis Int) (i : Basis) :
    rowCalculation (sourceRows H i) (sourceRows G i)
      (List.ofFn (sourceColumns H)) (List.ofFn (sourceColumns G)) =
      ∑ j : Basis, (∑ k : Basis, (H i k * G k j - G i k * H k j)).natAbs := by
  rw [rowCalculation, zipWith_ofFn, Fin.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceRows, sourceColumns, dot_ofFn, Finset.sum_sub_distrib]

end LAlanine40K2025.JointNext.NormCalculation.Commutator
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
