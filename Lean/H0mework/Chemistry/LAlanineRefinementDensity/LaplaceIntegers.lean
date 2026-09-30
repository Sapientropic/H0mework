import H0mework.Chemistry.LAlanineRefinementSource.JetIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers

open SourceGaussianModel SourceFiniteData SourceJetIncidence
open scoped BigOperators

noncomputable section

def orbitalInt (d : MultiIndex) (basis : Basis) : Nat :=
  orbitalIntegerBound (sourceJetIndex d) basis

def bilinearByIndex (left right : JetIndex) : Nat :=
  ∑ i : Basis, ∑ j : Basis, densityMatrixIntegerBound i j * orbitalIntegerBound left i * orbitalIntegerBound right j

def bilinearInt (left right : MultiIndex) : Nat :=
  bilinearByIndex (sourceJetIndex left) (sourceJetIndex right)

def rowBilinear (left right : MultiIndex) (i : Basis) : Nat :=
  ∑ j : Basis, densityMatrixIntegerBound i j * orbitalInt left i * orbitalInt right j

def rowSecond (left right : MultiIndex) (axis : Fin 3) (i : Basis) : Nat :=
  rowBilinear (raise (raise left axis) axis) right i +
    2 * rowBilinear (raise left axis) (raise right axis) i +
      rowBilinear left (raise (raise right axis) axis) i

def rowFourth (innerAxis axis : Fin 3) (i : Basis) : Nat :=
  rowSecond (raise (raise (fun _ => 0) innerAxis) innerAxis) (fun _ => 0) axis i +
    2 * rowSecond (raise (fun _ => 0) innerAxis) (raise (fun _ => 0) innerAxis) axis i +
      rowSecond (fun _ => 0) (raise (raise (fun _ => 0) innerAxis) innerAxis) axis i

def secondInt (left right : MultiIndex) (axis : Fin 3) : Nat :=
  bilinearInt (raise (raise left axis) axis) right +
    2 * bilinearInt (raise left axis) (raise right axis) +
      bilinearInt left (raise (raise right axis) axis)

def fourthInt (innerAxis axis : Fin 3) : Nat :=
  secondInt (raise (raise (fun _ => 0) innerAxis) innerAxis) (fun _ => 0) axis +
    2 * secondInt (raise (fun _ => 0) innerAxis) (raise (fun _ => 0) innerAxis) axis +
      secondInt (fun _ => 0) (raise (raise (fun _ => 0) innerAxis) innerAxis) axis

def fourthIndex (innerAxis axis : Fin 3) : JetIndex :=
  sourceJetIndex (raise (raise (raise (raise (fun _ => 0) innerAxis) innerAxis) axis) axis)

def densityInt (index : JetIndex) : Nat := (densityBound index).num.natAbs

theorem densityInt_cast (index : JetIndex) : (densityInt index : ℚ) = densityBound index := by
  fin_cases index <;> decide +kernel

private theorem tripleScale (m a b : Nat) :
    ((m : ℚ) / 10 ^ 12) * ((a : ℚ) / 10 ^ 9) * ((b : ℚ) / 10 ^ 9) =
      ((m * a * b : Nat) : ℚ) / 10 ^ 30 := by
  push_cast
  ring

theorem bilinear_cast (left right : MultiIndex) :
    bilinearEnvelope densityMatrixBound sourceOrbitalBound left right = (bilinearInt left right : ℚ) / 10 ^ 30 := by
  simp only [bilinearEnvelope, sourceOrbitalBound, orbitalBound_integer, densityMatrixBound_integer, tripleScale,
    bilinearInt, bilinearByIndex, Nat.cast_sum, Finset.sum_div]

theorem second_cast (left right : MultiIndex) (axis : Fin 3) :
    secondEnvelope densityMatrixBound sourceOrbitalBound left right axis = (secondInt left right axis : ℚ) / 10 ^ 30 := by
  simp only [secondEnvelope, bilinear_cast, secondInt, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem fourth_cast (innerAxis axis : Fin 3) :
    fourthEnvelope densityMatrixBound sourceOrbitalBound (fun _ => 0) (fun _ => 0) innerAxis axis =
      (fourthInt innerAxis axis : ℚ) / 10 ^ 30 := by
  simp only [fourthEnvelope, second_cast, fourthInt, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem fourth_eq_sum_rows (innerAxis axis : Fin 3) :
    fourthInt innerAxis axis = ∑ i : Basis, rowFourth innerAxis axis i := by
  simp only [fourthInt, secondInt, bilinearInt, bilinearByIndex, rowFourth, rowSecond,
    rowBilinear, orbitalInt, Finset.sum_add_distrib, Finset.mul_sum, mul_add]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers
