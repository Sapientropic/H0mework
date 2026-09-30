import H0mework.Chemistry.LAlanineRefinementSource.SharedIntegerTables
import H0mework.Chemistry.LAlanineRefinementSource.ContractionData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceSharedContractions

open SourceFiniteData SourceGaussianModel SourceJetIncidence SourceLaplaceSharedTables
open scoped BigOperators

noncomputable section

def rowBilinear (left right : MultiIndex) (i : Basis) : Nat :=
  ∑ j : Basis, matrix i j * orbital (sourceJetIndex left) i * orbital (sourceJetIndex right) j

def rowSecond (left right : MultiIndex) (axis : Fin 3) (i : Basis) : Nat :=
  rowBilinear (raise (raise left axis) axis) right i +
    2 * rowBilinear (raise left axis) (raise right axis) i + rowBilinear left (raise (raise right axis) axis) i

def rowFourth (innerAxis axis : Fin 3) (i : Basis) : Nat :=
  rowSecond (raise (raise (fun _ => 0) innerAxis) innerAxis) (fun _ => 0) axis i +
    2 * rowSecond (raise (fun _ => 0) innerAxis) (raise (fun _ => 0) innerAxis) axis i +
      rowSecond (fun _ => 0) (raise (raise (fun _ => 0) innerAxis) innerAxis) axis i

theorem fourth_commutes (a b : Fin 3) (i : Basis) :
    rowFourth a b i = SourceLaplaceIntegers.rowFourth a b i := by
  simp only [rowFourth, rowSecond, rowBilinear, matrix_commutes, orbital_commutes,
    SourceLaplaceIntegers.rowFourth, SourceLaplaceIntegers.rowSecond, SourceLaplaceIntegers.rowBilinear,
    SourceLaplaceIntegers.orbitalInt]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceSharedContractions
