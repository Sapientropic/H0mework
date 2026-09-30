import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataAssembledRows
import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataAssembledDensity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix

open SourceIntegerGrid SourceRectangle SourceFiniteData SourceSignedEvaluator

theorem first_exact (left : Jet) (right : Basis) :
    firstAt left right = dotList (aoRow left) (densityColumn right) := by
  fin_cases left
  closeIntegerRows first_row at right

theorem bilinear_exact (left right : Jet) :
    bilinearAt left right = dotList (firstRow left) (aoRow right) := by
  fin_cases left
  closeIntegerRows bilinear_row at right

theorem ao_grid (left : Jet) (right : Basis) :
    grid (aoAt left right) = SourceRectangleChecks.calculatedAO left right := by
  fin_cases left
  closeIntegerRows ao_grid_row at right

theorem density_grid (row column : Basis) :
    grid (densityAt row column) = point (densityMatrix row column) := by
  fin_cases column
  closeIntegerRows density_grid_column at row

theorem first_grid (left : Jet) (right : Basis) :
    grid (firstAt left right) = SourceSignedMatrix.calculatedFirst left right := by
  fin_cases left
  closeIntegerRows first_grid_row at right

theorem bilinear_grid (left right : Jet) :
    grid (bilinearAt left right) = SourceSignedMatrix.calculatedBilinear left right := by
  fin_cases left
  closeIntegerRows bilinear_grid_row at right

theorem first_commutes (left : Jet) (right : Basis) :
    SourceSignedMatrix.calculatedFirst left right =
      firstMatrixPair (SourceRectangleChecks.calculatedAO left) densityMatrix right := by
  rw [← first_grid, first_exact]
  rw [dotList_commutes _ _ 98 (aoRow_length left) (densityColumn_length right)]
  change dotPair (fun i => grid (aoAt left i)) (fun i => grid (densityAt i right)) = _
  simp only [ao_grid, density_grid, firstMatrixPair]

theorem bilinear_dot_commutes (left right : Jet) :
    SourceSignedMatrix.calculatedBilinear left right =
      dotPair (SourceSignedMatrix.calculatedFirst left) (SourceRectangleChecks.calculatedAO right) := by
  rw [← bilinear_grid, bilinear_exact]
  rw [dotList_commutes _ _ 98 (firstRow_length left) (aoRow_length right)]
  change dotPair (fun i => grid (firstAt left i)) (fun i => grid (aoAt right i)) = _
  simp_rw [first_grid, ao_grid]

theorem bilinear_commutes (left right : Jet) :
    SourceSignedMatrix.calculatedBilinear left right =
      bilinearPair (SourceRectangleChecks.calculatedAO left)
        (SourceRectangleChecks.calculatedAO right) densityMatrix := by
  rw [bilinear_dot_commutes]
  have first : SourceSignedMatrix.calculatedFirst left =
      firstMatrixPair (SourceRectangleChecks.calculatedAO left) densityMatrix :=
    funext (first_commutes left)
  rw [first]
  rfl

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix
