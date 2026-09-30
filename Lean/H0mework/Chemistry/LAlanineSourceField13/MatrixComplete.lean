import H0mework.Chemistry.LAlanineSourceField13.MatrixAssembled
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixLowAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.F13

open SourceIntegerGrid SourceFields SourceFiniteData SourceSignedEvaluator SourceRectangle SourceGaussianModel

theorem first_fast_exact (j : LowJet) (b : Basis) :
    firstAt j b = pointDot (aoMidRow j) (aoRadRow j) (PointColumns.column b) := by
  fin_cases j
  closeRegisteredRows first_row at b

theorem prepared_mid_exact (j : LowJet) : aoMidRow j = (aoRow j).map mid := by
  fin_cases j
  closeRegisteredConstantRows mid_

theorem prepared_rad_exact (j : LowJet) : aoRadRow j = (aoRow j).map rad := by
  fin_cases j
  closeRegisteredConstantRows rad_

theorem first_exact (j : LowJet) (b : Basis) :
    firstAt j b = dotList (aoRow j) (SourceIntegerMatrix.densityColumn b) := by
  rw [first_fast_exact, prepared_mid_exact, prepared_rad_exact,
    pointDot_commutes, PointColumns.column_commutes]

theorem bilinear_exact (j k : LowJet) : bilinearAt j k = dotList (firstRow j) (aoRow k) := by
  fin_cases j
  closeRegisteredRows bilinear_row at k

theorem ao_grid (j : LowJet) (b : Basis) : grid (aoAt j b) = SourceFields.AllFields.calculatedAO fieldIndex j b := by
  fin_cases j
  closeRegisteredRows ao_grid_row at b

theorem first_commutes (j : LowJet) (b : Basis) :
    calculatedFirst j b = firstMatrixPair (SourceFields.AllFields.calculatedAO fieldIndex j) densityMatrix b := by
  rw [calculatedFirst, first_exact]
  rw [dotList_commutes _ _ 98 (aoRow_length j) (SourceIntegerMatrix.densityColumn_length b)]
  change dotPair (fun i => grid (aoAt j i)) (fun i => grid (SourceIntegerMatrix.densityAt i b)) = _
  simp only [ao_grid, SourceIntegerMatrix.density_grid, firstMatrixPair]

theorem bilinear_dot_commutes (j k : LowJet) :
    calculatedBilinear j k = dotPair (calculatedFirst j) (SourceFields.AllFields.calculatedAO fieldIndex k) := by
  rw [calculatedBilinear, bilinear_exact]
  rw [dotList_commutes _ _ 98 (firstRow_length j) (aoRow_length k)]
  change dotPair (fun i => grid (firstAt j i)) (fun i => grid (aoAt k i)) = _
  simp only [ao_grid]
  rfl

theorem bilinear_commutes (j k : LowJet) :
    calculatedBilinear j k = bilinearPair (SourceFields.AllFields.calculatedAO fieldIndex j)
      (SourceFields.AllFields.calculatedAO fieldIndex k) densityMatrix := by
  rw [bilinear_dot_commutes]
  have first : calculatedFirst j = firstMatrixPair (SourceFields.AllFields.calculatedAO fieldIndex j) densityMatrix :=
    funext (first_commutes j)
  rw [first]
  rfl

theorem actual_bilinear_bounds : SourceLowMatrixField.BilinearBounds fieldIndex calculatedBilinear := by
  intro j k x inside
  rw [bilinear_commutes]
  exact bilinearPair_contains (SourceFields.AllFields.calculatedAO fieldIndex j) (SourceFields.AllFields.calculatedAO fieldIndex k)
    densityMatrix sourceTerms (multiindex (fullJet j)) (multiindex (fullJet k)) x
    (fun b => SourceFields.AllFields.calculatedAO_contains fieldIndex j b x inside)
    (fun b => SourceFields.AllFields.calculatedAO_contains fieldIndex k b x inside)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.F13
