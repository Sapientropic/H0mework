import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixAssembled
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixLowAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open SourceIntegerGrid SourceFields SourceFiniteData SourceSignedEvaluator SourceRectangle SourceGaussianModel

theorem first_exact (j : LowJet) (b : Basis) :
    firstAt j b = dotList (aoRow j) (SourceIntegerMatrix.densityColumn b) := by
  fin_cases j
  closeField1Rows first_row at b

theorem bilinear_exact (j k : LowJet) : bilinearAt j k = dotList (firstRow j) (aoRow k) := by
  fin_cases j
  closeField1Rows bilinear_row at k

theorem ao_grid (j : LowJet) (b : Basis) : grid (aoAt j b) = SourceFields.Field1.calculatedAO j b := by
  fin_cases j
  closeField1Rows ao_grid_row at b

theorem first_commutes (j : LowJet) (b : Basis) :
    calculatedFirst j b = firstMatrixPair (SourceFields.Field1.calculatedAO j) densityMatrix b := by
  rw [calculatedFirst, first_exact]
  rw [dotList_commutes _ _ 98 (aoRow_length j) (SourceIntegerMatrix.densityColumn_length b)]
  change dotPair (fun i => grid (aoAt j i)) (fun i => grid (SourceIntegerMatrix.densityAt i b)) = _
  simp only [ao_grid, SourceIntegerMatrix.density_grid, firstMatrixPair]

theorem bilinear_dot_commutes (j k : LowJet) :
    calculatedBilinear j k = dotPair (calculatedFirst j) (SourceFields.Field1.calculatedAO k) := by
  rw [calculatedBilinear, bilinear_exact]
  rw [dotList_commutes _ _ 98 (firstRow_length j) (aoRow_length k)]
  change dotPair (fun i => grid (firstAt j i)) (fun i => grid (aoAt k i)) = _
  simp only [ao_grid]
  rfl

theorem bilinear_commutes (j k : LowJet) :
    calculatedBilinear j k = bilinearPair (SourceFields.Field1.calculatedAO j)
      (SourceFields.Field1.calculatedAO k) densityMatrix := by
  rw [bilinear_dot_commutes]
  have first : calculatedFirst j = firstMatrixPair (SourceFields.Field1.calculatedAO j) densityMatrix :=
    funext (first_commutes j)
  rw [first]
  rfl

theorem actual_bilinear_bounds : SourceLowMatrixField.BilinearBounds 1 calculatedBilinear := by
  intro j k x inside
  rw [bilinear_commutes]
  exact bilinearPair_contains (SourceFields.Field1.calculatedAO j) (SourceFields.Field1.calculatedAO k)
    densityMatrix sourceTerms (multiindex (fullJet j)) (multiindex (fullJet k)) x
    (fun b => SourceFields.Field1.calculatedAO_contains j b x inside)
    (fun b => SourceFields.Field1.calculatedAO_contains k b x inside)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
