import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixCertificate
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixFieldReadout
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixSharedAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellMatrix

open Lean Elab Command

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

elab "assembleWholeCellMatrixRow " number:num : command => do
  let i := number.getNat
  unless i < 10 do throwError "registered low-jet row"
  emit s!"theorem first_row{i} (right : SourceFiniteData.Basis) : firstAt {i} right =
    SourceFieldMatrices.pointDot (aoMidRow {i}) (aoRadRow {i}) (SourceFieldMatrices.PointColumns.column right) := by
    fin_cases right
    closeRegisteredCells firstFast fixed {i} width 98"
  emit s!"theorem bilinear_row{i} (right : SourceFields.LowJet) : bilinearAt {i} right =
    SourceIntegerGrid.dotList (firstRow {i}) (aoRow right) := by
    fin_cases right
    closeRegisteredCells bilinear fixed {i} width 10"
  emit s!"theorem ao_grid_row{i} (right : SourceFiniteData.Basis) : SourceIntegerGrid.grid (aoAt {i} right) =
    sourceAO {i} right := by
    fin_cases right
    closeRegisteredCells ao fixed {i} width 98"

elab "assembleWholeCellMatrix " number:num : command => do
  let f := number.getNat
  unless 0 < f && f < 65 do throwError "registered whole-cell matrix source"
  emit "theorem first_fast_exact (j : LowJet) (b : Basis) :
    firstAt j b = SourceFieldMatrices.pointDot (aoMidRow j) (aoRadRow j) (SourceFieldMatrices.PointColumns.column b) := by
    fin_cases j
    closeRegisteredRows first_row at b"
  emit "theorem prepared_mid_exact (j : LowJet) : aoMidRow j = (aoRow j).map SourceIntegerGrid.mid := by
    fin_cases j
    closeRegisteredConstantRows mid_"
  emit "theorem prepared_rad_exact (j : LowJet) : aoRadRow j = (aoRow j).map SourceIntegerGrid.rad := by
    fin_cases j
    closeRegisteredConstantRows rad_"
  emit "theorem first_exact (j : LowJet) (b : Basis) :
    firstAt j b = dotList (aoRow j) (SourceIntegerMatrix.densityColumn b) := by
    rw [first_fast_exact, prepared_mid_exact, prepared_rad_exact,
      SourceFieldMatrices.pointDot_commutes, SourceFieldMatrices.PointColumns.column_commutes]"
  emit "theorem bilinear_exact (j k : LowJet) : bilinearAt j k = dotList (firstRow j) (aoRow k) := by
    fin_cases j
    closeRegisteredRows bilinear_row at k"
  emit "theorem ao_grid (j : LowJet) (b : Basis) : grid (aoAt j b) = sourceAO j b := by
    fin_cases j
    closeRegisteredRows ao_grid_row at b"
  emit "theorem first_commutes (j : LowJet) (b : Basis) :
    calculatedFirst j b = firstMatrixPair (sourceAO j) densityMatrix b := by
    rw [calculatedFirst, first_exact, dotList_commutes _ _ 98 (aoRow_length j) (SourceIntegerMatrix.densityColumn_length b)]
    change dotPair (fun i => grid (aoAt j i)) (fun i => grid (SourceIntegerMatrix.densityAt i b)) = _
    simp only [ao_grid, SourceIntegerMatrix.density_grid, firstMatrixPair]"
  emit "theorem bilinear_commutes (j k : LowJet) :
    calculatedBilinear j k = bilinearPair (sourceAO j) (sourceAO k) densityMatrix := by
    rw [calculatedBilinear, bilinear_exact, dotList_commutes _ _ 98 (firstRow_length j) (aoRow_length k)]
    change dotPair (fun i => grid (firstAt j i)) (fun i => grid (aoAt k i)) = _
    have first : calculatedFirst j = firstMatrixPair (sourceAO j) densityMatrix := funext (first_commutes j)
    change dotPair (calculatedFirst j) (fun i => grid (aoAt k i)) = _
    simp only [ao_grid, first, bilinearPair]"
  emit s!"theorem actual_bilinear_bounds (x : Point) (inside : InRectangle (WholeCellSource.box fieldIndex) x)
      (j k : LowJet) : Holds (calculatedBilinear j k)
        (bilinear sourceTerms densityMatrix (multiindex (fullJet j)) (multiindex (fullJet k)) x) := by
    rw [bilinear_commutes]
    exact bilinearPair_contains (sourceAO j) (sourceAO k) densityMatrix sourceTerms
      (multiindex (fullJet j)) (multiindex (fullJet k)) x
      (fun b => WholeCellCache.Field{f}.calculatedAO_contains j b x inside)
      (fun b => WholeCellCache.Field{f}.calculatedAO_contains k b x inside)"
  emit "noncomputable def sourceField : IntervalParameterMap.FieldBox := fieldFromBilinear calculatedBilinear"
  emit "theorem actual_source_field (x : Point) (inside : InRectangle (WholeCellSource.box fieldIndex) x) :
    IntervalParameterMap.FieldHolds sourceField x :=
    fieldFromBilinear_contains calculatedBilinear x (actual_bilinear_bounds x inside)"
  emit "theorem gradient_eq_report (axis : Fin 3) : sourceField.gradient axis =
    WholeCellSource.reportedDensity fieldIndex (SourceLowMatrixField.firstLow axis) := by
    fin_cases axis <;> decide +kernel"
  emit "theorem hessian_eq_report (axis direction : Fin 3) : sourceField.hessian axis direction =
    WholeCellSource.reportedDensity fieldIndex (SourceLowMatrixField.secondLow axis direction) := by
    fin_cases axis <;> fin_cases direction <;> decide +kernel"
  emit "theorem actual_field (x : Point) (inside : InRectangle (WholeCellSource.box fieldIndex) x) :
    IntervalParameterMap.FieldHolds (WholeCellReplay.recordedField fieldIndex) x := by
    constructor
    · intro axis
      change Holds (WholeCellSource.reportedDensity fieldIndex (WholeCellReplay.gradientIndex axis))
        (ContinuousGradient.sourceGradient x axis)
      rw [gradient_index_eq, ← gradient_eq_report]
      exact (actual_source_field x inside).1 axis
    · intro axis direction
      change Holds (WholeCellSource.reportedDensity fieldIndex (WholeCellReplay.hessianIndex axis direction))
        (ContinuousGradient.sourceHessian x axis direction)
      rw [hessian_index_eq, ← hessian_eq_report]
      exact (actual_source_field x inside).2 axis direction"

end LAlanine40K2025.BasinRefinement.WholeCellMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
