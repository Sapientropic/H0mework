import H0mework.Chemistry.LAlanineWholeCell.MatrixFieldReadout
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixSharedPointColumns

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandMatrix

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid SourceFields
open SourceFieldMatrices WholeCellMatrix IntervalParameterMap
noncomputable section

structure Rows where
  aoRows : LowJet → List Interval
  aoMidRows : LowJet → List ℤ
  aoRadRows : LowJet → List ℤ
  firstRows : LowJet → List Interval
  bilinearRows : LowJet → List Interval

def aoAt (rows : Rows) (j : LowJet) (b : Basis) : Interval := (rows.aoRows j)[b.val]!
def firstAt (rows : Rows) (j : LowJet) (b : Basis) : Interval := (rows.firstRows j)[b.val]!
def bilinearAt (rows : Rows) (j k : LowJet) : Interval := (rows.bilinearRows j)[k.val]!
def calculatedFirst (rows : Rows) (j : LowJet) (b : Basis) : Pair := grid (firstAt rows j b)
def calculatedBilinear (rows : Rows) (j k : LowJet) : Pair := grid (bilinearAt rows j k)
def calculatedField (rows : Rows) : FieldBox := fieldFromBilinear (calculatedBilinear rows)

/-- Only finite calculation equations; analytic inclusion is supplied independently by the AO producer. -/
structure RowsCertificate (rows : Rows) (AO : LowJet → Basis → Pair) : Prop where
  ao_length : ∀ j, (rows.aoRows j).length = 98
  first_length : ∀ j, (rows.firstRows j).length = 98
  bilinear_length : ∀ j, (rows.bilinearRows j).length = 10
  ao_grid : ∀ j b, grid (aoAt rows j b) = AO j b
  mid_exact : ∀ j, rows.aoMidRows j = (rows.aoRows j).map mid
  rad_exact : ∀ j, rows.aoRadRows j = (rows.aoRows j).map rad
  first_exact : ∀ j b, firstAt rows j b =
    pointDot (rows.aoMidRows j) (rows.aoRadRows j) (PointColumns.column b)
  bilinear_exact : ∀ j k, bilinearAt rows j k = dotList (rows.firstRows j) (rows.aoRows k)

theorem first_commutes (rows : Rows) (AO : LowJet → Basis → Pair)
    (calculation : RowsCertificate rows AO) (j : LowJet) (b : Basis) :
    calculatedFirst rows j b = firstMatrixPair (AO j) densityMatrix b := by
  rw [calculatedFirst, calculation.first_exact, calculation.mid_exact, calculation.rad_exact,
    pointDot_commutes, PointColumns.column_commutes,
    dotList_commutes _ _ 98 (calculation.ao_length j) (SourceIntegerMatrix.densityColumn_length b)]
  change dotPair (fun i => grid (aoAt rows j i)) (fun i => grid (SourceIntegerMatrix.densityAt i b)) = _
  simp only [calculation.ao_grid, SourceIntegerMatrix.density_grid, firstMatrixPair]

theorem bilinear_commutes (rows : Rows) (AO : LowJet → Basis → Pair)
    (calculation : RowsCertificate rows AO) (j k : LowJet) :
    calculatedBilinear rows j k = bilinearPair (AO j) (AO k) densityMatrix := by
  rw [calculatedBilinear, calculation.bilinear_exact,
    dotList_commutes _ _ 98 (calculation.first_length j) (calculation.ao_length k)]
  change dotPair (fun i => grid (firstAt rows j i)) (fun i => grid (aoAt rows k i)) = _
  have first : calculatedFirst rows j = firstMatrixPair (AO j) densityMatrix :=
    funext (first_commutes rows AO calculation j)
  change dotPair (calculatedFirst rows j) (fun i => grid (aoAt rows k i)) = _
  simp only [calculation.ao_grid, first, bilinearPair]

def AOContains (box : Rectangle) (AO : LowJet → Basis → Pair) : Prop :=
  ∀ j b x, InRectangle box x →
    Holds (AO j b) (orbital (sourceTerms b) (SourceRectangle.multiindex (fullJet j)) x)

theorem bilinear_contains (box : Rectangle) (AO : LowJet → Basis → Pair) (rows : Rows)
    (calculation : RowsCertificate rows AO) (ao_contains : AOContains box AO)
    (x : Point) (inside : InRectangle box x) (j k : LowJet) :
    Holds (calculatedBilinear rows j k)
      (bilinear sourceTerms densityMatrix (SourceRectangle.multiindex (fullJet j))
        (SourceRectangle.multiindex (fullJet k)) x) := by
  rw [bilinear_commutes rows AO calculation]
  exact bilinearPair_contains (AO j) (AO k) densityMatrix sourceTerms _ _ x
    (fun b => ao_contains j b x inside) (fun b => ao_contains k b x inside)

theorem fieldHolds_of_rows (box : Rectangle) (AO : LowJet → Basis → Pair) (rows : Rows)
    (calculation : RowsCertificate rows AO) (ao_contains : AOContains box AO)
    (x : Point) (inside : InRectangle box x) : FieldHolds (calculatedField rows) x :=
  fieldFromBilinear_contains (calculatedBilinear rows) x
    (bilinear_contains box AO rows calculation ao_contains x inside)

/-- The source report is recognized only after the matrix calculation has generated its field. -/
theorem recorded_fieldHolds (box : Rectangle) (AO : LowJet → Basis → Pair) (rows : Rows)
    (calculation : RowsCertificate rows AO) (ao_contains : AOContains box AO) (reported : FieldBox)
    (gradient_eq : ∀ axis, (calculatedField rows).gradient axis = reported.gradient axis)
    (hessian_eq : ∀ axis direction, (calculatedField rows).hessian axis direction = reported.hessian axis direction)
    (x : Point) (inside : InRectangle box x) : FieldHolds reported x := by
  have generated := fieldHolds_of_rows box AO rows calculation ao_contains x inside
  constructor
  · intro axis
    rw [← gradient_eq]
    exact generated.1 axis
  · intro axis direction
    rw [← hessian_eq]
    exact generated.2 axis direction

end
end LAlanine40K2025.BasinRefinement.WholeBandMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
