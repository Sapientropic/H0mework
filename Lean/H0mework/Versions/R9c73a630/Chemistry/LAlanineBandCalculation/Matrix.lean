import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMatrix.Rowwise

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

open SourceFiniteData SourceFields SourceIntegerGrid SourceFieldMatrices WholeBandMatrix
noncomputable section

private theorem ofFn_at {n : Nat} (f : Fin n → Interval) (i : Fin n) :
    (List.ofFn f)[i.val]! = f i := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some]

/-- The original dense D3 acts once on each actual AO row; all calls share this constructor. -/
def matrixRows (ao : LowJet → Basis → Interval) : Rows :=
  let inputs := fun j => List.ofFn (ao j)
  let first := fun j => List.ofFn (fun b =>
    pointDot ((inputs j).map mid) ((inputs j).map rad) (PointColumns.column b))
  { aoRows := inputs
    aoMidRows := fun j => (inputs j).map mid
    aoRadRows := fun j => (inputs j).map rad
    firstRows := first
    bilinearRows := fun j => List.ofFn (fun k => dotList (first j) (inputs k)) }

 theorem matrix_certificate (ao : LowJet → Basis → Interval) :
    RowsCertificate (matrixRows ao) (fun j b => grid (ao j b)) := by
  constructor
  · intro j; simp only [matrixRows,List.length_ofFn]
  · intro j; simp only [matrixRows,List.length_ofFn]
  · intro j; simp only [matrixRows,List.length_ofFn]
  · intro j b; simp only [aoAt,matrixRows,ofFn_at]
  · intro j; rfl
  · intro j; rfl
  · intro j b; simp only [firstAt,matrixRows,ofFn_at]
  · intro j k; simp only [bilinearAt,matrixRows,ofFn_at]

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
