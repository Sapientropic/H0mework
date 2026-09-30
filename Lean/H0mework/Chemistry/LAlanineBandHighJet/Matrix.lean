import H0mework.Chemistry.LAlanineBandMatrix.Soundness

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Matrix
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid SourceFieldMatrices
noncomputable section

structure Rows (n : Nat) where
  ao : Fin n → List Interval
  mids : Fin n → List ℤ
  radii : Fin n → List ℤ
  first : Fin n → List Interval

def aoAt {n : Nat} (rows : Rows n) (j : Fin n) (b : Basis) : Interval := (rows.ao j)[b.val]!
def firstAt {n : Nat} (rows : Rows n) (j : Fin n) (b : Basis) : Interval := (rows.first j)[b.val]!
def bilinearAt {n : Nat} (rows : Rows n) (j k : Fin n) : Interval := dotList (rows.first j) (rows.ao k)

structure Certificate {n : Nat} (rows : Rows n) (AO : Fin n → Basis → Pair) : Prop where
  ao_length : ∀ j, (rows.ao j).length = 98
  first_length : ∀ j, (rows.first j).length = 98
  ao_grid : ∀ j b, grid (aoAt rows j b) = AO j b
  mid_exact : ∀ j, rows.mids j = (rows.ao j).map mid
  rad_exact : ∀ j, rows.radii j = (rows.ao j).map rad
  first_exact : ∀ j b, firstAt rows j b = pointDot (rows.mids j) (rows.radii j) (PointColumns.column b)

 theorem first_commutes {n : Nat} (rows : Rows n) (AO : Fin n → Basis → Pair)
    (certificate : Certificate rows AO) (j : Fin n) (b : Basis) :
    grid (firstAt rows j b) = firstMatrixPair (AO j) densityMatrix b := by
  rw [certificate.first_exact,certificate.mid_exact,certificate.rad_exact,
    pointDot_commutes,PointColumns.column_commutes,
    dotList_commutes _ _ 98 (certificate.ao_length j) (SourceIntegerMatrix.densityColumn_length b)]
  change dotPair (fun i => grid (aoAt rows j i)) (fun i => grid (SourceIntegerMatrix.densityAt i b)) = _
  simp only [certificate.ao_grid,SourceIntegerMatrix.density_grid,firstMatrixPair]

 theorem bilinear_commutes {n : Nat} (rows : Rows n) (AO : Fin n → Basis → Pair)
    (certificate : Certificate rows AO) (j k : Fin n) :
    grid (bilinearAt rows j k) = bilinearPair (AO j) (AO k) densityMatrix := by
  rw [bilinearAt,dotList_commutes _ _ 98 (certificate.first_length j) (certificate.ao_length k)]
  change dotPair (fun b => grid (firstAt rows j b)) (fun b => grid (aoAt rows k b)) = _
  simp only [certificate.ao_grid,first_commutes rows AO certificate,bilinearPair]

 theorem bilinear_contains {n : Nat} (rows : Rows n) (AO : Fin n → Basis → Pair)
    (certificate : Certificate rows AO) (indices : Fin n → MultiIndex) (box : Rectangle)
    (contains : ∀ j b x, InRectangle box x → Holds (AO j b) (orbital (sourceTerms b) (indices j) x))
    (j k : Fin n) (x : Point) (inside : InRectangle box x) :
    Holds (grid (bilinearAt rows j k)) (bilinear sourceTerms densityMatrix (indices j) (indices k) x) := by
  rw [bilinear_commutes rows AO certificate]
  exact bilinearPair_contains (AO j) (AO k) densityMatrix sourceTerms (indices j) (indices k) x
    (fun b => contains j b x inside) (fun b => contains k b x inside)

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Matrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
