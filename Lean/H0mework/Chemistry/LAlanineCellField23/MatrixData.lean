import H0mework.Chemistry.LAlanineWholeCell.MatrixReifier
import H0mework.Chemistry.LAlanineCellField23.CacheData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellMatrix.F23

open SourceIntegerGrid SourceFields SourceFiniteData

generateWholeCellMatrix 23

noncomputable section
def sourceAO : LowJet → Basis → SourceSignedEvaluator.Pair := WholeCellCache.Field23.calculatedAO
def aoRow (j : LowJet) : List Interval := ![ao0, ao1, ao2, ao3, ao4, ao5, ao6, ao7, ao8, ao9] j
def aoMidRow (j : LowJet) : List ℤ := ![aoMid0, aoMid1, aoMid2, aoMid3, aoMid4, aoMid5, aoMid6, aoMid7, aoMid8, aoMid9] j
def aoRadRow (j : LowJet) : List ℤ := ![aoRad0, aoRad1, aoRad2, aoRad3, aoRad4, aoRad5, aoRad6, aoRad7, aoRad8, aoRad9] j
def firstRow (j : LowJet) : List Interval := ![first0, first1, first2, first3, first4, first5, first6, first7, first8, first9] j
def bilinearRow (j k : LowJet) : Interval :=
  (![bilinear0, bilinear1, bilinear2, bilinear3, bilinear4, bilinear5, bilinear6, bilinear7, bilinear8, bilinear9] j)[k.val]!
def aoAt (j : LowJet) (b : Basis) : Interval := (aoRow j)[b.val]!
def firstAt (j : LowJet) (b : Basis) : Interval := (firstRow j)[b.val]!
def bilinearAt := bilinearRow
def calculatedFirst (j : LowJet) (b : Basis) : SourceSignedEvaluator.Pair := grid (firstAt j b)
def calculatedBilinear (j k : LowJet) : SourceSignedEvaluator.Pair := grid (bilinearAt j k)

theorem field_index_exact : fieldIndex = (23 : WholeCellSource.Field) := rfl
theorem aoRow_length : ∀ j : LowJet, (aoRow j).length = 98 := by decide +kernel
theorem firstRow_length : ∀ j : LowJet, (firstRow j).length = 98 := by decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellMatrix.F23
