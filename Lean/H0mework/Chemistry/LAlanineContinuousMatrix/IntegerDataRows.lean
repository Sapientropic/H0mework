import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix

open SourceIntegerGrid SourceRectangle SourceFiniteData

noncomputable section

def aoRow (jet : Jet) : List Interval :=
  ![ao0, ao1, ao2, ao3, ao4, ao5, ao6, ao7, ao8, ao9,
    ao10, ao11, ao12, ao13, ao14, ao15, ao16, ao17, ao18, ao19] jet

def densityColumn (basis : Basis) : List Interval :=
  ![density0, density1, density2, density3, density4, density5, density6, density7, density8, density9,
    density10, density11, density12, density13, density14, density15, density16, density17, density18, density19,
    density20, density21, density22, density23, density24, density25, density26, density27, density28, density29,
    density30, density31, density32, density33, density34, density35, density36, density37, density38, density39,
    density40, density41, density42, density43, density44, density45, density46, density47, density48, density49,
    density50, density51, density52, density53, density54, density55, density56, density57, density58, density59,
    density60, density61, density62, density63, density64, density65, density66, density67, density68, density69,
    density70, density71, density72, density73, density74, density75, density76, density77, density78, density79,
    density80, density81, density82, density83, density84, density85, density86, density87, density88, density89,
    density90, density91, density92, density93, density94, density95, density96, density97] basis

def firstRow (jet : Jet) : List Interval :=
  ![first0, first1, first2, first3, first4, first5, first6, first7, first8, first9,
    first10, first11, first12, first13, first14, first15, first16, first17, first18, first19] jet

def bilinearRow (jet : Jet) : List Interval :=
  ![bilinear0, bilinear1, bilinear2, bilinear3, bilinear4, bilinear5, bilinear6, bilinear7, bilinear8, bilinear9,
    bilinear10, bilinear11, bilinear12, bilinear13, bilinear14, bilinear15, bilinear16, bilinear17, bilinear18, bilinear19] jet

def aoAt (jet : Jet) (basis : Basis) : Interval := (aoRow jet)[basis.val]!
def densityAt (row column : Basis) : Interval := (densityColumn column)[row.val]!
def firstAt (jet : Jet) (basis : Basis) : Interval := (firstRow jet)[basis.val]!
def bilinearAt (left right : Jet) : Interval := (bilinearRow left)[right.val]!

theorem aoRow_length : ∀ jet : Jet, (aoRow jet).length = 98 := by decide +kernel
theorem densityColumn_length : ∀ basis : Basis, (densityColumn basis).length = 98 := by decide +kernel
theorem firstRow_length : ∀ jet : Jet, (firstRow jet).length = 98 := by decide +kernel
theorem bilinearRow_length : ∀ jet : Jet, (bilinearRow jet).length = 20 := by decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix
