import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMatrix.Rowwise
import H0mework.Versions.AB.Chemistry.LAlanineBandCache.Kernel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

open SourceExponential SourceSignedEvaluator SourceIntegerGrid SourceRectangleChecks

def encode (a : Pair) : Interval := (⌊scale*a.1⌋,⌈scale*a.2⌉)
def addInteger (a b : Interval) : Interval := (a.1+b.1,a.2+b.2)

 theorem encode_grid (a : Interval) : encode (grid a) = a := by
  have cancel (n : ℤ) : scale * ((n : ℚ)/scale) = n := by
    field_simp [ne_of_gt scale_positive]
  simp only [encode,grid,cancel,Int.floor_intCast,Int.ceil_intCast]

 theorem grid_add (a b : Interval) : grid (addInteger a b) = add (grid a) (grid b) := by
  simp only [grid,addInteger,add,Int.cast_add,add_div]

 theorem grid_zero : grid (0,0) = point 0 := by
  simp [grid,point,roundDown,roundUp]

 theorem encode_rounds (l u : ℚ) :
    grid (encode (roundDown l,roundUp u)) = (roundDown l,roundUp u) :=
  congrArg grid (encode_grid (⌊scale*l⌋,⌈scale*u⌉))

 theorem encode_mul (a b : Pair) : grid (encode (mul a b)) = mul a b :=
  encode_rounds _ _

 theorem encode_cachedTerm (weight : ℚ) (exponential : Pair) (polynomial : Fin 3 → Pair) :
    grid (encode (cachedTerm weight exponential polynomial)) = cachedTerm weight exponential polynomial :=
  encode_mul _ _

 theorem grid_fold (values : List Interval) :
    grid (values.foldr addInteger (0,0)) = (values.map grid).foldr add (point 0) := by
  induction values with
  | nil => exact grid_zero
  | cons value rest ih => simp only [List.foldr_cons,List.map_cons,grid_add,ih]

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
