import H0mework.Chemistry.LAlanineBandCalculation.Grid

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
open SourceIntegerGrid SourceSignedEvaluator SourceExponential SourceRectangleChecks

def lowerInteger (a b : Interval) : ℤ :=
  min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2))
def upperInteger (a b : Interval) : ℤ :=
  max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2))
def mulInteger (a b : Interval) : Interval :=
  (lowerInteger a b / denominator,-((-upperInteger a b)/denominator))

private theorem product_grid (a b : ℤ) :
    (a : ℚ)/scale * ((b : ℚ)/scale) = ((a*b : ℤ) : ℚ)/scale^2 := by
  push_cast
  ring

 theorem grid_lowerCorner (a b : Interval) :
    lowerCorner (grid a) (grid b) = (lowerInteger a b : ℚ)/scale^2 := by
  simp only [lowerCorner,grid,product_grid,lowerInteger,Int.cast_min]
  rw [min_div_div_right (sq_pos_of_pos scale_positive).le,
    min_div_div_right (sq_pos_of_pos scale_positive).le,
    min_div_div_right (sq_pos_of_pos scale_positive).le]

 theorem grid_upperCorner (a b : Interval) :
    upperCorner (grid a) (grid b) = (upperInteger a b : ℚ)/scale^2 := by
  simp only [upperCorner,grid,product_grid,upperInteger,Int.cast_max]
  rw [max_div_div_right (sq_pos_of_pos scale_positive).le,
    max_div_div_right (sq_pos_of_pos scale_positive).le,
    max_div_div_right (sq_pos_of_pos scale_positive).le]

 theorem grid_mul (a b : Interval) : grid (mulInteger a b) = mul (grid a) (grid b) := by
  rw [mul,grid_lowerCorner,grid_upperCorner,roundDown_square_grid,roundUp_square_grid]
  rfl

 def cachedIntegerTerm (weight exponential : Interval) (polynomial : Fin 3 → Interval) : Interval :=
   mulInteger (mulInteger (mulInteger (mulInteger weight exponential) (polynomial 0)) (polynomial 1))
     (polynomial 2)

 theorem grid_cachedIntegerTerm (weight exponential : Interval) (polynomial : Fin 3 → Interval)
    (q : ℚ) (weight_exact : grid weight = point q) :
    grid (cachedIntegerTerm weight exponential polynomial) =
      cachedTerm q (grid exponential) (fun a => grid (polynomial a)) := by
  simp only [cachedIntegerTerm,grid_mul,weight_exact,cachedTerm]

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
