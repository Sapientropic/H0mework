import H0mework.Chemistry.LAlanineBandCalculation.Grid

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
open SourceSignedEvaluator SourceIntegerGrid

 theorem grid_mapped_fold {α : Type*} (terms : List α) (value : α → Pair)
    (exactValue : ∀ term, grid (encode (value term)) = value term) :
    grid ((terms.map (fun term => encode (value term))).foldr addInteger (0,0)) =
      (terms.map value).foldr add (point 0) := by
  induction terms with
  | nil => exact grid_zero
  | cons term rest ih =>
    simp only [List.map_cons,List.foldr_cons,grid_add,exactValue,ih]

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
