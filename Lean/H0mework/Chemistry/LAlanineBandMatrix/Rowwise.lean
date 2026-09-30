import H0mework.Chemistry.LAlanineBandMatrix.Soundness

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandMatrix

open SourceFields SourceFiniteData SourceSignedEvaluator SourceIntegerGrid SourceFieldMatrices
noncomputable section

/-- A row packages the same finite equations, without a separate declaration for every matrix cell. -/
structure RowComputed (rows : Rows) (AO : LowJet → Basis → Pair) (j : LowJet) : Prop where
  ao_length : (rows.aoRows j).length = 98
  first_length : (rows.firstRows j).length = 98
  bilinear_length : (rows.bilinearRows j).length = 10
  ao_grid : List.ofFn (fun b => grid (aoAt rows j b)) = List.ofFn (AO j)
  mid_exact : rows.aoMidRows j = (rows.aoRows j).map mid
  rad_exact : rows.aoRadRows j = (rows.aoRows j).map rad
  first_exact : List.ofFn (firstAt rows j) = List.ofFn (fun b =>
    pointDot (rows.aoMidRows j) (rows.aoRadRows j) (PointColumns.column b))
  bilinear_exact : List.ofFn (bilinearAt rows j) =
    List.ofFn (fun k => dotList (rows.firstRows j) (rows.aoRows k))

theorem rowsCertificate_of_computed (rows : Rows) (AO : LowJet → Basis → Pair)
    (computed : ∀ j, RowComputed rows AO j) : RowsCertificate rows AO where
  ao_length j := (computed j).ao_length
  first_length j := (computed j).first_length
  bilinear_length j := (computed j).bilinear_length
  ao_grid j b := congrFun (List.ofFn_injective (computed j).ao_grid) b
  mid_exact j := (computed j).mid_exact
  rad_exact j := (computed j).rad_exact
  first_exact j b := congrFun (List.ofFn_injective (computed j).first_exact) b
  bilinear_exact j k := congrFun (List.ofFn_injective (computed j).bilinear_exact) k

theorem rowComputed_of_points (rows : Rows) (AO : LowJet → Basis → Pair) (j : LowJet)
    (ao_length : (rows.aoRows j).length = 98) (first_length : (rows.firstRows j).length = 98)
    (bilinear_length : (rows.bilinearRows j).length = 10)
    (ao_grid : ∀ b, grid (aoAt rows j b) = AO j b)
    (mid_exact : rows.aoMidRows j = (rows.aoRows j).map mid)
    (rad_exact : rows.aoRadRows j = (rows.aoRows j).map rad)
    (first_exact : ∀ b, firstAt rows j b =
      pointDot (rows.aoMidRows j) (rows.aoRadRows j) (PointColumns.column b))
    (bilinear_exact : ∀ k, bilinearAt rows j k = dotList (rows.firstRows j) (rows.aoRows k)) :
    RowComputed rows AO j where
  ao_length := ao_length
  first_length := first_length
  bilinear_length := bilinear_length
  ao_grid := congrArg List.ofFn (funext ao_grid)
  mid_exact := mid_exact
  rad_exact := rad_exact
  first_exact := congrArg List.ofFn (funext first_exact)
  bilinear_exact := congrArg List.ofFn (funext bilinear_exact)

end
end LAlanine40K2025.BasinRefinement.WholeBandMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
