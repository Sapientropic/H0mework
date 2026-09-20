import H0mework.Arithmetic.SourceAtoms.EndpointCoordinates

/-!
# Dependency-light SU(7)/A6 root datum extension

`SU7A6EndpointCoordinateCore` is the unique owner of the A6 Dynkin-coordinate
carrier, Cartan lowering action, signed-height readout, and endpoint/source
encoding.  This module adds only the unfiltered unit-descent neighbor used at
the high-level repair boundary.

Keeping the neighbor in this thin extension lets physical source lineage
consume the shared coordinate authority without importing branching,
no-prime filtering, P459/P508/P523, completion, or a repair producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

/-- An unfiltered A6 root-graph neighbor carrying exact signed-height unit
descent. -/
structure SU7A6UnfilteredUnitDescentNeighbor
    (source : SU7A6WeightLabel) where
  root : Fin 6
  target : SU7A6WeightLabel
  root_move : SU7A6SimpleRootMove source target
  signed_height_unit :
    su7A6SignedHeight target + 1 = su7A6SignedHeight source

/-- The unfiltered A6 graph has a concrete unit-descent neighbor at any chosen
simple root. -/
def su7A6UnfilteredUnitDescentNeighborAt
    (source : SU7A6WeightLabel) (i : Fin 6) :
    SU7A6UnfilteredUnitDescentNeighbor source where
  root := i
  target := su7A6LowerBySimpleRoot i source
  root_move := ⟨i, rfl⟩
  signed_height_unit := su7A6SignedHeight_lowerBySimpleRoot source i

/-- Positive-height form of the unfiltered theorem.

The positivity assumption matches the residual-use site; the unfiltered A6
graph itself supplies a unit descent from every label. -/
theorem su7A6_unfiltered_positive_unit_descent_neighbor
    (source : SU7A6WeightLabel)
    (_hpos : 0 < su7A6SignedHeight source) :
    Nonempty (SU7A6UnfilteredUnitDescentNeighbor source) :=
  ⟨su7A6UnfilteredUnitDescentNeighborAt source ⟨0, by decide⟩⟩

end
end StandardModelConstraint
end SaturationMonoid
