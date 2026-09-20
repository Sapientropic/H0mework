import H0mework.Arithmetic.SourceAtoms.SourcePotentialPathAntisymmetry

/-!
# Source strict-potential path antisymmetry

This file lowers the potential hard-door input one step further.

Instead of separately proving nonincrease and equal-potential collapse, a
source category may provide the more dynamics-shaped law:

```text
every source path either is already closed,
or strictly lowers a native potential / grade / height
```

This is the shape expected from directed lowering / branching / crystal-style
source paths.  It is still a source-only condition; endpoint atomhood remains
an arithmetic readout elsewhere.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source paths are either closed or strictly lower a source potential. -/
structure SourceStrictPotentialPath
    (SourceEvidence : Type u)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  potential : SourceEvidence -> Nat
  path_strict_or_closed :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        target = source ∨ potential target < potential source

namespace SourceStrictPotentialPath

variable {SourceEvidence : Type u}
variable {Source : RepresentationFeasibleCategory SourceEvidence}

/-- Strict-or-closed potential paths induce the nonincreasing/equal-collapse
potential socket. -/
def toSourcePathPotentialAntisymmetry
    (P : SourceStrictPotentialPath SourceEvidence Source) :
    SourcePathPotentialAntisymmetry SourceEvidence Source where
  potential := P.potential
  path_nonincreasing := by
    intro source target hPath
    rcases P.path_strict_or_closed hPath with hClosed | hStrict
    · exact Nat.le_of_eq (congrArg P.potential hClosed)
    · exact Nat.le_of_lt hStrict
  two_way_equal_potential_closes := by
    intro source target hForward _hBackward hPotential
    rcases P.path_strict_or_closed hForward with hClosed | hStrict
    · exact hClosed
    · exact False.elim
        ((Nat.not_lt_of_ge (Nat.le_of_eq hPotential.symm)) hStrict)

/-- Strict-or-closed potential paths induce the path antisymmetry consumed by
the source holonomy hard door. -/
theorem toSourcePathAntisymmetry
    (P : SourceStrictPotentialPath SourceEvidence Source) :
    SourcePathAntisymmetry SourceEvidence Source :=
  P.toSourcePathPotentialAntisymmetry.toSourcePathAntisymmetry

end SourceStrictPotentialPath

namespace CrystalBranchingSource

/-- Rank-one monotone paths satisfy the strict-or-closed potential law with
height itself as potential. -/
def rankOneSourceStrictPotentialPath :
    SourceStrictPotentialPath Nat rankOneSourceCategory where
  potential := id
  path_strict_or_closed := by
    intro source target hPath
    by_cases hClosed : target = source
    · exact Or.inl hClosed
    · exact Or.inr (lt_of_le_of_ne hPath hClosed)

/-- The rank-one potential antisymmetry object factors through the
strict-or-closed potential law. -/
def rankOneSourcePathPotentialAntisymmetryOfStrictPotential :
    SourcePathPotentialAntisymmetry Nat rankOneSourceCategory :=
  rankOneSourceStrictPotentialPath.toSourcePathPotentialAntisymmetry

/-- The rank-one path antisymmetry proof also factors through the
strict-or-closed potential law. -/
theorem rankOneSourcePathAntisymmetryOfStrictPotential :
    SourcePathAntisymmetry Nat rankOneSourceCategory :=
  rankOneSourceStrictPotentialPath.toSourcePathAntisymmetry

end CrystalBranchingSource


end RepresentationArithmeticAtomProjectionDefect
