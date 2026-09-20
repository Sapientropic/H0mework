import H0mework.Arithmetic.SourceAtoms.SourceAntisymmetricHolonomy

/-!
# Source potential path antisymmetry

This file lowers `SourcePathAntisymmetry` to a more native source-dynamics
obligation.

For GT / crystal / branching style sources, the expected proof shape is often
not "path antisymmetry" directly.  It is:

```text
source path is nonincreasing for a grade / height / potential
+ two-way paths at equal potential collapse to the same source evidence
-> source path antisymmetry
```

The arithmetic endpoint filter is not mentioned here.  This is only the
source-side hard-door input needed to rule out stable projection defects.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Potential-derived source path antisymmetry.

`potential` is the source-side grade/height readout.  A path may move inside a
level set, so we keep a separate equal-potential collapse law instead of
requiring strict decrease on every nontrivial path. -/
structure SourcePathPotentialAntisymmetry
    (SourceEvidence : Type u)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  potential : SourceEvidence -> Nat
  path_nonincreasing :
    ∀ {source target : SourceEvidence},
      Source.path source target -> potential target ≤ potential source
  two_way_equal_potential_closes :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        Source.path target source ->
          potential target = potential source ->
            target = source

namespace SourcePathPotentialAntisymmetry

variable {SourceEvidence : Type u}
variable {Source : RepresentationFeasibleCategory SourceEvidence}

/-- A source potential with nonincreasing paths and equal-level collapse
induces the path antisymmetry consumed by the holonomy hard door. -/
theorem toSourcePathAntisymmetry
    (P : SourcePathPotentialAntisymmetry SourceEvidence Source) :
    SourcePathAntisymmetry SourceEvidence Source := by
  refine { closes := ?_ }
  intro source target hForward hBackward
  exact
    P.two_way_equal_potential_closes
      hForward hBackward
      (Nat.le_antisymm
        (P.path_nonincreasing hForward)
        (P.path_nonincreasing hBackward))

end SourcePathPotentialAntisymmetry

namespace CrystalBranchingSource

/-- The rank-one monotone source path is the minimal sanity check for the
potential socket: height itself is the potential. -/
def rankOneSourcePathPotentialAntisymmetry :
    SourcePathPotentialAntisymmetry Nat rankOneSourceCategory where
  potential := id
  path_nonincreasing := by
    intro _source _target hPath
    exact hPath
  two_way_equal_potential_closes := by
    intro _source _target _hForward _hBackward hPotential
    exact hPotential

/-- The old rank-one antisymmetry proof factors through the potential socket. -/
theorem rankOneSourcePathAntisymmetryOfPotential :
    SourcePathAntisymmetry Nat rankOneSourceCategory :=
  rankOneSourcePathPotentialAntisymmetry.toSourcePathAntisymmetry

end CrystalBranchingSource


end RepresentationArithmeticAtomProjectionDefect
