import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Realization.Claims.P8

/-!
# Canonical pre-P950 SU7 raw coordinates

This is the dependency-light canonical coordinate layer for the active
Borromean/SU7 proof line.  The historical
`SaturationMonoid.SU7BranchingDecompositionCell` lives behind a long physical
and holonomy-oriented proposition chain; importing it into the source-only
core would destroy the intended dependency boundary.

The types here contain exactly the shared finite syntax needed before P950:
six Schubert branches, six `3 + 2 + 1 + 1` incidences, two raw weight codes,
and their additive residual energy.  They carry no Boolean atomicity,
irreducibility, no-prime spectrum membership, holonomy, endpoint realization,
or atom pair.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace BorromeanPreRealization

/-- Six source-side Schubert coordinates, before physical realization. -/
inductive CanonicalPreP950SU3Branch where
  | e
  | s1
  | s2
  | s1s2
  | s2s1
  | w0
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Six canonical incidences of the `3 + 2 + 1 + 1` carrier. -/
inductive CanonicalPreP950SU7Incidence where
  | colorWeak
  | colorPositiveSinglet
  | colorNegativeSinglet
  | weakPositiveSinglet
  | weakNegativeSinglet
  | positiveNegativeSinglet
  deriving DecidableEq, Repr, FintypeViaProxy

namespace CanonicalPreP950SU7Incidence

/-- Ordered endpoint-block dimensions of the concrete `3 + 2 + 1 + 1`
carrier.

This is representation syntax, not arithmetic endpoint atomhood.  It is the
dependency-light counterpart of the historical SU(7) incidence endpoint map:
`colorWeak` reads `(3,2)`, color-singlet incidences read `(3,1)`, weak-singlet
incidences read `(2,1)`, and the singlet-singlet incidence reads `(1,1)`. -/
def endpointBlockDimensions :
    CanonicalPreP950SU7Incidence -> Nat × Nat
  | .colorWeak => (3, 2)
  | .colorPositiveSinglet => (3, 1)
  | .colorNegativeSinglet => (3, 1)
  | .weakPositiveSinglet => (2, 1)
  | .weakNegativeSinglet => (2, 1)
  | .positiveNegativeSinglet => (1, 1)

/-- The canonically oriented second endpoint of an incidence supplies the
inward block dimension used by the source-side completion branch.

No primality or Boolean filter fact is attached to this natural number. -/
def inwardBlockDimension
    (incidence : CanonicalPreP950SU7Incidence) : Nat :=
  incidence.endpointBlockDimensions.2

/-- The canonically oriented first endpoint of an incidence supplies the
outward block dimension used by the terminal completion branch.

This is the ordered mate of `inwardBlockDimension`; it does not reverse the
incidence or choose a block from a desired endpoint code. -/
def outwardBlockDimension
    (incidence : CanonicalPreP950SU7Incidence) : Nat :=
  incidence.endpointBlockDimensions.1

@[simp] theorem colorWeak_endpointBlockDimensions :
    endpointBlockDimensions .colorWeak = (3, 2) := rfl

@[simp] theorem colorWeak_inwardBlockDimension :
    inwardBlockDimension .colorWeak = 2 := rfl

@[simp] theorem colorWeak_outwardBlockDimension :
    outwardBlockDimension .colorWeak = 3 := rfl

end CanonicalPreP950SU7Incidence

/-- Canonical raw branching cell over the even fiber `2 * n`. -/
structure CanonicalPreP950SU7BranchingCell (n : Nat) where
  branch : CanonicalPreP950SU3Branch
  incidence : CanonicalPreP950SU7Incidence
  leftWeightCode : Nat
  rightWeightCode : Nat
  deriving DecidableEq, Repr

/-- Signed raw residual of a canonical pre-P950 source cell. -/
def canonicalPreP950RawResidual
    {n : Nat} (cell : CanonicalPreP950SU7BranchingCell n) : Int :=
  ((cell.leftWeightCode + cell.rightWeightCode : Nat) : Int) -
    ((2 * n : Nat) : Int)

/-- Absolute additive energy of a canonical pre-P950 source cell. -/
def canonicalPreP950RawEnergy
    {n : Nat} (cell : CanonicalPreP950SU7BranchingCell n) : Nat :=
  Int.natAbs (canonicalPreP950RawResidual cell)

end BorromeanPreRealization
end RepresentationArithmeticAtomProjectionDefect
