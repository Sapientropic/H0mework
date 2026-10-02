import Mathlib.Data.Complex.Basic
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CofinalReversalRelation

/-!
# Coordinate projection obstruction for the cofinal reversal carrier

The coordinate-free relation carrier is upstream of every complex
coordinate.  This file tests the only legitimate final direction: a
classical coordinate may be read from that carrier only through its actual
quotient relation.  Already on one generated dual pair, such a projection
exists exactly when the coordinate is fixed by `s ↦ 1 - conj s`.

This is a representation obstruction, not a producer and not a premise for
the arithmetic source.  In particular, quotienting by reversal before the
classical projection cannot manufacture the missing landing law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCoordinateProjectionObstruction

open CanonicalUnitArithmeticCofinalReversalRelation
open scoped ComplexConjugate

noncomputable section

def coordinateReversal (coordinate : ℂ) : ℂ :=
  1 - conj coordinate

/-- One actual generator in one prime-stage dual pair. -/
def stageBasis (stage : Nat) (primeIndex : Fin (StageRank stage))
    (dualIndex : Fin 2) : StageRelationLattice stage :=
  Pi.single (primeIndex, dualIndex) 1

/-- Its class in the generated anti-invariant cokernel. -/
def stageGenerator (stage : Nat) (primeIndex : Fin (StageRank stage))
    (dualIndex : Fin 2) : StageCarrier stage := by
  unfold StageCarrier
  exact Submodule.Quotient.mk (stageBasis stage primeIndex dualIndex)

theorem stageBoundary_stageBasis
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (dualIndex : Fin 2) :
    stageBoundary stage (stageBasis stage primeIndex dualIndex) =
      stageBasis stage primeIndex dualIndex -
        stageBasis stage primeIndex dualIndex.rev := by
  unfold stageBoundary
  rw [weightedStageReversal_eq_reversal]
  ext index
  simp [stageBasis, stageReversal, Pi.single_apply, Prod.ext_iff,
    Fin.rev_eq_iff]

/-- The source-generated `id - reversal` boundary identifies the two sides
of every actual dual pair in the cokernel. -/
theorem stageGenerator_reversal_eq
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (dualIndex : Fin 2) :
    stageGenerator stage primeIndex dualIndex =
      stageGenerator stage primeIndex dualIndex.rev := by
  unfold stageGenerator StageCarrier
  apply (Submodule.Quotient.eq _).2
  change stageBasis stage primeIndex dualIndex -
      stageBasis stage primeIndex dualIndex.rev ∈
        LinearMap.range (stageBoundary stage)
  exact ⟨stageBasis stage primeIndex dualIndex,
    stageBoundary_stageBasis stage primeIndex dualIndex⟩

/-- A final coordinate readout that sends the two generated sides to the
claimed classical coordinate and its reversal.  No algebraic strength is
hidden in `project`; even a bare function must respect equality in the
quotient. -/
structure DualPairCoordinateProjectionAt
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) : Type where
  project : StageCarrier stage → ℂ
  original : project (stageGenerator stage primeIndex 0) = coordinate
  reversed : project (stageGenerator stage primeIndex 1) =
    coordinateReversal coordinate

/-- Exact typed obstruction: a classical projection through the generated
reversal quotient exists iff the requested coordinate is already fixed.
Thus the quotient cannot be used as a post-hoc producer of fixedness. -/
theorem nonempty_coordinateProjection_iff_fixed
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    Nonempty (DualPairCoordinateProjectionAt stage primeIndex coordinate) ↔
      coordinate = coordinateReversal coordinate := by
  constructor
  · rintro ⟨projection⟩
    have sameGenerator := stageGenerator_reversal_eq stage primeIndex (0 : Fin 2)
    have sameValue := congrArg projection.project sameGenerator
    exact projection.original.symm.trans <|
      sameValue.trans projection.reversed
  · intro fixed
    refine ⟨{
      project := fun _ => coordinate
      original := rfl
      reversed := fixed
    }⟩

end
end CanonicalUnitArithmeticCoordinateProjectionObstruction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
