import H0mework.Arithmetic.RiemannSource.FiniteThetaExposure

/-!
# Source-owned theta zero mode

The zero lattice term is emitted once from the exact global-germ owner.  It
is not inserted later as an unexplained constant in the Mellin formula.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open RootedAccountedUnfolding

noncomputable section

inductive ThetaZeroEventAt (owner : GlobalGermOwner) : Type 5
  | anchor
  | zeroMode

def thetaZeroPatch (owner : GlobalGermOwner) :
    RootedAccountedUnfolding (ThetaZeroEventAt owner) :=
  RootedAccountedUnfolding.zero .zeroMode

def thetaZeroOccurrence (owner : GlobalGermOwner) :
    RootedAccountedUnfolding (ThetaZeroEventAt owner) :=
  (RootedAccountedUnfolding.zero (.anchor)).advance
    (fun _ => thetaZeroPatch owner)

@[simp] theorem thetaZeroOccurrence_trace (owner : GlobalGermOwner) :
    (thetaZeroOccurrence owner).trace = [.anchor, .zeroMode] := by
  rfl

theorem thetaZeroOccurrence_event_provenance
    (owner : GlobalGermOwner) (event : ThetaZeroEventAt owner) :
    event ∈ (thetaZeroOccurrence owner).trace ↔
      event ∈ (RootedAccountedUnfolding.zero
        (ThetaZeroEventAt.anchor : ThetaZeroEventAt owner)).trace ∨
        ∃ leaf,
          leaf ∈ (RootedAccountedUnfolding.zero
            (ThetaZeroEventAt.anchor : ThetaZeroEventAt owner)).frontier ∧
            event ∈ (thetaZeroPatch owner).trace :=
  mem_trace_advance_iff (fun _ => thetaZeroPatch owner)
    (RootedAccountedUnfolding.zero
      (ThetaZeroEventAt.anchor : ThetaZeroEventAt owner)) event

noncomputable def thetaZeroWeight (owner : GlobalGermOwner) (t : ℝ) :
    ThetaZeroEventAt owner → ℝ
  | .anchor => 0
  | .zeroMode => Real.exp (-Real.pi * (0 : ℝ) ^ 2 * t)

noncomputable def thetaZeroFold (owner : GlobalGermOwner) (t : ℝ) : ℝ :=
  (thetaZeroOccurrence owner).fold
    (additiveFoldAlgebra (thetaZeroWeight owner t))

@[simp] theorem thetaZeroFold_eq_one
    (owner : GlobalGermOwner) (t : ℝ) :
    thetaZeroFold owner t = 1 := by
  unfold thetaZeroFold
  rw [← traceSum_eq_fold]
  simp [traceSum, thetaZeroWeight]

abbrev ZeroModePayload :=
  GlobalGermOwner × RootedAccountedUnfolding
    (ThetaZeroEventAt globalGermOccurrence.root)

/-- Same exact global-germ occurrence carrying the once-generated zero
mode.  The payload is computed from its owner; it is not caller supplied. -/
def thetaZeroModeOccurrence : RootedAccountedUnfolding
    (Σ owner : GlobalGermOwner,
      RootedAccountedUnfolding (ThetaZeroEventAt owner)) :=
  globalGermOccurrence.map fun owner =>
    ⟨owner, thetaZeroOccurrence owner⟩

theorem thetaZeroModeOccurrence_projects :
    thetaZeroModeOccurrence.map Sigma.fst = globalGermOccurrence := by
  rw [thetaZeroModeOccurrence, RootedAccountedUnfolding.map_map]
  change globalGermOccurrence.map id = globalGermOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem thetaZeroModeOccurrence_projects_to_seed :
    (thetaZeroModeOccurrence.map Sigma.fst).map Prod.fst =
      seedOccurrence := by
  rw [thetaZeroModeOccurrence_projects, globalGermOccurrence_projects]

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
