import H0mework.Versions.Y.Arithmetic.RiemannSource.ThetaEulerOverlap

/-!
# Owner-indexed generated Riemann zero read

A zero is a conditional observation of the analytic function already born
from the theta--Mellin occurrence.  It is indexed by that exact owner and is
transported branchwise through certified analytic equality.  This module
does not claim that the source emits a completed inventory of zeros.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open RootedAccountedUnfolding

noncomputable section

abbrev ActualAnalyticOwner : GlobalGermOwner :=
  generatedRiemannAnalyticContinuationOccurrence.root.1

theorem actualAnalyticOwner_eq_globalGermOwner :
    ActualAnalyticOwner = globalGermOccurrence.root :=
  rfl

/-- A zero observation indexed by the exact owner of the generated analytic
function.  The private constructor prevents replacing that function. -/
structure GeneratedRiemannZeroObservationAt
    (owner : GlobalGermOwner) : Type 5 where
  private mk ::
  coordinate : ℂ
  zero : generatedRiemannZeta owner coordinate = 0

namespace GeneratedRiemannZeroObservationAt

def observe (owner : GlobalGermOwner) (coordinate : ℂ)
    (zero : generatedRiemannZeta owner coordinate = 0) :
    GeneratedRiemannZeroObservationAt owner :=
  ⟨coordinate, zero⟩

theorem ext {owner : GlobalGermOwner}
    (left right : GeneratedRiemannZeroObservationAt owner)
    (coordinate_eq : left.coordinate = right.coordinate) : left = right := by
  cases left
  cases right
  cases coordinate_eq
  rfl

theorem mathlibZero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    riemannZeta observation.coordinate = 0 := by
  rw [← generatedRiemannZeta_eq_mathlib owner]
  exact observation.zero

def ofMathlibZero (owner : GlobalGermOwner) (coordinate : ℂ)
    (zero : riemannZeta coordinate = 0) :
    GeneratedRiemannZeroObservationAt owner :=
  observe owner coordinate <| by
    rw [generatedRiemannZeta_eq_mathlib owner]
    exact zero

end GeneratedRiemannZeroObservationAt

abbrev GeneratedRiemannZeroObservation :=
  GeneratedRiemannZeroObservationAt ActualAnalyticOwner

namespace GeneratedRiemannZeroObservation

def observe (coordinate : ℂ)
    (zero : generatedRiemannZeta ActualAnalyticOwner coordinate = 0) :
    GeneratedRiemannZeroObservation :=
  GeneratedRiemannZeroObservationAt.observe
    ActualAnalyticOwner coordinate zero

theorem ext (left right : GeneratedRiemannZeroObservation)
    (coordinate_eq : left.coordinate = right.coordinate) : left = right :=
  GeneratedRiemannZeroObservationAt.ext left right coordinate_eq

theorem mathlibZero (observation : GeneratedRiemannZeroObservation) :
    riemannZeta observation.coordinate = 0 :=
  GeneratedRiemannZeroObservationAt.mathlibZero observation

def ofMathlibZero (coordinate : ℂ)
    (zero : riemannZeta coordinate = 0) :
    GeneratedRiemannZeroObservation :=
  GeneratedRiemannZeroObservationAt.ofMathlibZero
    ActualAnalyticOwner coordinate zero

/-- Rebuild the conditional observation from each branch's own generated
analytic function. -/
def transport (observation : GeneratedRiemannZeroObservation)
    (owner : GlobalGermOwner) : GeneratedRiemannZeroObservationAt owner :=
  GeneratedRiemannZeroObservationAt.observe owner observation.coordinate <| by
    rw [generatedRiemannZeta_eq_mathlib owner]
    exact observation.mathlibZero

@[simp] theorem ofMathlibZero_coordinate (coordinate : ℂ)
    (zero : riemannZeta coordinate = 0) :
    (ofMathlibZero coordinate zero).coordinate = coordinate :=
  rfl

end GeneratedRiemannZeroObservation

abbrev GeneratedZeroObservationPayload :=
  Σ analytic : AnalyticContinuationPayload,
    GeneratedRiemannZeroObservationAt analytic.1

/-- Observer-indexed conditional readout on the exact analytic occurrence. -/
def zeroObservationReadoutOccurrence
    (observation : GeneratedRiemannZeroObservation) :
    RootedAccountedUnfolding GeneratedZeroObservationPayload :=
  generatedRiemannAnalyticContinuationOccurrence.map fun analytic =>
    ⟨analytic, observation.transport analytic.1⟩

theorem zeroObservationReadoutOccurrence_projects
    (observation : GeneratedRiemannZeroObservation) :
    (zeroObservationReadoutOccurrence observation).map Sigma.fst =
      generatedRiemannAnalyticContinuationOccurrence := by
  rw [zeroObservationReadoutOccurrence, RootedAccountedUnfolding.map_map]
  change generatedRiemannAnalyticContinuationOccurrence.map id =
    generatedRiemannAnalyticContinuationOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem zeroObservationReadoutOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) :
    (((zeroObservationReadoutOccurrence observation).map Sigma.fst).map
        Sigma.fst).map Prod.fst =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [zeroObservationReadoutOccurrence_projects,
    generatedRiemannAnalyticContinuationOccurrence_projects,
    globalGermOccurrence_projects]

@[simp] theorem zeroObservationReadoutOccurrence_root_coordinate
    (observation : GeneratedRiemannZeroObservation) :
    (zeroObservationReadoutOccurrence observation).root.2.coordinate =
      observation.coordinate :=
  rfl

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
