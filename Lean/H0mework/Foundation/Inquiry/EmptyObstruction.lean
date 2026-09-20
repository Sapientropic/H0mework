import Mathlib.Logic.IsEmpty.Defs
import H0mework.Foundation.Inquiry.ObstructionLineage

/-!
# Canonical U7 calculus for an empty obstruction language

When every obstruction fibre of a world network is empty, its U7 producer,
event source, and evolution compiler are uniquely vacuous.  The constructors
below consume only the fibrewise emptiness proof; no demand, event, ledger row,
disposition, root, emitter, or future is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedEmptyObstructionU7

universe u

/-- Canonical vacuous demand producer. -/
def producer
    (N : WorldRelationNetwork.{u})
    (empty : (support : N.Support) → IsEmpty (N.ObstructionAt support)) :
    U7ProducerCalculus N where
  DemandAt := by
    intro support obstruction
    exact False.elim ((empty support).false obstruction)
  generateDemand := by
    intro support obstruction
    exact False.elim ((empty support).false obstruction)

/-- No actual U7 event can exist before an obstruction exists. -/
def source
    (N : WorldRelationNetwork.{u})
    (empty : (support : N.Support) → IsEmpty (N.ObstructionAt support)) :
    U7ActualSuccessorSource N (producer N empty) where
  EventAt := by
    intro support obstruction demand
    exact False.elim ((empty support).false obstruction)
  emit := by
    intro support obstruction
    exact False.elim ((empty support).false obstruction)
  demandGeneratedAt := by
    intro support obstruction demand event
    exact False.elim ((empty support).false obstruction)
  demandEntryAt := by
    intro support obstruction demand event
    exact False.elim ((empty support).false obstruction)

/-- Canonical vacuous U7 evolution compiler. -/
def calculus
    (N : WorldRelationNetwork.{u})
    (empty : (support : N.Support) → IsEmpty (N.ObstructionAt support)) :
    U7ObstructionEvolutionCalculus N (producer N empty) where
  source := source N empty
  compile := by
    intro support obstruction demand event
    exact False.elim ((empty support).false obstruction)

end RootGeneratedEmptyObstructionU7
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
