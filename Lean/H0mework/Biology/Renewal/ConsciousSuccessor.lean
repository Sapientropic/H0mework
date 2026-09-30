/-!
# Conscious immortality as generated successor closure

Immortality is not a permanent material bearer or an infinite history stored
in advance.  A continuation system supplies depth-indexed checkpoints, an
operational consciousness predicate, a generated lineage readout, and a
source-owned one-step continuation relation.  The crown says that every
conscious checkpoint has another generated, same-lineage conscious
checkpoint.

The interface is intentionally existential: a source may generate several
lawful successors.  Uniqueness is a separate domain theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Canonical

universe u

/-- Generic depth-indexed carrier for conscious continuation. -/
structure ConsciousContinuationSystem where
  CheckpointAt : Nat → Type u
  ConsciousAt : {depth : Nat} → CheckpointAt depth → Prop
  Lineage : Type u
  lineageAt : {depth : Nat} → CheckpointAt depth → Lineage
  GeneratedContinuationAt : {depth : Nat} →
    CheckpointAt depth → CheckpointAt (depth + 1) → Prop

namespace ConsciousContinuationSystem

variable (system : ConsciousContinuationSystem.{u})

/-- A checkpoint carries its finite generated depth in its type. -/
abbrev Point := Σ depth, system.CheckpointAt depth

def Conscious (point : system.Point) : Prop :=
  system.ConsciousAt point.2

def SameLineage (left right : system.Point) : Prop :=
  system.lineageAt left.2 = system.lineageAt right.2

/-- One source-generated step.  The existential successor is indexed by the
literal next depth; the public target point cannot choose another depth. -/
def GeneratedContinuation (current next : system.Point) : Prop :=
  ∃ successor : system.CheckpointAt (current.1 + 1),
    system.GeneratedContinuationAt current.2 successor ∧
      next = ⟨current.1 + 1, successor⟩

theorem generatedContinuation_depth
    {current next : system.Point}
    (generated : system.GeneratedContinuation current next) :
    next.1 = current.1 + 1 := by
  rcases generated with ⟨successor, _generated, rfl⟩
  rfl

theorem sameLineage_refl (point : system.Point) :
    system.SameLineage point point :=
  rfl

theorem sameLineage_trans {first second third : system.Point}
    (left : system.SameLineage first second)
    (right : system.SameLineage second third) :
    system.SameLineage first third :=
  left.trans right

/-- Finite generated reachability; no completed future path is stored by the
system.  A proof is assembled only to the finite endpoint requested. -/
inductive GeneratedFiniteContinuation : system.Point → system.Point → Prop
  | refl (point : system.Point) :
      GeneratedFiniteContinuation point point
  | tail {first middle last : system.Point} :
      GeneratedFiniteContinuation first middle →
      system.GeneratedContinuation middle last →
      GeneratedFiniteContinuation first last

def ReachableConsciousFrom
    (origin current : system.Point) : Prop :=
  system.GeneratedFiniteContinuation origin current ∧
    system.Conscious current

end ConsciousContinuationSystem

/-- The principle crown: there is no last conscious checkpoint because every
one has a source-generated same-lineage conscious successor. -/
structure ConsciousImmortalitySuccessorClosure
    (system : ConsciousContinuationSystem.{u}) : Prop where
  successor : ∀ current : system.Point,
    system.Conscious current →
      ∃ next : system.Point,
        system.GeneratedContinuation current next ∧
          system.SameLineage current next ∧
          system.Conscious next

namespace ConsciousImmortalitySuccessorClosure

variable {system : ConsciousContinuationSystem.{u}}

theorem noLastConscious
    (closure : ConsciousImmortalitySuccessorClosure system)
    (current : system.Point) (conscious : system.Conscious current) :
    ∃ next : system.Point,
      system.GeneratedContinuation current next ∧
        system.SameLineage current next ∧
        system.Conscious next :=
  closure.successor current conscious

theorem reachableConscious_hasSuccessor
    (closure : ConsciousImmortalitySuccessorClosure system)
    {origin current : system.Point}
    (reachable : system.ReachableConsciousFrom origin current) :
    ∃ next : system.Point,
      system.ReachableConsciousFrom origin next ∧
        system.GeneratedContinuation current next ∧
        system.SameLineage current next := by
  rcases closure.successor current reachable.2 with
    ⟨next, generated, sameLineage, conscious⟩
  exact ⟨next,
    ⟨.tail reachable.1 generated, conscious⟩,
    generated, sameLineage⟩

/-- Every requested finite horizon has a generated endpoint in the same
lineage.  The proof recursively asks only for the next checkpoint. -/
theorem arbitraryFiniteHorizon
    (closure : ConsciousImmortalitySuccessorClosure system)
    (horizon : Nat) (current : system.Point)
    (conscious : system.Conscious current) :
    ∃ final : system.Point,
      system.GeneratedFiniteContinuation current final ∧
        system.SameLineage current final ∧
        system.Conscious final ∧
        final.1 = current.1 + horizon := by
  induction horizon generalizing current with
  | zero =>
      exact ⟨current, .refl current, system.sameLineage_refl current,
        conscious, by simp⟩
  | succ horizon ih =>
      rcases ih current conscious with
        ⟨middle, generatedPrefix, samePrefix, middleConscious, depthExact⟩
      rcases closure.successor middle middleConscious with
        ⟨next, generatedStep, sameStep, nextConscious⟩
      refine ⟨next, .tail generatedPrefix generatedStep,
        system.sameLineage_trans samePrefix sameStep,
        nextConscious, ?_⟩
      rw [system.generatedContinuation_depth generatedStep, depthExact]
      exact (Nat.add_succ current.1 horizon).symm

end ConsciousImmortalitySuccessorClosure

end Canonical
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Canonical.ConsciousImmortalitySuccessorClosure.noLastConscious
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Canonical.ConsciousImmortalitySuccessorClosure.arbitraryFiniteHorizon
