import H0mework.Foundation.Runtime.AnswerHistory

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- The exact state reached after a finite number of source-generated root
successors.  No table of future states is stored. -/
def SourceNativeLivingRootProcess.stateAfter
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) : Nat → process.State
  | 0 => process.initial
  | index + 1 => process.successor (process.stateAfter index)

@[simp] theorem SourceNativeLivingRootProcess.stateAfter_zero
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) :
    process.stateAfter 0 = process.initial :=
  rfl

@[simp] theorem SourceNativeLivingRootProcess.stateAfter_succ
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    (index : Nat) :
    process.stateAfter (index + 1) =
      process.successor (process.stateAfter index) :=
  rfl

/-- A global invariant is lawful only through a source seed and one local
successor rule.  There is deliberately no field of type
`∀ index, InvariantAt (stateAfter index)`. -/
structure SourceNativeGeneratedInvariantLaw
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) : Type (u + 1) where
  private mk ::
  InvariantAt : process.State → Type u
  initialAt : InvariantAt process.initial
  advanceAt : (state : process.State) →
    InvariantAt state → InvariantAt (process.successor state)

def SourceNativeGeneratedInvariantLaw.create
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (InvariantAt : process.State → Type u)
    (initialAt : InvariantAt process.initial)
    (advanceAt : (state : process.State) →
      InvariantAt state → InvariantAt (process.successor state)) :
    SourceNativeGeneratedInvariantLaw process :=
  ⟨InvariantAt, initialAt, advanceAt⟩

/-- Canonical invariant witness at one generated depth. -/
def SourceNativeGeneratedInvariantLaw.generatedAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedInvariantLaw process) :
    (index : Nat) → law.InvariantAt (process.stateAfter index)
  | 0 => law.initialAt
  | index + 1 => law.advanceAt (process.stateAfter index) (law.generatedAt index)

@[simp] theorem SourceNativeGeneratedInvariantLaw.generatedAt_zero
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedInvariantLaw process) :
    law.generatedAt 0 = law.initialAt :=
  rfl

@[simp] theorem SourceNativeGeneratedInvariantLaw.generatedAt_succ
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedInvariantLaw process)
    (index : Nat) :
    law.generatedAt (index + 1) =
      law.advanceAt (process.stateAfter index) (law.generatedAt index) :=
  rfl

/-- Authority-free token for the canonical recursively generated invariant
history.  Its private empty constructor prevents a caller from replacing the
generated family by an independently supplied completed future. -/
structure SourceNativeGeneratedInvariantHistoryAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (_law : SourceNativeGeneratedInvariantLaw process) : Type where
  private mk ::

def SourceNativeGeneratedInvariantLaw.generateHistory
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedInvariantLaw process) :
    SourceNativeGeneratedInvariantHistoryAt law :=
  ⟨⟩

def SourceNativeGeneratedInvariantHistoryAt.at
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedInvariantLaw process}
    (_history : SourceNativeGeneratedInvariantHistoryAt law)
    (index : Nat) : law.InvariantAt (process.stateAfter index) :=
  law.generatedAt index

namespace SourceNativeGeneratedInvariantHistoryAt

/-- Exact living current carrying one recursively generated invariant
witness. -/
def currentAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedInvariantLaw process}
    (_history : SourceNativeGeneratedInvariantHistoryAt law)
    (index : Nat) : SourceNativeLivingRootCurrentAt N :=
  process.stateAt (process.stateAfter index)

/-- Invariant induction follows the fixed root successor rather than an
independent natural-number schedule. -/
theorem current_succ_is_generated
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedInvariantLaw process}
    (history : SourceNativeGeneratedInvariantHistoryAt law)
    (index : Nat) :
    (history.currentAt index).IsGeneratedSuccessor
      (history.currentAt (index + 1)) :=
  (process.successorAt (process.stateAfter index)).2

/-- A fixed local induction law has one canonical generated history token. -/
theorem unique
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedInvariantLaw process}
    (left right : SourceNativeGeneratedInvariantHistoryAt law) : left = right := by
  cases left
  cases right
  rfl

end SourceNativeGeneratedInvariantHistoryAt

/-- Local patch generation and its one-step restriction law.

Only the source patch and local advance are stored.  In particular there is
no field `(state : process.State) → PatchAt state`, which would become a
completed future table whenever the process state itself is a time index. -/
structure SourceNativeGeneratedContinuityLaw
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) : Type (u + 1) where
  private mk ::
  PatchAt : process.State → Type u
  initialAt : PatchAt process.initial
  advanceAt : (state : process.State) →
    PatchAt state → PatchAt (process.successor state)
  restrictAt : (state : process.State) →
    PatchAt (process.successor state) → PatchAt state
  advance_restricts : (state : process.State) → (patch : PatchAt state) →
    restrictAt state (advanceAt state patch) = patch

def SourceNativeGeneratedContinuityLaw.create
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (PatchAt : process.State → Type u)
    (initialAt : PatchAt process.initial)
    (advanceAt : (state : process.State) →
      PatchAt state → PatchAt (process.successor state))
    (restrictAt : (state : process.State) →
      PatchAt (process.successor state) → PatchAt state)
    (advance_restricts : (state : process.State) → (patch : PatchAt state) →
      restrictAt state (advanceAt state patch) = patch) :
    SourceNativeGeneratedContinuityLaw process :=
  ⟨PatchAt, initialAt, advanceAt, restrictAt, advance_restricts⟩

/-- Canonical patch generated at one finite root depth. -/
def SourceNativeGeneratedContinuityLaw.generatedAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedContinuityLaw process) :
    (index : Nat) → law.PatchAt (process.stateAfter index)
  | 0 => law.initialAt
  | index + 1 => law.advanceAt (process.stateAfter index)
      (law.generatedAt index)

@[simp] theorem SourceNativeGeneratedContinuityLaw.generatedAt_zero
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedContinuityLaw process) :
    law.generatedAt 0 = law.initialAt :=
  rfl

@[simp] theorem SourceNativeGeneratedContinuityLaw.generatedAt_succ
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedContinuityLaw process)
    (index : Nat) :
    law.generatedAt (index + 1) =
      law.advanceAt (process.stateAfter index) (law.generatedAt index) :=
  rfl

/-- Universal observation-cone factorization.  A completed candidate family
may appear in this theorem only as a conditional readout: seed and local
advance force every finite component to be the source-generated one. -/
theorem SourceNativeGeneratedContinuityLaw.generatedAt_unique
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedContinuityLaw process)
    (candidate : (index : Nat) →
      law.PatchAt (process.stateAfter index))
    (initial_commutes : candidate 0 = law.initialAt)
    (advance_commutes : (index : Nat) →
      candidate (index + 1) =
        law.advanceAt (process.stateAfter index) (candidate index)) :
    (index : Nat) → candidate index = law.generatedAt index
  | 0 => initial_commutes
  | index + 1 =>
      (advance_commutes index).trans
        (congrArg (law.advanceAt (process.stateAfter index))
          (law.generatedAt_unique candidate initial_commutes
            advance_commutes index))

/-- The continuum is the canonical compatible family generated by the fixed
root process.  It stores no function `Nat → Patch`, global path, limit point,
or consumer-selected completion. -/
structure SourceNativeGeneratedContinuumAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (_law : SourceNativeGeneratedContinuityLaw process) : Type where
  private mk ::

def SourceNativeGeneratedContinuityLaw.generate
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    (law : SourceNativeGeneratedContinuityLaw process) :
    SourceNativeGeneratedContinuumAt law :=
  ⟨⟩

namespace SourceNativeGeneratedContinuumAt

/-- Exact full living current underlying one local patch. -/
def currentAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (_continuum : SourceNativeGeneratedContinuumAt law)
    (index : Nat) : SourceNativeLivingRootCurrentAt N :=
  process.stateAt (process.stateAfter index)

/-- Local patch generated at one finite depth. -/
def patchAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (_continuum : SourceNativeGeneratedContinuumAt law)
    (index : Nat) : law.PatchAt (process.stateAfter index) :=
  law.generatedAt index

/-- Adjacent patches commute exactly under the source-owned restriction. -/
theorem restrict_succ_eq
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (continuum : SourceNativeGeneratedContinuumAt law)
    (index : Nat) :
    law.restrictAt (process.stateAfter index) (continuum.patchAt (index + 1)) =
      continuum.patchAt index := by
  exact law.advance_restricts (process.stateAfter index) (law.generatedAt index)

/-- The adjacent local patches are indexed by the exact generated root
successor, not by an independent chronology. -/
theorem current_succ_is_generated
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (continuum : SourceNativeGeneratedContinuumAt law)
    (index : Nat) :
    (continuum.currentAt index).IsGeneratedSuccessor
      (continuum.currentAt (index + 1)) :=
  (process.successorAt (process.stateAfter index)).2

/-- The generated continuum is terminal among families obeying the same
source seed and local transition law, pointwise at every finite view. -/
theorem patchAt_eq_of_local_generation
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (continuum : SourceNativeGeneratedContinuumAt law)
    (candidate : (index : Nat) →
      law.PatchAt (process.stateAfter index))
    (initial_commutes : candidate 0 = law.initialAt)
    (advance_commutes : (index : Nat) →
      candidate (index + 1) =
        law.advanceAt (process.stateAfter index) (candidate index))
    (index : Nat) :
    candidate index = continuum.patchAt index :=
  law.generatedAt_unique candidate initial_commutes advance_commutes index

/-- There is only one generated compatible-family token for a fixed law. -/
theorem unique
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {law : SourceNativeGeneratedContinuityLaw process}
    (left right : SourceNativeGeneratedContinuumAt law) : left = right := by
  cases left
  cases right
  rfl

end SourceNativeGeneratedContinuumAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
