import H0mework.Foundation.Cofinal.TemporalAnswer

/-!
# Source-fixed root answer-and-next histories

`LivingLawRootTemporalAnswerNextKernel` generates one typed answer and one next
authoritative root current for finite, cofinal, and post-cofinal visits.  A
process history additionally needs the living source law at that target;
otherwise a caller could install a new continuation law between two steps.

This kernel fixes the complete reachable-state registry in one source-owned
process.  `stateAt` is an embedding, so an opaque process state cannot carry a
future bit omitted from the registered living current.  The current root
compiler generates the next authoritative root/current; the process source
law fixes which complete living registry entry realizes that target.
`successorAt` emits both in one dependent object and proves their erasures
commute.  Finite histories then have only `exhausted` (observation fuel) and
`step`; there is no world-level `stopped` constructor.

The kernel is constructive and stores no completed execution table.  Every
row is generated recursively when a finite prefix is requested.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Heterogeneous living root/current package. -/
structure SourceNativeLivingRootCurrentAt
    (N : WorldRelationNetwork.{u}) : Type (u + 3) where
  V : Vocabulary.{u}
  root : SourceNativeLivingRootClosure N V
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot

/-- Forget only the pre-emitter continuation law. -/
def SourceNativeLivingRootCurrentAt.erase
    {N : WorldRelationNetwork.{u}}
    (current : SourceNativeLivingRootCurrentAt N) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  ⟨current.V, current.root.toAuthoritativeRoot, current.visit⟩

/-- Exact generated-successor relation for one complete living current.

The authoritative target equation and the branch-sensitive living-law rule
are one proposition.  They are deliberately not exposed as two independent
receipts: on a local terminal the second component contains no information,
so it must never be usable without the exact source-generated handoff target.
Continuing branches additionally preserve the complete living root rather
than only its erased authoritative presentation. -/
def SourceNativeLivingRootCurrentAt.IsGeneratedSuccessor
    {N : WorldRelationNetwork.{u}}
    (source target : SourceNativeLivingRootCurrentAt N) : Prop :=
  target.erase = source.root.generatedNextCurrentAt source.visit ∧
    match source.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        source.visit.current with
    | .faithfulTerminal .. => True
    | .nativeWrite ..
    | .relationWrite ..
    | .continuedTransport ..
    | .borromeanRedirect .. => HEq target.root source.root

/-- Complete source-owned root process.

`stateAt` is an injective presentation of the complete living current.  Thus
two states of this fixed process cannot share one registered root occurrence
while secretly selecting different futures.  Distinct process values are
distinct source laws; a root-local result alone cannot authorize either one.
`successorAt` is the one-step dependent compiler: it emits the next state and
its exact authoritative-root equation in one object. -/
structure SourceNativeLivingRootProcess
    (N : WorldRelationNetwork.{u}) : Type (u + 4) where
  State : Type u
  stateAt : State → SourceNativeLivingRootCurrentAt N
  stateAt_injective : Function.Injective stateAt
  initial : State
  successorAt : (state : State) →
    { successor : State //
      (stateAt state).IsGeneratedSuccessor (stateAt successor) }

/-- The source-generated next process state. -/
def SourceNativeLivingRootProcess.successor
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    (state : process.State) : process.State :=
  (process.successorAt state).1

/-- The generated next state is definitionally accompanied by its exact
authoritative-root answer-and-next equation; its complete living law remains
indexed by this fixed process rather than by a later adapter. -/
theorem SourceNativeLivingRootProcess.successor_eq
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    (state : process.State) :
    (process.stateAt (process.successor state)).erase =
      (process.stateAt state).root.generatedNextCurrentAt
        (process.stateAt state).visit :=
  (process.successorAt state).2.1

/-- A fixed-law process cannot hide a theory revision in a local terminal or
carrier handoff.  Every generated successor preserves the source state's root
law surface; U8 lives in the separate rooted revision engine. -/
theorem SourceNativeLivingRootProcess.successor_lawSurface_eq
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    (state : process.State) :
    (process.stateAt (process.successor state)).root.toAuthoritativeRoot.source.lawSurface =
      (process.stateAt state).root.toAuthoritativeRoot.source.lawSurface := by
  have target_eq := process.successor_eq state
  have target_law_eq := congrArg
    (fun current : SourceNativeAuthoritativeRootCurrentAt N =>
      current.root.source.lawSurface)
    target_eq
  exact target_law_eq.trans
    ((process.stateAt state).root.generatedNextCurrentAt_lawSurface_eq
      (process.stateAt state).visit)

/-- No hidden process-state bit can fork the future of one registered living
current.  Equal full currents force equal source states and hence the same
generated successor current. -/
theorem SourceNativeLivingRootProcess.successor_current_eq_of_current_eq
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    {left right : process.State}
    (current_eq : process.stateAt left = process.stateAt right) :
    process.stateAt (process.successor left) =
      process.stateAt (process.successor right) := by
  have state_eq := process.stateAt_injective current_eq
  cases state_eq
  rfl

/-- Any difference in the generated successor is already visible in the
registered source current.  A theorem parameter which leaves the complete
current unchanged cannot silently fork the next world. -/
theorem SourceNativeLivingRootProcess.successor_difference_reflects_current
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    {left right : process.State}
    (successor_ne :
      process.stateAt (process.successor left) ≠
        process.stateAt (process.successor right)) :
    process.stateAt left ≠ process.stateAt right := by
  intro current_eq
  exact successor_ne
    (process.successor_current_eq_of_current_eq current_eq)

/-- Raw finite process history.  `exhausted` means only that the requested
finite observation budget is zero. -/
inductive SourceNativeLivingRootHistoryAt
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) :
    Nat → process.State → Type (u + 4)
  | exhausted (state : process.State) :
      SourceNativeLivingRootHistoryAt process 0 state
  | step {fuel : Nat}
      {state : process.State}
      (tail : SourceNativeLivingRootHistoryAt process fuel
        (process.successor state)) :
      SourceNativeLivingRootHistoryAt process (fuel + 1) state

/-- Every finite prefix is recursively generated by the same process law. -/
def SourceNativeLivingRootProcess.generateHistory
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N) :
    (fuel : Nat) → (state : process.State) →
      SourceNativeLivingRootHistoryAt process fuel state
  | 0, state => .exhausted state
  | fuel + 1, state =>
      .step (process.generateHistory fuel (process.successor state))

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
