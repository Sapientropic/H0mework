import H0mework.Foundation.Ledger.CompilerFacade

/-!
# Causal-visit authority for source-native root ledgers

A current label is not an event identity.  A lawful recurrence may revisit the
same current after a different causal history, so a compiler image indexed only
by `current` can be spent again at the later visit.

This kernel supplies the finite causal ingredients consumed by the unified
temporal authority.  The exact `RootVisit` is its finite occurrence index.
Its `ReachableAt` witness can be generated only from the source-owned initial
current or by appending the exact successor of the fixed root evolution.  The
resulting temporal occurrence contains:

* the canonical finite incidence patch at the current visit;
* the complete causal prefix of prior visit-indexed finite patches; and
* the whole-ledger write-back generated at the exact visit.

The prefix is generated recursively from `RootClosure.ReachableAt`; it is not a
caller-supplied trace.  Each predecessor patch is itself indexed by its exact
visit and contains only occurrence-local generated rows.  Whole-ledger
destination/origin/discharge tables are static folds of those patches, never
one-step authority payloads.  An omitted identity-remainder entry receives no
standing authority: renewal must consume exact row membership.  Thus a repeated
current may have a new receipt only through a distinct generated visit.
Reapplying `RootVisit.next` is therefore a new actual recurrence: it consumes
the complete predecessor history and the fixed source compiler's successor
equation.  It cannot select a sibling target or omit the prior causal prefix.

The old `ReachableCompatibilityEvolutionAt` current-indexed wrapper has been
deleted: static ledger compatibility is read directly from the root, while
canonical authority is generated only by the unified temporal kernel.  There
is no finite-only receipt, compiler, or external event-source registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- One prior finite patch is identified by the exact causal visit at which it
was generated.  Its patch is read from the fixed root compiler below; there is
no independently replaceable patch field. -/
abbrev SourceNativeCausalLedgerPatch
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : Type u :=
  RootVisit root.toRoot

def SourceNativeCausalLedgerPatch.patch
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : SourceNativeCausalLedgerPatch root) :
    SourceNativeFiniteLedgerPatchAt root.source.source
      root.source.ledgerCompiler.ExactTransitionAt
      root.source.ledgerCompiler.writeRowSource
      root.source.ledgerCompiler.terminalRowSource
      (root.generatedLedgerAt visit.current) :=
  root.generatedPatchAt visit.current

namespace SourceNativeLedgerRootClosure

/-- Canonical causal trace of all finite patches preceding one reachable
current.  Every successor consumes the complete previous trace and appends
the exact patch generated at its predecessor visit. -/
def generatedPriorPatchesAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) :
    {current : V.Current} ->
      root.toRoot.ReachableAt current ->
      List (SourceNativeCausalLedgerPatch root)
  | _, .initial => []
  | _, @RootClosure.ReachableAt.step _ _ _ current _next prior _next_eq =>
      root.generatedPriorPatchesAt prior ++
        [⟨current, prior⟩]

end SourceNativeLedgerRootClosure

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
