import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer

/-!
# Zero Law: no unaccounted world difference

This is the derived admission surface of the existing causally closed root,
not a ninth living-law constitution and not a caller-supplied audit record.

A lawful world state is exactly one generated temporal visit of one fixed,
complete-inventory-admitted source-native root: finite, source-owned cofinal, or a generated
successor after cofinal landing.  Its registered occurrence, whole generated
evolution, current patch, and exhaustive positive disposition are all
recomputed from that same visit.  Consequently a difference between two
lawful states is already a difference between registered root occurrences.

Arbitrary Lean data may still wrap a lawful state with an extra field.  Such
a wrapper is only a presentation: the extra field has no world identity and
cannot enter this API.  To become an actual difference it must instead change
the source/root occurrence or be registered by a later residual/U8 event.
If it is forever operationally indistinguishable, it remains in the same
presentation class rather than defining another lawful world state.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ZeroLawRootAdmission

universe u

/-- The zero-law admission carrier is the unified temporal root history; no
second registry or world-state record is added. -/
abbrev LawfulWorldStateAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V) : Type (u + 1) :=
  SourceNativeTemporalVisitAt root.toLedgerRoot

/-- Exact registered occurrence of a lawful state. -/
def LawfulWorldStateAt.registeredOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (state : LawfulWorldStateAt root) :
    ExactTemporalCausalRootEvent root.toLedgerRoot :=
  ⟨state, root.toLedgerRoot.exactTemporalCausalEventAt state⟩

/-- Complete-source temporal authority at this lawful state. -/
def LawfulWorldStateAt.authoritativeEvolution
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (state : LawfulWorldStateAt root) :
    SourceNativeAuthoritativeTemporalEvolutionAt root state :=
  root.authoritativeEvolutionAt state

/-- Exhaustive native/relation/continued/redirect/terminal/extension
disposition read from the same compiler image. -/
def LawfulWorldStateAt.positiveDisposition
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (state : LawfulWorldStateAt root) :
    SourceNativeLedgerEvolutionAt root.source.restructuringSource.source
      (root.emitted state.current) :=
  root.generatedLedgerAt state.current

/-- World identity is occurrence identity: two admitted states with the same
registered root occurrence are the same generated visit. -/
theorem LawfulWorldStateAt.eq_of_registeredOccurrence_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    {left right : LawfulWorldStateAt root}
    (same : left.registeredOccurrence = right.registeredOccurrence) :
    left = right :=
  congrArg Sigma.fst same

/-- Zero-law positive form: any actual difference between lawful states is
already visible as a difference between exact registered occurrences. -/
theorem LawfulWorldStateAt.registeredOccurrence_ne_of_ne
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    {left right : LawfulWorldStateAt root}
    (different : left ≠ right) :
    left.registeredOccurrence ≠ right.registeredOccurrence := by
  intro same
  exact different (LawfulWorldStateAt.eq_of_registeredOccurrence_eq same)

end ZeroLawRootAdmission
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
