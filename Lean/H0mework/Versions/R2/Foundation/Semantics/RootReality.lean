import H0mework.Foundation.Semantics.TotalReality
import H0mework.Versions.R2.Foundation.Authority.ZeroLawAdmission
import H0mework.Versions.R2.Foundation.Authority.Representation

/-!
# A causally closed root realizes total reality

This adapter pays the abstract `TotalRealityAt` contract with the existing
source-native root machinery.  A difference is a pair of lawful temporal root visits.
Actuality is witnessed by both canonical visit-compiler receipts; stable
reference fixes both exact registered occurrences; real difference is visit
inequality.  The registered-occurrence theorem then generates the positive
structural identity.

Nothing in this file accepts `NoMagic`, `NoExternalSupplement`, a difference
classifier, an occurrence inequality, or a second causal-closure token from a
consumer.  The result is a direct readout of the registered root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootTotalReality

open TotalReality
open ZeroLawRootAdmission

universe u

variable
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)

/-- One claim of difference inside a fixed source-native root. -/
abbrev RootDifference := LawfulWorldStateAt root × LawfulWorldStateAt root

/-- Both sides are actual compiler images of the same fixed root. -/
abbrev RootActualityAt (difference : RootDifference root) : Prop :=
  Nonempty (CanonicalReceiptAuthority.CanonicalReceipt
      root.temporalVisitAuthorityCompiler
      ⟨difference.1, difference.1.authoritativeEvolution⟩) ∧
    Nonempty (CanonicalReceiptAuthority.CanonicalReceipt
      root.temporalVisitAuthorityCompiler
      ⟨difference.2, difference.2.authoritativeEvolution⟩)

/-- Both sides have exact stable root references. -/
abbrev RootStableReferenceAt (difference : RootDifference root) : Prop :=
  (∃ leftOccurrence : ExactTemporalCausalRootEvent root.toLedgerRoot,
    leftOccurrence = difference.1.registeredOccurrence) ∧
  (∃ rightOccurrence : ExactTemporalCausalRootEvent root.toLedgerRoot,
    rightOccurrence = difference.2.registeredOccurrence)

/-- Root-owned realization of the weak difference vocabulary. -/
def semantics : RealityDifferenceSemantics where
  Difference := RootDifference root
  ActualAt := RootActualityAt root
  StableReferenceAt := RootStableReferenceAt root
  RealDifferenceAt := fun difference => difference.1 ≠ difference.2
  RedundantAt := fun difference =>
    difference.1.registeredOccurrence = difference.2.registeredOccurrence
  StructuralIdentityAt := fun difference =>
    difference.1.registeredOccurrence ≠ difference.2.registeredOccurrence

/-- A distinct pair of lawful visits generates its complete weak actual
difference witness from the root compiler. -/
theorem actualDifference
    {difference : RootDifference root}
    (different : difference.1 ≠ difference.2) :
    ActualDifferenceAt (semantics root) difference where
  actual :=
    ⟨⟨root.generatedAtTemporalVisit_isCanonical difference.1⟩,
      ⟨root.generatedAtTemporalVisit_isCanonical difference.2⟩⟩
  stableReference :=
    ⟨⟨difference.1.registeredOccurrence, rfl⟩,
      ⟨difference.2.registeredOccurrence, rfl⟩⟩
  realDifference := different

/-- The registered root positively locates every actual difference at its
exact registered-occurrence identity. -/
theorem isTotal : TotalRealityAt (semantics root) where
  locate := fun _difference actual =>
    Or.inr (LawfulWorldStateAt.registeredOccurrence_ne_of_ne
      actual.realDifference)

/-- No actual root difference can be an external supplement. -/
theorem noExternalSupplement {difference : RootDifference root} :
    ExternalSupplementAt (semantics root) difference -> False :=
  (isTotal root).noExternalSupplement

/-- Root-level no-magic is derived from positive totality, not supplied as a
world field. -/
theorem noMagicBit {difference : RootDifference root} :
    MagicBitAt (semantics root) difference -> False :=
  (isTotal root).noMagicBit

end RootTotalReality

/-! ## Total reality across living-root handoffs

The fixed-root adapter above classifies differences between temporal visits of
one authoritative root.  A living source process may cross a faithful local
terminal or a revised-law boundary, so its next registered current can use a
heterogeneous vocabulary and root.  The process already fixes that whole
registry through an injective `stateAt` and generates one canonical causal
answer-and-next occurrence at every state.  The following is therefore a
derived adapter, not another world law. -/

namespace RootProcessTotalReality

open TotalReality

universe u

variable
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)

/-- One claim of difference inside a fixed complete living source process. -/
abbrev ProcessDifference := process.State × process.State

/-- Both sides are canonical answer-and-next compiler images of the fixed
source process. -/
abbrev ProcessActualityAt (difference : ProcessDifference process) : Prop :=
  Nonempty (SourceNativeLivingProcessCausalEvolutionAt process
      (ULift.up difference.1)) ∧
    Nonempty (SourceNativeLivingProcessCausalEvolutionAt process
      (ULift.up difference.2))

/-- Both sides retain their exact process-indexed root occurrence. -/
abbrev ProcessStableReferenceAt
    (difference : ProcessDifference process) : Prop :=
  Nonempty (SourceNativeLivingProcessCausalOccurrenceAt process
      (ULift.up difference.1)) ∧
    Nonempty (SourceNativeLivingProcessCausalOccurrenceAt process
      (ULift.up difference.2))

/-- Root-owned realization of the weak difference vocabulary for the complete
source process.  Redundancy and structural identity compare full living
currents, including vocabulary, root, temporal visit, and terminal-handoff
law—not a projected current label. -/
def semantics : RealityDifferenceSemantics where
  Difference := ProcessDifference process
  ActualAt := ProcessActualityAt process
  StableReferenceAt := ProcessStableReferenceAt process
  RealDifferenceAt := fun difference => difference.1 ≠ difference.2
  RedundantAt := fun difference =>
    process.stateAt difference.1 = process.stateAt difference.2
  StructuralIdentityAt := fun difference =>
    process.stateAt difference.1 ≠ process.stateAt difference.2

/-- A distinct pair of process states generates both exact occurrences and
both canonical answer-and-next transitions from the same source process. -/
theorem actualDifference
    {difference : ProcessDifference process}
    (different : difference.1 ≠ difference.2) :
    ActualDifferenceAt (semantics process) difference where
  actual :=
    ⟨⟨process.canonicalCausalAnswerAndNext (ULift.up difference.1)⟩,
      ⟨process.canonicalCausalAnswerAndNext (ULift.up difference.2)⟩⟩
  stableReference :=
    ⟨⟨process.toAnswerNextCausalWorld.emitted (ULift.up difference.1)⟩,
      ⟨process.toAnswerNextCausalWorld.emitted (ULift.up difference.2)⟩⟩
  realDifference := different

/-- Injective registration prevents an opaque process state from changing the
future while retaining the same complete living current. -/
theorem registeredCurrent_ne_of_ne
    {left right : process.State}
    (different : left ≠ right) :
    process.stateAt left ≠ process.stateAt right := by
  intro sameCurrent
  exact different (process.stateAt_injective sameCurrent)

/-- The complete source process positively locates every actual difference at
its registered living-current identity, including differences across local
terminal and U8 handoffs. -/
theorem isTotal : TotalRealityAt (semantics process) where
  locate := fun _difference actual =>
    Or.inr (registeredCurrent_ne_of_ne process actual.realDifference)

/-- No actual difference inside the fixed source process can remain an
external supplement between two root epochs. -/
theorem noExternalSupplement {difference : ProcessDifference process} :
    ExternalSupplementAt (semantics process) difference -> False :=
  (isTotal process).noExternalSupplement

/-- Process-level no-magic follows from positive registered-current totality;
it is not supplied as a source field. -/
theorem noMagicBit {difference : ProcessDifference process} :
    MagicBitAt (semantics process) difference -> False :=
  (isTotal process).noMagicBit

end RootProcessTotalReality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
