import H0mework.Foundation.Authority.EntryDisposition
import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Foundation.Semantics.TheoryState

/-!
# Obstruction-generated minimal root coface

An exact rooted expressibility failure generates a free whole-network coface.
The old network is a constructive retract; the obstruction opens new support,
incidence, live-ledger, and claim coordinates with no old preimage.  The root
extension's exact target occurrence and whole-ledger write-back are the first
actual transition of the completion.

The completion does not contain a revised theory, a settlement, or a chosen
future.  Its universal property says that every admissible coface revision
receives a faithful injective factorization of the live-row, incidence, and
claim generators, pointwise unique once the old face and generators are fixed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- A constructive old-to-new embedding with an exact retraction on old data.
No `forward_backward` law is required, so the larger carrier may contain
genuinely new coordinates. -/
structure ConstructiveRetract (A B : Type u) : Type u where
  forward : A -> B
  backward : B -> A
  backward_forward : (value : A) -> backward (forward value) = value

/-- Whole-network non-conservative translation.  Old identities and live
ledger rows survive by constructive retracts; added coordinates need not have
old preimages. -/
structure TypedSemanticWorldNetworkTranslationAt
    (OldN NewN : WorldRelationNetwork.{u}) : Type (u + 2) where
  support : ConstructiveRetract OldN.Support NewN.Support
  anchor : ConstructiveRetract OldN.Anchor NewN.Anchor
  incidence : ConstructiveRetract OldN.Incidence NewN.Incidence
  lineage : ConstructiveRetract OldN.Lineage NewN.Lineage
  responsibility : ConstructiveRetract OldN.Responsibility NewN.Responsibility
  claim : ConstructiveRetract OldN.Claim NewN.Claim
  anchor_commutes : (oldSupport : OldN.Support) ->
    anchor.forward (OldN.anchorAt oldSupport) =
      NewN.anchorAt (support.forward oldSupport)
  incidence_commutes : (oldSupport : OldN.Support) ->
    incidence.forward (OldN.incidenceAt oldSupport) =
      NewN.incidenceAt (support.forward oldSupport)
  lineage_commutes : (oldSupport : OldN.Support) ->
    lineage.forward (OldN.lineageAt oldSupport) =
      NewN.lineageAt (support.forward oldSupport)
  oldOpenLedger : (oldSupport : OldN.Support) ->
    ConstructiveRetract
      (OpenResponsibilityAt OldN oldSupport)
      (OpenResponsibilityAt NewN (support.forward oldSupport))
  oldOpenClaim_commutes : (oldSupport : OldN.Support) ->
    (oldEntry : OpenResponsibilityAt OldN oldSupport) ->
      claim.forward oldEntry.claim =
        ((oldOpenLedger oldSupport).forward oldEntry).claim
  oldOpenProgressBudget_commutes : (oldSupport : OldN.Support) ->
    (oldEntry : OpenResponsibilityAt OldN oldSupport) ->
      ((oldOpenLedger oldSupport).forward oldEntry).progressBudget =
        oldEntry.progressBudget
  oldHoldsSurvives : (oldSupport : OldN.Support) ->
    (oldClaim : OldN.Claim) -> OldN.HoldsAt oldSupport oldClaim ->
      NewN.HoldsAt (support.forward oldSupport) (claim.forward oldClaim)
  oldDispositionSurvives : (oldSupport : OldN.Support) ->
    (kind : WorldDispositionKind) -> OldN.DispositionAt oldSupport kind ->
      NewN.DispositionAt (support.forward oldSupport) kind

/-- Token asserting that one fixed root compiler generated a nonterminal
initial write.  The target is read from that root evolution; the token stores
no U8 selection, revised carrier, or sibling branch. -/
def CanonicalFirstRootWriteAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : Type u :=
  match (root.toRoot.evolutionAt root.toRoot.source.initial).nextCurrent? with
  | some _ => PUnit
  | none => PEmpty

namespace CanonicalFirstRootWriteAt

instance instSubsingleton
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V} :
    Subsingleton (CanonicalFirstRootWriteAt root) := by
  unfold CanonicalFirstRootWriteAt
  split <;> infer_instance

def target
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (write : CanonicalFirstRootWriteAt root) : V.Current := by
  match next_eq :
      (root.toRoot.evolutionAt root.toRoot.source.initial).nextCurrent? with
  | some target => exact target
  | none =>
      unfold CanonicalFirstRootWriteAt at write
      rw [next_eq] at write
      exact PEmpty.elim write

theorem next_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (write : CanonicalFirstRootWriteAt root) :
    (root.toRoot.evolutionAt root.toRoot.source.initial).nextCurrent? =
      some write.target := by
  unfold target
  split
  · assumption
  · rename_i root_eq
    unfold CanonicalFirstRootWriteAt at write
    rw [root_eq] at write
    exact PEmpty.elim write

def targetVisit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (write : CanonicalFirstRootWriteAt root) : RootVisit root.toRoot :=
  root.toRoot.initialVisit.next write.next_eq

end CanonicalFirstRootWriteAt

namespace ObstructionGeneratedMinimalCoface

/-- Relative expressive capacity is a constructive old-face retract together
with a jointly injective family of generated coordinates.  The generator
carrier is source data; numerical rank is a finite Mathlib readout, not part
of the authority core. -/
structure RelativeExpressiveCapacity
    (Old New Generator : Type u) : Type u where
  oldFace : ConstructiveRetract Old New
  generator : Generator -> New
  embed : Old ⊕ Generator -> New
  embed_old : (old : Old) -> embed (.inl old) = oldFace.forward old
  embed_new : (index : Generator) -> embed (.inr index) = generator index
  injective : Function.Injective embed

/-- An alleged realization of one generated direction entirely through the
old face. -/
def OldFaceOnlyGeneratedCoordinateAt
    {Old New Generator : Type u}
    (capacity : RelativeExpressiveCapacity Old New Generator)
    (index : Generator) : Type u :=
  Sigma fun old : Old =>
    PLift (capacity.oldFace.forward old = capacity.generator index)

/-- A generated direction cannot be supplied by the old face.  Any consumer
that actually addresses this direction therefore cannot close through an
old-face-only realization. -/
theorem no_oldFaceOnlyGeneratedCoordinate
    {Old New Generator : Type u}
    (capacity : RelativeExpressiveCapacity Old New Generator)
    (index : Generator) :
    IsEmpty (OldFaceOnlyGeneratedCoordinateAt capacity index) :=
  ⟨fun alleged => by
    rcases alleged with ⟨old, equality⟩
    have collision : capacity.embed (.inl old) = capacity.embed (.inr index) :=
      calc
        capacity.embed (.inl old) = capacity.oldFace.forward old :=
          capacity.embed_old old
        _ = capacity.generator index := equality.down
        _ = capacity.embed (.inr index) := (capacity.embed_new index).symm
    cases capacity.injective collision⟩

/-- One genuinely new coordinate indexed by a source-generated singleton.

The generator carrier remains visible in the resulting type.  A unique
direction may carry zero additional choice while retaining the exact
source/failure index that generated it. -/
def relativeExpressiveCapacityUnique
    {Old New Generator : Type u}
    (oldFace : ConstructiveRetract Old New)
    (distinguished : Generator)
    (generator_unique : (index : Generator) -> index = distinguished)
    (newCoordinate : New)
    (hasNoOldPreimage : IsEmpty (Sigma fun old : Old =>
      PLift (oldFace.forward old = newCoordinate))) :
    RelativeExpressiveCapacity Old New Generator where
  oldFace := oldFace
  generator := fun _ => newCoordinate
  embed
    | .inl old => oldFace.forward old
    | .inr _ => newCoordinate
  embed_old := fun _ => rfl
  embed_new := fun _ => rfl
  injective := by
    intro left right equality
    cases left with
    | inl leftOld =>
        cases right with
        | inl rightOld =>
            have oldEquality := congrArg oldFace.backward equality
            rw [oldFace.backward_forward, oldFace.backward_forward] at oldEquality
            cases oldEquality
            rfl
        | inr _ =>
            exact False.elim <| hasNoOldPreimage.false
              ⟨leftOld, PLift.up equality⟩
    | inr leftIndex =>
        cases right with
        | inl rightOld =>
            exact False.elim <| hasNoOldPreimage.false
              ⟨rightOld, PLift.up equality.symm⟩
        | inr rightIndex =>
            rw [generator_unique leftIndex, generator_unique rightIndex]

namespace RelativeExpressiveCapacity

/-- Compose two constructive coface extensions.  The accumulated generator
carrier is a disjoint sum: a later extension cannot identify an earlier
generated direction with old data or with a later generated direction. -/
private def retractTrans
    {A B C : Type u}
    (left : ConstructiveRetract A B)
    (right : ConstructiveRetract B C) :
    ConstructiveRetract A C where
  forward := right.forward ∘ left.forward
  backward := left.backward ∘ right.backward
  backward_forward := by
    intro value
    exact calc
      left.backward (right.backward (right.forward (left.forward value))) =
          left.backward (left.forward value) :=
        congrArg left.backward (right.backward_forward (left.forward value))
      _ = value := left.backward_forward value

private def composeInput
    {Old Middle G₁ G₂ : Type u}
    (first : RelativeExpressiveCapacity Old Middle G₁) :
    Old ⊕ (G₁ ⊕ G₂) -> Middle ⊕ G₂
  | .inl old => .inl (first.embed (.inl old))
  | .inr (.inl firstIndex) => .inl (first.embed (.inr firstIndex))
  | .inr (.inr secondIndex) => .inr secondIndex

private theorem composeInput_injective
    {Old Middle G₁ G₂ : Type u}
    (first : RelativeExpressiveCapacity Old Middle G₁) :
    Function.Injective (composeInput (G₂ := G₂) first) := by
  intro left right equality
  cases left with
  | inl leftOld =>
      cases right with
      | inl rightOld =>
          have firstEquality := first.injective (Sum.inl.inj equality)
          exact congrArg Sum.inl (Sum.inl.inj firstEquality)
      | inr rightGenerator =>
          cases rightGenerator with
          | inl rightFirst =>
              have firstEquality := first.injective (Sum.inl.inj equality)
              cases firstEquality
          | inr rightSecond =>
              cases equality
  | inr leftGenerator =>
      cases leftGenerator with
      | inl leftFirst =>
          cases right with
          | inl rightOld =>
              have firstEquality := first.injective (Sum.inl.inj equality)
              cases firstEquality
          | inr rightGenerator =>
              cases rightGenerator with
              | inl rightFirst =>
                  have firstEquality := first.injective (Sum.inl.inj equality)
                  exact congrArg (fun index => Sum.inr (Sum.inl index))
                    (Sum.inr.inj firstEquality)
              | inr rightSecond =>
                  cases equality
      | inr leftSecond =>
          cases right with
          | inl rightOld =>
              cases equality
          | inr rightGenerator =>
              cases rightGenerator with
              | inl rightFirst =>
                  cases equality
              | inr rightSecond =>
                  exact congrArg (fun index => Sum.inr (Sum.inr index))
                    (Sum.inr.inj equality)

/-- Sequential expressive extensions accumulate their generated directions.
This is the constructive algebraic core used by multi-step coface histories;
it does not manufacture either source event. -/
def compose
    {Old Middle New G₁ G₂ : Type u}
    (first : RelativeExpressiveCapacity Old Middle G₁)
    (second : RelativeExpressiveCapacity Middle New G₂) :
    RelativeExpressiveCapacity Old New (G₁ ⊕ G₂) where
  oldFace := retractTrans first.oldFace second.oldFace
  generator
    | .inl firstIndex => second.oldFace.forward (first.generator firstIndex)
    | .inr secondIndex => second.generator secondIndex
  embed := fun input => second.embed (composeInput first input)
  embed_old := by
    intro old
    exact calc
      second.embed (composeInput first (.inl old)) =
          second.embed (.inl (first.oldFace.forward old)) :=
        congrArg (fun middle => second.embed (.inl middle))
          (first.embed_old old)
      _ = second.oldFace.forward (first.oldFace.forward old) :=
        second.embed_old (first.oldFace.forward old)
      _ = (retractTrans first.oldFace second.oldFace).forward old := rfl
  embed_new := by
    intro index
    cases index with
    | inl firstIndex =>
        exact calc
          second.embed (composeInput first (.inr (.inl firstIndex))) =
              second.embed (.inl (first.generator firstIndex)) :=
            congrArg (fun middle => second.embed (.inl middle))
              (first.embed_new firstIndex)
          _ = second.oldFace.forward (first.generator firstIndex) :=
            second.embed_old (first.generator firstIndex)
    | inr secondIndex =>
        exact second.embed_new secondIndex
  injective := by
    intro left right equality
    exact composeInput_injective first (second.injective equality)

private def generatorAssociator (G₁ G₂ G₃ : Type u) :
    ConstructivePresentation (G₁ ⊕ (G₂ ⊕ G₃)) ((G₁ ⊕ G₂) ⊕ G₃) where
  forward
    | .inl first => .inl (.inl first)
    | .inr (.inl second) => .inl (.inr second)
    | .inr (.inr third) => .inr third
  backward
    | .inl (.inl first) => .inl first
    | .inl (.inr second) => .inr (.inl second)
    | .inr third => .inr (.inr third)
  backward_forward := by
    intro value
    cases value with
    | inl first => rfl
    | inr rest =>
        cases rest with
        | inl second => rfl
        | inr third => rfl
  forward_backward := by
    intro value
    cases value with
    | inl rest =>
        cases rest with
        | inl first => rfl
        | inr second => rfl
    | inr third => rfl

/-- Canonical rebracketing of the old coordinate and three generated
families.  This is a presentation change, not a new expressive direction. -/
def inputAssociator (Old G₁ G₂ G₃ : Type u) :
    ConstructivePresentation
      (Old ⊕ (G₁ ⊕ (G₂ ⊕ G₃)))
      (Old ⊕ ((G₁ ⊕ G₂) ⊕ G₃)) where
  forward
    | .inl old => .inl old
    | .inr generator =>
        .inr ((generatorAssociator G₁ G₂ G₃).forward generator)
  backward
    | .inl old => .inl old
    | .inr generator =>
        .inr ((generatorAssociator G₁ G₂ G₃).backward generator)
  backward_forward := by
    intro value
    cases value with
    | inl old => rfl
    | inr generator =>
        exact congrArg Sum.inr
          ((generatorAssociator G₁ G₂ G₃).backward_forward generator)
  forward_backward := by
    intro value
    cases value with
    | inl old => rfl
    | inr generator =>
        exact congrArg Sum.inr
          ((generatorAssociator G₁ G₂ G₃).forward_backward generator)

/-- Capacity composition is associative after the canonical constructive
rebracketing of its generated-coordinate carrier.  A nontrivial associator
residual must therefore come from actual coupling or disposition data, not
from `Sum` syntax. -/
theorem compose_embed_associates
    {Old First Second Third G₁ G₂ G₃ : Type u}
    (first : RelativeExpressiveCapacity Old First G₁)
    (second : RelativeExpressiveCapacity First Second G₂)
    (third : RelativeExpressiveCapacity Second Third G₃)
    (input : Old ⊕ (G₁ ⊕ (G₂ ⊕ G₃))) :
    ((first.compose second).compose third).embed
        ((inputAssociator Old G₁ G₂ G₃).forward input) =
      (first.compose (second.compose third)).embed input := by
  cases input with
  | inl old => rfl
  | inr generators =>
      cases generators with
      | inl firstIndex => rfl
      | inr rest =>
          cases rest with
          | inl secondIndex => rfl
          | inr thirdIndex => rfl

end RelativeExpressiveCapacity

/-- Low-universe identity token for the exact failure compiler/event pair
carried by a fixed root projection.  The higher-universe calculus and failure
are indices, not stored data, so the token fits the root projection payload
universe without erasing their identity. -/
inductive SourceNativeRootExpressibilityFailureTokenAt
    {N : WorldRelationNetwork.{u}} {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N} {support : N.Support}
    {obstruction : N.ObstructionAt support}
    (failure : ActualExpressibilityFailure oldTheory obstruction)
    (calculus : U7ObstructionEvolutionCalculus N U7)
    (event : calculus.source.EventAt obstruction
      (U7.generateDemand obstruction)) : Type u
  | canonical

/-- Recognition of an expressibility-failure payload in the projection
inventory of one *already fixed* authoritative root.

No component law, registry, compiler, obstruction, or failure is installed by
this record.  It can only point at an existing root coordinate and prove that
the coordinate's canonical project is the exact occurrence-indexed payload.
This is the source-native boundary-reflection gate for U8. -/
structure SourceNativeRootExpressibilityFailureFaceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (world : SourceNativeAuthoritativeRootClosure N V)
    (visit : SourceNativeTemporalVisitAt world.toLedgerRoot)
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    (failure : ActualExpressibilityFailure oldTheory obstruction) :
    Type (u + 2) where
  /-- Fieldwise provenance gate.  A grounded root occurrence does not confer
  authority on an independently selected theory field: the failed theory is
  exactly the law surface already owned by this source epoch. -/
  lawSurface_eq : oldTheory = world.source.lawSurface
  projection : world.source.projectionLaw.Projection
  active : world.source.projectionLaw.ActiveAt projection
    (world.emitted visit.current)
  classifier_eq :
    world.source.projectionLaw.classify projection
      (world.emitted visit.current) = .inl active
  calculus : U7ObstructionEvolutionCalculus N U7
  u7Event : calculus.source.EventAt obstruction
    (U7.generateDemand obstruction)
  u7Event_eq_emit : u7Event = calculus.source.emit obstruction
  theoryAudit : SourceNativeU7TheoryAuditAt calculus u7Event
  support_eq : world.toRoot.supportAt visit.current = support
  rootEntry : OpenResponsibilityAt N
    (world.toRoot.supportAt visit.current)
  rootEntryAtFailure_eq :
    (ConstructivePresentation.cast
      (F := fun indexedSupport : N.Support =>
        OpenResponsibilityAt N indexedSupport)
      support_eq).forward rootEntry =
        U7ActualSuccessorSource.demandEntry u7Event
  rootDispositionCommutes :
    U7DemandEntryRootDispositionCommutesAt calculus u7Event rootEntry
      ((world.toLedgerRoot.source.ledgerCompiler.compile
        (world.emitted visit.current)).entryDisposition rootEntry)
  project_heq : HEq
    (world.source.projectionLaw.project projection
      (world.emitted visit.current) active)
    (SourceNativeRootExpressibilityFailureTokenAt.canonical
      (failure := failure) (calculus := calculus) (event := u7Event))

namespace SourceNativeRootExpressibilityFailureFaceAt

/-- The failure face is literally the selected coordinate of the canonical
root occurrence.  This theorem is the deletion-test witness: removing the
fixed root projection makes the failure payload unavailable. -/
theorem installedAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {world : SourceNativeAuthoritativeRootClosure N V}
    {visit : SourceNativeTemporalVisitAt world.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      world visit (U7 := U7) failure) :
    let generated := world.toLedgerRoot.generatedAtTemporalVisit visit
    generated = world.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (world.source.projectionLaw.project face.projection
          generated.occurrence face.active)
        (SourceNativeRootExpressibilityFailureTokenAt.canonical
          (failure := failure) (calculus := face.calculus)
          (event := face.u7Event)) := by
  dsimp only
  exact ⟨rfl, face.project_heq⟩

end SourceNativeRootExpressibilityFailureFaceAt

/-- A rooted expressibility failure.  Its public producers consume an exact
failure coordinate already installed in the root source inventory; no revised
carrier or settlement enters this record. -/
structure RootedActualExpressibilityFailureAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    (oldWorld : SourceNativeAuthoritativeRootClosure N OldV)
    (oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot)
    (U7 : U7ProducerCalculus N) {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    (failure : ActualExpressibilityFailure oldTheory obstruction) :
    Type (u + 10) where
  private mk ::
  calculus : U7ObstructionEvolutionCalculus N U7
  u7Event : calculus.source.EventAt obstruction (U7.generateDemand obstruction)
  u7Event_eq_emit : u7Event = calculus.source.emit obstruction
  theoryAudit : SourceNativeU7TheoryAuditAt calculus u7Event
  support_eq : oldWorld.toRoot.supportAt oldVisit.current = support
  rootEntry : OpenResponsibilityAt N
    (oldWorld.toRoot.supportAt oldVisit.current)
  rootEntryAtFailure_eq :
    (ConstructivePresentation.cast
      (F := fun indexedSupport : N.Support =>
        OpenResponsibilityAt N indexedSupport)
      support_eq).forward rootEntry =
        U7ActualSuccessorSource.demandEntry u7Event
  rootDispositionCommutes :
    U7DemandEntryRootDispositionCommutesAt calculus u7Event rootEntry
      ((oldWorld.toLedgerRoot.source.ledgerCompiler.compile
        (oldWorld.emitted oldVisit.current)).entryDisposition rootEntry)
  authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
    oldWorld oldVisit rootEntry
  successor : CausalEntrySuccessorAt oldWorld.toLedgerRoot oldVisit rootEntry

/-- Internal assembler for the source-generated rooted-failure readout.  The
public producer below fixes the theory epoch and failure in the installed
pre-emitter source law before this data can be assembled. -/
private def RootedActualExpressibilityFailureAt.ofRootOccurrence
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (calculus : U7ObstructionEvolutionCalculus N U7)
    (u7Event : calculus.source.EventAt obstruction
      (U7.generateDemand obstruction))
    (u7Event_eq_emit : u7Event = calculus.source.emit obstruction)
    (theoryAudit : SourceNativeU7TheoryAuditAt calculus u7Event)
    (support_eq : oldWorld.toRoot.supportAt oldVisit.current = support)
    (rootEntry : OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt oldVisit.current))
    (rootEntryAtFailure_eq :
      (ConstructivePresentation.cast
        (F := fun indexedSupport : N.Support =>
          OpenResponsibilityAt N indexedSupport)
        support_eq).forward rootEntry =
          U7ActualSuccessorSource.demandEntry u7Event)
    (rootDispositionCommutes :
      U7DemandEntryRootDispositionCommutesAt calculus u7Event rootEntry
        ((oldWorld.toLedgerRoot.source.ledgerCompiler.compile
          (oldWorld.emitted oldVisit.current)).entryDisposition rootEntry))
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      oldWorld oldVisit rootEntry)
    (successor : CausalEntrySuccessorAt oldWorld.toLedgerRoot oldVisit rootEntry) :
    RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure :=
  ⟨calculus, u7Event, u7Event_eq_emit, theoryAudit, support_eq,
    rootEntry, rootEntryAtFailure_eq, rootDispositionCommutes, authority,
    successor⟩

/-- Generate a rooted failure from the exact failure face of the already fixed
root occurrence and the same occurrence's whole-ledger causal authority.

The source face supplies the failure, U7 event, and theory-audit branch;
the temporal root supplies row authority and the canonical successor.  A
domain cannot create either half after observing the other. -/
def RootedActualExpressibilityFailureAt.ofRootFailureFace
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      oldWorld oldVisit (U7 := U7) failure)
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      oldWorld oldVisit face.rootEntry)
    (successor : CausalEntrySuccessorAt oldWorld.toLedgerRoot oldVisit
      face.rootEntry) :
    RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure :=
  RootedActualExpressibilityFailureAt.ofRootOccurrence
    face.calculus face.u7Event face.u7Event_eq_emit face.theoryAudit
    face.support_eq face.rootEntry face.rootEntryAtFailure_eq
    face.rootDispositionCommutes
    authority successor

namespace RootedActualExpressibilityFailureAt

variable
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

/-- Exact original-root occurrence at which the failure face was emitted. -/
def oldBoundaryEvolution
    (_rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      oldWorld.toLedgerRoot oldVisit :=
  oldWorld.toLedgerRoot.generatedAtTemporalVisit oldVisit

/-- Exact successor emitted by the original root at the failure occurrence. -/
def oldSuccessor
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    CausalEntrySuccessorAt oldWorld.toLedgerRoot oldVisit rooted.rootEntry :=
  rooted.successor

def targetEntry
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.successor.next) :=
  rooted.successor.targetEntry

/-- Compatibility name for the old-root target row used by typed U8
realizations. -/
def oldTargetEntry
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.oldSuccessor.next) :=
  rooted.oldSuccessor.targetEntry

def revisionDemand
    (_rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    TheoryRevisionDemandAt U7 failure :=
  theoryRevisionDemandOfFailure U7 failure

end RootedActualExpressibilityFailureAt

/-- The unique completion direction generated by one exact rooted failure.

The constructor is deliberately zero-information.  Its type, however, is
indexed by the complete rooted failure: source occurrence, old obstruction,
U7 demand, causal entry, and whole-ledger successor.  It may therefore serve
as a rank-one marker, but never as the semantic source of the revision. -/
inductive GeneratedDirectionAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : Type u
  | completion

namespace GeneratedDirectionAt

variable
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}

/-- Attaching boundary of the generated direction.  This is a readout of the
rooted index, not a caller-supplied obstruction. -/
def boundary (_direction : GeneratedDirectionAt rooted) :
    N.ObstructionAt support :=
  obstruction

@[simp] theorem completion_boundary_eq :
    boundary (rooted := rooted) .completion = obstruction :=
  rfl

theorem eq_completion (direction : GeneratedDirectionAt rooted) :
    direction = .completion := by
  cases direction
  rfl

end GeneratedDirectionAt

/-- Type-valued equality of two generated directions.  Unlike a bare
`PUnit`, this seal can only inhabit fibres whose source-generated directions
actually coincide. -/
inductive GeneratedDirectionAlignedAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    GeneratedDirectionAt rooted -> GeneratedDirectionAt rooted -> Type u
  | same (direction : GeneratedDirectionAt rooted) :
      GeneratedDirectionAlignedAt rooted direction direction

/-- Exact attaching law of the new direction.  The only constructor states
the core U8 boundary equation: the boundary of the generated coface direction
is the exact old obstruction. -/
inductive GeneratedDirectionBoundaryAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    (direction : GeneratedDirectionAt rooted) ->
      N.ObstructionAt support -> Type u
  | exact : GeneratedDirectionBoundaryAt rooted .completion obstruction

/-- Non-bare impossibility generated from one exact rooted obstruction.

The private constructor prevents a domain from pairing a valid residual with
a sibling direction.  Actual consumption by the revised first write is added
only when a typed coface realization exists. -/
structure SourceGeneratedAttachingDirectionAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : Type u where
  private mk ::
  direction : GeneratedDirectionAt rooted
  boundary : GeneratedDirectionBoundaryAt rooted direction obstruction

/-- The exact rooted failure generates its attaching direction without a
semantic payload parameter. -/
def sourceGeneratedAttachingDirection
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) :
    SourceGeneratedAttachingDirectionAt rooted :=
  ⟨.completion, .exact⟩

/-- Local live-ledger carrier of the obstruction-generated minimal coface. -/
inductive MinimalCofaceCoordinateAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : Type u
  | inherited (entry : OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.successor.next))
  | obstruction (direction : GeneratedDirectionAt rooted)

namespace MinimalCofaceCoordinateAt

/-- Remaining budget carried by the generated coface.  Inherited debt keeps its
exact source budget; the new obstruction direction receives no free
maintenance credit. -/
def progressBudget
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure} : MinimalCofaceCoordinateAt rooted -> Nat
  | .inherited entry => entry.progressBudget
  | .obstruction _ => 0

end MinimalCofaceCoordinateAt

/-- Canonical generation token.  All data are read from the rooted failure. -/
inductive GeneratedMinimalCofaceAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : Type u
  | canonical

def root_obstruction_generates_minimal_coface
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : GeneratedMinimalCofaceAt rooted :=
  .canonical

namespace GeneratedMinimalCofaceAt

variable
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}

def oldLedgerRetract
    (_generated : GeneratedMinimalCofaceAt rooted) :
    ConstructiveRetract
      (OpenResponsibilityAt N
        (oldWorld.toRoot.supportAt rooted.successor.next))
      (MinimalCofaceCoordinateAt rooted) where
  forward := MinimalCofaceCoordinateAt.inherited
  backward
    | .inherited entry => entry
    | .obstruction _ => rooted.targetEntry
  backward_forward := fun _ => rfl

def obstructionCoordinate
    (_generated : GeneratedMinimalCofaceAt rooted) :
    MinimalCofaceCoordinateAt rooted :=
  .obstruction .completion

/-- Exact attachment generated together with the minimal coface. -/
def attachingDirection
    (_generated : GeneratedMinimalCofaceAt rooted) :
    SourceGeneratedAttachingDirectionAt rooted :=
  sourceGeneratedAttachingDirection rooted

/-- The attachment has no semantic choice beyond its rooted residual index. -/
theorem attachingDirection_unique
    (generated : GeneratedMinimalCofaceAt rooted)
    (attachment : SourceGeneratedAttachingDirectionAt rooted) :
    attachment = generated.attachingDirection := by
  rcases attachment with ⟨direction, boundary⟩
  cases boundary
  rfl

theorem obstructionCoordinate_hasNoOldPreimage
    (generated : GeneratedMinimalCofaceAt rooted) :
    IsEmpty (Sigma fun oldEntry :
        OpenResponsibilityAt N
          (oldWorld.toRoot.supportAt rooted.successor.next) =>
      PLift (generated.oldLedgerRetract.forward oldEntry =
        generated.obstructionCoordinate)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldEntry, equality⟩
    cases equality.down⟩

/-- The generated live-row coordinate has one source-generated expressive
direction over the complete old target ledger. -/
def ledgerRelativeCapacity
    (generated : GeneratedMinimalCofaceAt rooted) :
    RelativeExpressiveCapacity
      (OpenResponsibilityAt N
        (oldWorld.toRoot.supportAt rooted.successor.next))
      (MinimalCofaceCoordinateAt rooted) (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique generated.oldLedgerRetract .completion
    GeneratedDirectionAt.eq_completion
    generated.obstructionCoordinate
    generated.obstructionCoordinate_hasNoOldPreimage

def firstWriteOccurrence
    (_generated : GeneratedMinimalCofaceAt rooted) :=
  oldWorld.emitted rooted.successor.next

def firstWriteEntryEvolution
    (_generated : GeneratedMinimalCofaceAt rooted) :=
  rooted.successor.entryDestination

def generatedDemand
    (_generated : GeneratedMinimalCofaceAt rooted) :
    TheoryRevisionDemandAt U7 failure :=
  rooted.revisionDemand

private def targetSupport
    (_generated : GeneratedMinimalCofaceAt rooted) : N.Support :=
  oldWorld.toRoot.supportAt rooted.successor.next

/-- Old live rows survive at both the embedded old face and the newly opened
coface.  Only the coface also admits the generated obstruction row. -/
def CofaceOpenAt
    (generated : GeneratedMinimalCofaceAt rooted) :
    (N.Support ⊕ GeneratedDirectionAt rooted) ->
      (N.Responsibility ⊕ GeneratedDirectionAt rooted) -> Type u
  | .inl oldSupport, .inl oldResponsibility =>
      N.OpenAt oldSupport oldResponsibility
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl oldResponsibility =>
      N.OpenAt (targetSupport generated) oldResponsibility
  | .inr supportDirection, .inr responsibilityDirection =>
      GeneratedDirectionAlignedAt rooted supportDirection
        responsibilityDirection

/-- Old world facts survive on the embedded face.  At the coface the old
target facts remain available and the obstruction obtains one new claim. -/
def CofaceHoldsAt
    (generated : GeneratedMinimalCofaceAt rooted) :
    (N.Support ⊕ GeneratedDirectionAt rooted) ->
      (N.Claim ⊕ GeneratedDirectionAt rooted) -> Type u
  | .inl oldSupport, .inl oldClaim => N.HoldsAt oldSupport oldClaim
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl oldClaim => N.HoldsAt (targetSupport generated) oldClaim
  | .inr supportDirection, .inr claimDirection =>
      GeneratedDirectionAlignedAt rooted supportDirection claimDirection

/-- The only new semantic-change constructor is generated at the coface from
the exact old obstruction claim.  Using an indexed constructor avoids
turning propositional equality into authority. -/
inductive CofaceSemanticChangeAt
    (generated : GeneratedMinimalCofaceAt rooted) :
    (N.Support ⊕ GeneratedDirectionAt rooted) ->
      (N.Claim ⊕ GeneratedDirectionAt rooted) ->
        (N.Claim ⊕ GeneratedDirectionAt rooted) -> Type u
  | inherited {oldSupport oldValue revisedValue}
      (change : N.SemanticChangeAt oldSupport oldValue revisedValue) :
      CofaceSemanticChangeAt generated (.inl oldSupport)
        (.inl oldValue) (.inl revisedValue)
  | targetInherited {oldValue revisedValue}
      (change : N.SemanticChangeAt
        (targetSupport generated) oldValue revisedValue) :
      CofaceSemanticChangeAt generated (.inr .completion)
        (.inl oldValue) (.inl revisedValue)
  | obstructionRevealed :
      CofaceSemanticChangeAt generated (.inr .completion)
        (.inl (N.obstructionClaim obstruction)) (.inr .completion)

/-- Failure-indexed presentation of an old target-support disposition on the
new coface support.

The payload remains the exact old receipt, but it is no longer definitionally
the receipt of the new support.  Reusing it therefore requires an explicit
registration under this generated coface; a receipt from the old support or a
sibling revision cannot silently acquire the new support identity.  This is a
presentation seal, not a settlement producer. -/
structure CofaceTargetDispositionAt
    (generated : GeneratedMinimalCofaceAt rooted)
    (kind : WorldDispositionKind) : Type u where
  private mk ::
  targetReceipt : N.DispositionAt (targetSupport generated) kind

namespace CofaceTargetDispositionAt

/-- Register one old target-support receipt in the exact generated coface. -/
def ofTarget
    {generated : GeneratedMinimalCofaceAt rooted}
    {kind : WorldDispositionKind}
    (receipt : N.DispositionAt (targetSupport generated) kind) :
    CofaceTargetDispositionAt generated kind :=
  ⟨receipt⟩

end CofaceTargetDispositionAt

/-- Canonical whole-network minimal coface generated by the rooted failure.
The new support, incidence, responsibility, and claim are sums with one
source-generated coordinate; no revised root or settlement is stored here. -/
def worldNetwork
    (generated : GeneratedMinimalCofaceAt rooted) :
    WorldRelationNetwork.{u} where
  Support := N.Support ⊕ GeneratedDirectionAt rooted
  Anchor := N.Anchor
  Incidence := N.Incidence ⊕ GeneratedDirectionAt rooted
  Lineage := N.Lineage
  Responsibility := N.Responsibility ⊕ GeneratedDirectionAt rooted
  Claim := N.Claim ⊕ GeneratedDirectionAt rooted
  anchorAt
    | .inl oldSupport => N.anchorAt oldSupport
    | .inr _ => N.anchorAt (targetSupport generated)
  incidenceAt
    | .inl oldSupport => .inl (N.incidenceAt oldSupport)
    | .inr direction => .inr direction
  lineageAt
    | .inl oldSupport => N.lineageAt oldSupport
    | .inr _ => N.lineageAt (targetSupport generated)
  OpenAt := CofaceOpenAt generated
  openClaimAt := by
    intro newSupport newResponsibility isOpen
    cases newSupport with
    | inl oldSupport =>
        cases newResponsibility with
        | inl oldResponsibility =>
            exact Sum.inl (N.openClaimAt isOpen)
        | inr _ => exact PEmpty.elim isOpen
    | inr supportDirection =>
        cases newResponsibility with
        | inl oldResponsibility =>
            exact Sum.inl (N.openClaimAt isOpen)
        | inr responsibilityDirection =>
            exact Sum.inr responsibilityDirection
  openProgressBudgetAt := by
    intro newSupport newResponsibility isOpen
    cases newSupport with
    | inl oldSupport =>
        cases newResponsibility with
        | inl _ => exact N.openProgressBudgetAt isOpen
        | inr _ => exact PEmpty.elim isOpen
    | inr _ =>
        cases newResponsibility with
        | inl _ => exact N.openProgressBudgetAt isOpen
        | inr _ => exact 0
  HoldsAt := CofaceHoldsAt generated
  ObstructionAt := fun _ => Sigma fun oldSupport : N.Support =>
    N.ObstructionAt oldSupport
  obstructionClaim := fun indexedObstruction =>
    Sum.inl (N.obstructionClaim indexedObstruction.2)
  SemanticChangeAt := CofaceSemanticChangeAt generated
  DispositionAt := fun newSupport kind =>
    match newSupport with
    | .inl oldSupport => N.DispositionAt oldSupport kind
    | .inr _ => CofaceTargetDispositionAt generated kind

/-- Constructive whole-network inclusion and retraction.  All old identities,
facts, dispositions, and live-ledger fibres commute on the embedded face. -/
def translation
    (generated : GeneratedMinimalCofaceAt rooted) :
    TypedSemanticWorldNetworkTranslationAt N generated.worldNetwork where
  support :=
    { forward := Sum.inl
      backward
        | .inl oldSupport => oldSupport
        | .inr _ => targetSupport generated
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward
        | .inl oldIncidence => oldIncidence
        | .inr _ => N.incidenceAt (targetSupport generated)
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := Sum.inl
      backward
        | .inl oldResponsibility => oldResponsibility
        | .inr _ => rooted.targetEntry.1
      backward_forward := fun _ => rfl }
  claim :=
    { forward := Sum.inl
      backward
        | .inl oldClaim => oldClaim
        | .inr _ => N.obstructionClaim obstruction
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := fun oldEntry => ⟨Sum.inl oldEntry.1, oldEntry.2⟩
      backward := fun newEntry =>
        match newEntry with
        | ⟨.inl oldResponsibility, isOpen⟩ =>
            ⟨oldResponsibility, isOpen⟩
        | ⟨.inr _, impossible⟩ => PEmpty.elim impossible
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ receipt => receipt

/-- Restricting the generated coface to any old support recovers the complete
old open ledger.  This is stronger than the global retract: no generated row
exists on an old support. -/
def oldFaceOpenLedgerPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldSupport : N.Support) :
    ConstructivePresentation
      (OpenResponsibilityAt N oldSupport)
      (OpenResponsibilityAt generated.worldNetwork (.inl oldSupport)) where
  forward := fun oldEntry => ⟨.inl oldEntry.1, oldEntry.2⟩
  backward := fun newEntry =>
    match newEntry with
    | ⟨.inl oldResponsibility, isOpen⟩ => ⟨oldResponsibility, isOpen⟩
    | ⟨.inr _, impossible⟩ => PEmpty.elim impossible
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, isOpen⟩
    cases responsibility with
    | inl _ => rfl
    | inr _ => exact PEmpty.elim isOpen

/-- Old facts are definitionally unchanged on every embedded support. -/
def oldFaceHoldsPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldSupport : N.Support) (oldClaim : N.Claim) :
    ConstructivePresentation
      (N.HoldsAt oldSupport oldClaim)
      (generated.worldNetwork.HoldsAt (.inl oldSupport) (.inl oldClaim)) :=
  ConstructivePresentation.refl _

/-- Old dispositions are definitionally unchanged on every embedded support. -/
def oldFaceDispositionPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldSupport : N.Support) (kind : WorldDispositionKind) :
    ConstructivePresentation
      (N.DispositionAt oldSupport kind)
      (generated.worldNetwork.DispositionAt (.inl oldSupport) kind) :=
  ConstructivePresentation.refl _

/-- The newly opened support is not an old support in disguise. -/
def cofaceSupport
    (_generated : GeneratedMinimalCofaceAt rooted) :
    N.Support ⊕ GeneratedDirectionAt rooted :=
  Sum.inr .completion

/-- At the attached coface, every old target-responsibility fibre is retained
exactly; only the generated obstruction row enlarges the whole ledger. -/
def cofaceTargetOpenPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldResponsibility : N.Responsibility) :
    ConstructivePresentation
      (N.OpenAt (targetSupport generated) oldResponsibility)
      (generated.worldNetwork.OpenAt generated.cofaceSupport
        (.inl oldResponsibility)) :=
  ConstructivePresentation.refl _

/-- Old target facts remain exact on the attached coface. -/
def cofaceTargetHoldsPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldClaim : N.Claim) :
    ConstructivePresentation
      (N.HoldsAt (targetSupport generated) oldClaim)
      (generated.worldNetwork.HoldsAt generated.cofaceSupport
        (.inl oldClaim)) :=
  ConstructivePresentation.refl _

/-- Old target dispositions have a two-sided, failure-indexed presentation on
the attached coface.  They are faithfully retained but are no longer
definitionally reusable as receipts of the new support. -/
def cofaceTargetDispositionPresentation
    (generated : GeneratedMinimalCofaceAt rooted)
    (kind : WorldDispositionKind) :
    ConstructivePresentation
      (N.DispositionAt (targetSupport generated) kind)
      (generated.worldNetwork.DispositionAt generated.cofaceSupport kind) where
  forward := CofaceTargetDispositionAt.ofTarget
  backward := CofaceTargetDispositionAt.targetReceipt
  backward_forward := fun _ => rfl
  forward_backward := fun receipt => by cases receipt; rfl

/-- A generated responsibility coordinate cannot leak onto an old support. -/
theorem no_newResponsibility_on_oldFace
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldSupport : N.Support) :
    IsEmpty (generated.worldNetwork.OpenAt
      (.inl oldSupport) (.inr .completion)) :=
  ⟨fun impossible => nomatch impossible⟩

/-- A generated claim cannot leak onto an old support. -/
theorem no_newClaim_on_oldFace
    (generated : GeneratedMinimalCofaceAt rooted)
    (oldSupport : N.Support) :
    IsEmpty (generated.worldNetwork.HoldsAt
      (.inl oldSupport) (.inr .completion)) :=
  ⟨fun impossible => nomatch impossible⟩

theorem cofaceSupport_hasNoOldPreimage
    (generated : GeneratedMinimalCofaceAt rooted) :
    IsEmpty (Sigma fun oldSupport : N.Support =>
      PLift (generated.translation.support.forward oldSupport =
        generated.cofaceSupport)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldSupport, equality⟩
    cases equality.down⟩

/-- The coface contains the full old target ledger plus one generated row. -/
def cofaceLedgerRetract
    (generated : GeneratedMinimalCofaceAt rooted) :
    ConstructiveRetract
      (OpenResponsibilityAt N (targetSupport generated))
      (OpenResponsibilityAt generated.worldNetwork generated.cofaceSupport) where
  forward := fun oldEntry => ⟨Sum.inl oldEntry.1, oldEntry.2⟩
  backward := fun newEntry =>
    match newEntry with
    | ⟨.inl oldResponsibility, isOpen⟩ => ⟨oldResponsibility, isOpen⟩
    | ⟨.inr _, _⟩ => rooted.targetEntry
  backward_forward := fun _ => rfl

def obstructionEntry
    (generated : GeneratedMinimalCofaceAt rooted) :
    OpenResponsibilityAt generated.worldNetwork generated.cofaceSupport :=
  ⟨Sum.inr .completion, .same .completion⟩

theorem obstructionEntry_hasNoOldPreimage
    (generated : GeneratedMinimalCofaceAt rooted) :
    IsEmpty (Sigma fun oldEntry :
        OpenResponsibilityAt N (targetSupport generated) =>
      PLift (generated.cofaceLedgerRetract.forward oldEntry =
        generated.obstructionEntry)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldEntry, equality⟩
    cases equality.down⟩

def obstructionIncidence
    (_generated : GeneratedMinimalCofaceAt rooted) :
    N.Incidence ⊕ GeneratedDirectionAt rooted :=
  Sum.inr .completion

theorem obstructionIncidence_hasNoOldPreimage
    (generated : GeneratedMinimalCofaceAt rooted) :
    IsEmpty (Sigma fun oldIncidence : N.Incidence =>
      PLift (generated.translation.incidence.forward oldIncidence =
        generated.obstructionIncidence)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldIncidence, equality⟩
    cases equality.down⟩

/-- The generated incidence is one source-generated expressive direction over
the old incidence carrier. -/
def incidenceRelativeCapacity
    (generated : GeneratedMinimalCofaceAt rooted) :
    RelativeExpressiveCapacity N.Incidence generated.worldNetwork.Incidence
      (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique generated.translation.incidence .completion
    GeneratedDirectionAt.eq_completion
    generated.obstructionIncidence
    generated.obstructionIncidence_hasNoOldPreimage

def obstructionClaim
    (_generated : GeneratedMinimalCofaceAt rooted) :
    N.Claim ⊕ GeneratedDirectionAt rooted :=
  Sum.inr .completion

/-- The generated live row and the generated expressive claim are one ledger
incidence.  The equality is definitional because the minimal coface compiler
creates both coordinates from the same rooted obstruction. -/
theorem obstructionEntry_claim_eq_obstructionClaim
    (generated : GeneratedMinimalCofaceAt rooted) :
    generated.obstructionEntry.claim = generated.obstructionClaim :=
  rfl

theorem obstructionClaim_hasNoOldPreimage
    (generated : GeneratedMinimalCofaceAt rooted) :
    IsEmpty (Sigma fun oldClaim : N.Claim =>
      PLift (generated.translation.claim.forward oldClaim =
        generated.obstructionClaim)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldClaim, equality⟩
    cases equality.down⟩

/-- The generated claim is one source-generated expressive direction over the
old claim carrier. -/
def claimRelativeCapacity
    (generated : GeneratedMinimalCofaceAt rooted) :
    RelativeExpressiveCapacity N.Claim generated.worldNetwork.Claim
      (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique generated.translation.claim .completion
    GeneratedDirectionAt.eq_completion
    generated.obstructionClaim
    generated.obstructionClaim_hasNoOldPreimage

def obstructionClaimHolds
    (generated : GeneratedMinimalCofaceAt rooted) :
    generated.worldNetwork.HoldsAt generated.cofaceSupport
      generated.obstructionClaim :=
  .same .completion

def obstructionSemanticChange
    (generated : GeneratedMinimalCofaceAt rooted) :
    generated.worldNetwork.SemanticChangeAt generated.cofaceSupport
      (generated.translation.claim.forward (N.obstructionClaim obstruction))
      generated.obstructionClaim :=
  CofaceSemanticChangeAt.obstructionRevealed

/-- At the generated support and claim indices there is exactly one semantic
change: the attaching direction whose boundary is the exact old obstruction.
The zero-information constructor cannot be replayed for a sibling residual. -/
theorem obstructionSemanticChange_unique
    (generated : GeneratedMinimalCofaceAt rooted)
    (change : generated.worldNetwork.SemanticChangeAt
      generated.cofaceSupport
      (generated.translation.claim.forward (N.obstructionClaim obstruction))
      generated.obstructionClaim) :
    change = generated.obstructionSemanticChange := by
  cases change
  rfl

/-- Every old theorem survives as the same world fact on the embedded face.
This is theorem preservation, not a claim that the obstruction is settled. -/
def oldTheoremSurvival
    (generated : GeneratedMinimalCofaceAt rooted)
    {oldSupport : N.Support}
    (expression : oldTheory.ExpressionAt oldSupport) :
    oldTheory.TheoremAt expression ->
      generated.worldNetwork.HoldsAt
        (generated.translation.support.forward oldSupport)
        (generated.translation.claim.forward (oldTheory.denotes expression)) :=
  fun proof => generated.translation.oldHoldsSurvives oldSupport _ <|
    (oldTheory.theoremPresentation expression).forward proof

/-- The exact first root write lands on the old target that is the restriction
of the generated coface; no sibling target is introduced. -/
theorem firstWrite_targetSupport_is_cofaceRestriction
    (generated : GeneratedMinimalCofaceAt rooted) :
    generated.translation.support.backward generated.cofaceSupport =
      oldWorld.toRoot.supportAt rooted.successor.next :=
  rfl

end GeneratedMinimalCofaceAt

/-- Any admissible coface preserves the old live ledger, incidence, and claim
carriers by retracts and contains one genuinely new generator in each. -/
structure AdmissibleCofaceRevisionAt
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure) : Type (u + 1) where
  Carrier : Type u
  oldLedger : ConstructiveRetract
    (OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.successor.next)) Carrier
  obstructionCoordinate : Carrier
  obstructionCoordinate_hasNoOldPreimage : IsEmpty
    (Sigma fun oldEntry : OpenResponsibilityAt N
        (oldWorld.toRoot.supportAt rooted.successor.next) =>
      PLift (oldLedger.forward oldEntry = obstructionCoordinate))
  progressBudgetAt : Carrier -> Nat
  inheritedProgressBudget_not_refilled : (oldEntry : OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.successor.next)) ->
    progressBudgetAt (oldLedger.forward oldEntry) ≤ oldEntry.progressBudget
  obstructionProgressBudget_eq_zero :
    progressBudgetAt obstructionCoordinate = 0
  IncidenceCarrier : Type u
  oldIncidenceEmbedding : ConstructiveRetract N.Incidence IncidenceCarrier
  obstructionIncidence : IncidenceCarrier
  obstructionIncidence_hasNoOldPreimage : IsEmpty
    (Sigma fun inheritedIncidence : N.Incidence =>
      PLift (oldIncidenceEmbedding.forward inheritedIncidence =
        obstructionIncidence))
  ClaimCarrier : Type u
  oldClaimEmbedding : ConstructiveRetract N.Claim ClaimCarrier
  obstructionClaim : ClaimCarrier
  obstructionClaim_hasNoOldPreimage : IsEmpty
    (Sigma fun inheritedClaim : N.Claim =>
      PLift (oldClaimEmbedding.forward inheritedClaim = obstructionClaim))

namespace AdmissibleCofaceRevisionAt

variable
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}

/-- Every admissible revision must carry the generated live-row direction;
its carrier may contain more structure, but cannot erase this relative rank. -/
def ledgerRelativeCapacity
    (candidate : AdmissibleCofaceRevisionAt rooted) :
    RelativeExpressiveCapacity
      (OpenResponsibilityAt N
        (oldWorld.toRoot.supportAt rooted.successor.next))
      candidate.Carrier (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique candidate.oldLedger .completion
    GeneratedDirectionAt.eq_completion
    candidate.obstructionCoordinate
    candidate.obstructionCoordinate_hasNoOldPreimage

/-- Every admissible revision must carry the generated incidence direction. -/
def incidenceRelativeCapacity
    (candidate : AdmissibleCofaceRevisionAt rooted) :
    RelativeExpressiveCapacity N.Incidence candidate.IncidenceCarrier
      (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique candidate.oldIncidenceEmbedding .completion
    GeneratedDirectionAt.eq_completion
    candidate.obstructionIncidence
    candidate.obstructionIncidence_hasNoOldPreimage

/-- Every admissible revision must carry the generated claim direction. -/
def claimRelativeCapacity
    (candidate : AdmissibleCofaceRevisionAt rooted) :
    RelativeExpressiveCapacity N.Claim candidate.ClaimCarrier
      (GeneratedDirectionAt rooted) :=
  relativeExpressiveCapacityUnique candidate.oldClaimEmbedding .completion
    GeneratedDirectionAt.eq_completion
    candidate.obstructionClaim
    candidate.obstructionClaim_hasNoOldPreimage

end AdmissibleCofaceRevisionAt

/-- The generated whole-network coface is itself an admissible realization of
the generated local carrier. -/
def GeneratedMinimalCofaceAt.toAdmissibleWorldCoface
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedMinimalCofaceAt rooted) :
    AdmissibleCofaceRevisionAt rooted where
  Carrier := OpenResponsibilityAt generated.worldNetwork generated.cofaceSupport
  oldLedger := generated.cofaceLedgerRetract
  obstructionCoordinate := generated.obstructionEntry
  obstructionCoordinate_hasNoOldPreimage :=
    generated.obstructionEntry_hasNoOldPreimage
  progressBudgetAt := fun entry => entry.progressBudget
  inheritedProgressBudget_not_refilled := fun _ => Nat.le_refl _
  obstructionProgressBudget_eq_zero := rfl
  IncidenceCarrier := generated.worldNetwork.Incidence
  oldIncidenceEmbedding := generated.translation.incidence
  obstructionIncidence := generated.obstructionIncidence
  obstructionIncidence_hasNoOldPreimage :=
    generated.obstructionIncidence_hasNoOldPreimage
  ClaimCarrier := generated.worldNetwork.Claim
  oldClaimEmbedding := generated.translation.claim
  obstructionClaim := generated.obstructionClaim
  obstructionClaim_hasNoOldPreimage :=
    generated.obstructionClaim_hasNoOldPreimage

/-- Unique structure-preserving factorization token of the generated coface.

The token stores no maps or proof fields.  Ledger, incidence and claim maps
are definitionally reconstructed below from the old-face retracts and the
single obstruction coordinate.  Consequently a caller cannot install a
sibling factorization and the full universal-property uniqueness theorem is
constructive. -/
inductive FaithfulCofaceMorphism
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedMinimalCofaceAt rooted)
    (candidate : AdmissibleCofaceRevisionAt rooted) : Type (u + 1)
  | canonical : FaithfulCofaceMorphism generated candidate

namespace FaithfulCofaceMorphism

variable
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    {generated : GeneratedMinimalCofaceAt rooted}
    {candidate : AdmissibleCofaceRevisionAt rooted}

/-- Canonical ledger-coordinate map of the initial factorization. -/
def map
    (_morphism : FaithfulCofaceMorphism generated candidate) :
    MinimalCofaceCoordinateAt rooted -> candidate.Carrier
  | .inherited oldEntry => candidate.oldLedger.forward oldEntry
  | .obstruction _ => candidate.obstructionCoordinate

@[simp] theorem inherited_commutes
    (morphism : FaithfulCofaceMorphism generated candidate)
    (oldEntry : OpenResponsibilityAt N
      (oldWorld.toRoot.supportAt rooted.successor.next)) :
    morphism.map (generated.oldLedgerRetract.forward oldEntry) =
      candidate.oldLedger.forward oldEntry :=
  rfl

@[simp] theorem obstruction_commutes
    (morphism : FaithfulCofaceMorphism generated candidate) :
    morphism.map generated.obstructionCoordinate =
      candidate.obstructionCoordinate :=
  rfl

theorem injective
    (morphism : FaithfulCofaceMorphism generated candidate) :
    Function.Injective morphism.map := by
  cases morphism
  intro left right equality
  cases left with
  | inherited leftEntry =>
      cases right with
      | inherited rightEntry =>
          change candidate.oldLedger.forward leftEntry =
            candidate.oldLedger.forward rightEntry at equality
          have oldEquality := congrArg candidate.oldLedger.backward equality
          rw [candidate.oldLedger.backward_forward,
            candidate.oldLedger.backward_forward] at oldEquality
          cases oldEquality
          rfl
      | obstruction _ =>
          change candidate.oldLedger.forward leftEntry =
            candidate.obstructionCoordinate at equality
          exact False.elim <|
            candidate.obstructionCoordinate_hasNoOldPreimage.false
              ⟨leftEntry, PLift.up equality⟩
  | obstruction leftDirection =>
      cases right with
      | inherited rightEntry =>
          change candidate.obstructionCoordinate =
            candidate.oldLedger.forward rightEntry at equality
          exact False.elim <|
            candidate.obstructionCoordinate_hasNoOldPreimage.false
              ⟨rightEntry, PLift.up equality.symm⟩
      | obstruction rightDirection =>
          cases leftDirection
          cases rightDirection
          rfl

theorem progressBudget_not_refilled
    (morphism : FaithfulCofaceMorphism generated candidate)
    (coordinate : MinimalCofaceCoordinateAt rooted) :
    candidate.progressBudgetAt (morphism.map coordinate) ≤
      coordinate.progressBudget := by
  cases morphism
  cases coordinate with
  | inherited oldEntry =>
      exact candidate.inheritedProgressBudget_not_refilled oldEntry
  | obstruction direction =>
      cases direction
      change candidate.progressBudgetAt candidate.obstructionCoordinate ≤ 0
      exact candidate.obstructionProgressBudget_eq_zero.le

/-- Canonical incidence map of the same factorization token. -/
def incidenceMap
    (_morphism : FaithfulCofaceMorphism generated candidate) :
    generated.worldNetwork.Incidence -> candidate.IncidenceCarrier
  | .inl oldIncidence =>
      candidate.oldIncidenceEmbedding.forward oldIncidence
  | .inr _ => candidate.obstructionIncidence

@[simp] theorem incidence_inherited_commutes
    (morphism : FaithfulCofaceMorphism generated candidate)
    (oldIncidence : N.Incidence) :
    morphism.incidenceMap
        (generated.translation.incidence.forward oldIncidence) =
      candidate.oldIncidenceEmbedding.forward oldIncidence :=
  rfl

@[simp] theorem incidence_obstruction_commutes
    (morphism : FaithfulCofaceMorphism generated candidate) :
    morphism.incidenceMap generated.obstructionIncidence =
      candidate.obstructionIncidence :=
  rfl

theorem incidence_injective
    (morphism : FaithfulCofaceMorphism generated candidate) :
    Function.Injective morphism.incidenceMap := by
  cases morphism
  intro left right equality
  cases left with
  | inl leftIncidence =>
      cases right with
      | inl rightIncidence =>
          change candidate.oldIncidenceEmbedding.forward leftIncidence =
            candidate.oldIncidenceEmbedding.forward rightIncidence at equality
          have oldEquality :=
            congrArg candidate.oldIncidenceEmbedding.backward equality
          rw [candidate.oldIncidenceEmbedding.backward_forward,
            candidate.oldIncidenceEmbedding.backward_forward] at oldEquality
          cases oldEquality
          rfl
      | inr _ =>
          change candidate.oldIncidenceEmbedding.forward leftIncidence =
            candidate.obstructionIncidence at equality
          exact False.elim <|
            candidate.obstructionIncidence_hasNoOldPreimage.false
              ⟨leftIncidence, PLift.up equality⟩
  | inr leftDirection =>
      cases leftDirection
      cases right with
      | inl rightIncidence =>
          change candidate.obstructionIncidence =
            candidate.oldIncidenceEmbedding.forward rightIncidence at equality
          exact False.elim <|
            candidate.obstructionIncidence_hasNoOldPreimage.false
              ⟨rightIncidence, PLift.up equality.symm⟩
      | inr rightDirection => cases rightDirection; rfl

/-- Canonical claim map of the same factorization token. -/
def claimMap
    (_morphism : FaithfulCofaceMorphism generated candidate) :
    generated.worldNetwork.Claim -> candidate.ClaimCarrier
  | .inl oldClaim => candidate.oldClaimEmbedding.forward oldClaim
  | .inr _ => candidate.obstructionClaim

@[simp] theorem claim_inherited_commutes
    (morphism : FaithfulCofaceMorphism generated candidate)
    (oldClaim : N.Claim) :
    morphism.claimMap (generated.translation.claim.forward oldClaim) =
      candidate.oldClaimEmbedding.forward oldClaim :=
  rfl

@[simp] theorem claim_obstruction_commutes
    (morphism : FaithfulCofaceMorphism generated candidate) :
    morphism.claimMap generated.obstructionClaim =
      candidate.obstructionClaim :=
  rfl

theorem claim_injective
    (morphism : FaithfulCofaceMorphism generated candidate) :
    Function.Injective morphism.claimMap := by
  cases morphism
  intro left right equality
  cases left with
  | inl leftClaim =>
      cases right with
      | inl rightClaim =>
          change candidate.oldClaimEmbedding.forward leftClaim =
            candidate.oldClaimEmbedding.forward rightClaim at equality
          have oldEquality :=
            congrArg candidate.oldClaimEmbedding.backward equality
          rw [candidate.oldClaimEmbedding.backward_forward,
            candidate.oldClaimEmbedding.backward_forward] at oldEquality
          cases oldEquality
          rfl
      | inr _ =>
          change candidate.oldClaimEmbedding.forward leftClaim =
            candidate.obstructionClaim at equality
          exact False.elim <|
            candidate.obstructionClaim_hasNoOldPreimage.false
              ⟨leftClaim, PLift.up equality⟩
  | inr leftDirection =>
      cases leftDirection
      cases right with
      | inl rightClaim =>
          change candidate.obstructionClaim =
            candidate.oldClaimEmbedding.forward rightClaim at equality
          exact False.elim <|
            candidate.obstructionClaim_hasNoOldPreimage.false
              ⟨rightClaim, PLift.up equality.symm⟩
      | inr rightDirection => cases rightDirection; rfl

end FaithfulCofaceMorphism

def minimal_coface_initial
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedMinimalCofaceAt rooted)
    (candidate : AdmissibleCofaceRevisionAt rooted) :
    FaithfulCofaceMorphism generated candidate :=
  .canonical

/-- Canonical injection of the free coordinate carrier into its generated
whole-network coface realization. -/
def GeneratedMinimalCofaceAt.worldCofaceMorphism
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedMinimalCofaceAt rooted) :
    FaithfulCofaceMorphism generated generated.toAdmissibleWorldCoface :=
  minimal_coface_initial generated generated.toAdmissibleWorldCoface

theorem minimal_coface_factorization_unique
    {N : WorldRelationNetwork.{u}} {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    {generated : GeneratedMinimalCofaceAt rooted}
    {candidate : AdmissibleCofaceRevisionAt rooted}
    (morphism : FaithfulCofaceMorphism generated candidate) :
    morphism = minimal_coface_initial generated candidate := by
  cases morphism
  rfl

end ObstructionGeneratedMinimalCoface
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
