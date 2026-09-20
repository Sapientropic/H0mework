import H0mework.Foundation.Source.ConstructivePresentation

/-!
# Constructive living-law relation network and obstruction calculus

This is the U5–U7 core.  It knows only actual world support, local occurrence
presentations, responsibility accounts, world dispositions, and obstruction
demands.  It does not import `Field`, `LinearMap`, `Quiver.Path`, quotient
transport, or the effective-residual implementation.

* `WorldRelationNetwork` is the common actual support/account ledger.
* `OccurrenceChart` and `SharedOccurrenceSpan` present heterogeneous local
  domains without identifying their carrier types.
* `U7ProducerCalculus` turns an actual network obstruction into the exact next
  producer demand; `LivingLawObstructionLineageEvolutionKernel` consumes that
  demand in the source-owned successor calculus.

Mathlib residual/path machinery is attached only by
`LivingLawRelationNetworkMathlibAdapter`.  Reflexive U8 theory evolution lives
in `LivingLawTheoryEvolutionKernel`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution

universe u

/-- Support-local settlement, transfer, or law-surface extension after a
domain's ordinary write fibre has been exhausted.  Settlement closes the
indexed responsibility at this support; it does not assert that the whole
root world has no further occurrence. -/
inductive WorldDispositionKind
  | supportSettlement
  | transfer
  | lawSurfaceExtension

/-- Common world account carried by one actual support occurrence.  Domain
charts may use different carriers and local account presentations, but their
occurrences can only be identified through this shared ledger. -/
structure WorldRelationNetwork where
  Support : Type u
  Anchor : Type u
  Incidence : Type u
  Lineage : Type u
  Responsibility : Type u
  Claim : Type u
  anchorAt : Support → Anchor
  incidenceAt : Support → Incidence
  lineageAt : Support → Lineage
  OpenAt : Support → Responsibility → Type u
  /-- Claim carried by one exact open-incidence witness.  A claim is not a
  sibling receipt that a later revision may attach to the same support: it is
  a source-native readout of the live ledger row itself. -/
  openClaimAt : {support : Support} → {responsibility : Responsibility} →
    OpenAt support responsibility → Claim
  /-- Remaining maintenance/progress capacity of one exact open incidence.
  Sources which do not admit maintenance use the default zero budget.  The
  value belongs to the live row, not to a later domain vocabulary or revision. -/
  openProgressBudgetAt : {support : Support} →
    {responsibility : Responsibility} → OpenAt support responsibility → Nat :=
      fun _ => 0
  HoldsAt : Support → Claim → Type u
  ObstructionAt : Support → Type u
  obstructionClaim : {support : Support} → ObstructionAt support → Claim
  SemanticChangeAt : Support → Claim → Claim → Type u
  DispositionAt : Support → WorldDispositionKind → Type u

/-- A local domain presents its actual occurrences and responsibility
inventory as a chart of one shared world network.  The chart supplies no state
update, receipt compiler, or target current. -/
structure OccurrenceChart (N : WorldRelationNetwork.{u}) : Type (u + 1) where
  Occurrence : Type u
  LocalAnchor : Type u
  LocalIncidence : Type u
  LocalLineage : Type u
  supportOf : Occurrence → N.Support
  anchorAt : Occurrence → LocalAnchor
  incidenceAt : Occurrence → LocalIncidence
  lineageAt : Occurrence → LocalLineage
  anchorKey : LocalAnchor → N.Anchor
  incidenceKey : LocalIncidence → N.Incidence
  lineageKey : LocalLineage → N.Lineage
  ResponsibilityAt : Occurrence → Type u
  responsibilityPresentation : (occurrence : Occurrence) →
    ConstructivePresentation (ResponsibilityAt occurrence)
      (Σ responsibility, N.OpenAt (supportOf occurrence) responsibility)
  anchor_commutes : (occurrence : Occurrence) →
    anchorKey (anchorAt occurrence) = N.anchorAt (supportOf occurrence)
  incidence_commutes : (occurrence : Occurrence) →
    incidenceKey (incidenceAt occurrence) =
      N.incidenceAt (supportOf occurrence)
  lineage_commutes : (occurrence : Occurrence) →
    lineageKey (lineageAt occurrence) = N.lineageAt (supportOf occurrence)

/-- Existing overlap identifies two local occurrences through one common
actual support.  It does not identify their state, residual, or event types. -/
structure SharedOccurrenceSpan
    {N : WorldRelationNetwork.{u}}
    (A B : OccurrenceChart N) : Type u where
  oldOccurrence : A.Occurrence
  newOccurrence : B.Occurrence
  support_eq : A.supportOf oldOccurrence = B.supportOf newOccurrence

namespace SharedOccurrenceSpan

variable
    {N : WorldRelationNetwork.{u}}
    {A B : OccurrenceChart N}

/-- Transport a world-indexed object from the new presentation back to the
old occurrence's definitionally shared support. -/
def transportNew
    (span : SharedOccurrenceSpan A B)
    {F : N.Support → Type u}
    (value : F (B.supportOf span.newOccurrence)) :
    F (A.supportOf span.oldOccurrence) :=
  span.support_eq.symm ▸ value

/-- Open responsibility inventory is conserved through an explicit
bidirectional program over the shared support equality. -/
def responsibilityPresentation
    (span : SharedOccurrenceSpan A B) :
    ConstructivePresentation
      (A.ResponsibilityAt span.oldOccurrence)
      (B.ResponsibilityAt span.newOccurrence) := by
  let OpenInventory : N.Support → Type u := fun support =>
    Σ responsibility, N.OpenAt support responsibility
  exact
    (A.responsibilityPresentation span.oldOccurrence).trans <|
      (ConstructivePresentation.cast
        (F := OpenInventory) span.support_eq).trans <|
        (B.responsibilityPresentation span.newOccurrence).symm

theorem anchor_key_eq
    (span : SharedOccurrenceSpan A B) :
    A.anchorKey (A.anchorAt span.oldOccurrence) =
      B.anchorKey (B.anchorAt span.newOccurrence) :=
  calc
    A.anchorKey (A.anchorAt span.oldOccurrence) =
        N.anchorAt (A.supportOf span.oldOccurrence) :=
      A.anchor_commutes span.oldOccurrence
    _ = N.anchorAt (B.supportOf span.newOccurrence) :=
      congrArg N.anchorAt span.support_eq
    _ = B.anchorKey (B.anchorAt span.newOccurrence) :=
      (B.anchor_commutes span.newOccurrence).symm

theorem incidence_key_eq
    (span : SharedOccurrenceSpan A B) :
    A.incidenceKey (A.incidenceAt span.oldOccurrence) =
      B.incidenceKey (B.incidenceAt span.newOccurrence) :=
  calc
    A.incidenceKey (A.incidenceAt span.oldOccurrence) =
        N.incidenceAt (A.supportOf span.oldOccurrence) :=
      A.incidence_commutes span.oldOccurrence
    _ = N.incidenceAt (B.supportOf span.newOccurrence) :=
      congrArg N.incidenceAt span.support_eq
    _ = B.incidenceKey (B.incidenceAt span.newOccurrence) :=
      (B.incidence_commutes span.newOccurrence).symm

theorem lineage_key_eq
    (span : SharedOccurrenceSpan A B) :
    A.lineageKey (A.lineageAt span.oldOccurrence) =
      B.lineageKey (B.lineageAt span.newOccurrence) :=
  calc
    A.lineageKey (A.lineageAt span.oldOccurrence) =
        N.lineageAt (A.supportOf span.oldOccurrence) :=
      A.lineage_commutes span.oldOccurrence
    _ = N.lineageAt (B.supportOf span.newOccurrence) :=
      congrArg N.lineageAt span.support_eq
    _ = B.lineageKey (B.lineageAt span.newOccurrence) :=
      (B.lineage_commutes span.newOccurrence).symm

end SharedOccurrenceSpan

/-- U7 turns one actual network obstruction into the exact next structural
producer responsibility.  Cross-step consumption and typed disposition live
in `LivingLawObstructionLineageEvolutionKernel`; theory revision remains U8. -/
structure U7ProducerCalculus (N : WorldRelationNetwork.{u}) : Type (u + 1) where
  DemandAt : {support : N.Support} → N.ObstructionAt support → Type u
  generateDemand : {support : N.Support} →
    (obstruction : N.ObstructionAt support) → DemandAt obstruction

/-- Exact generation authority for one U7 demand.

`DemandAt obstruction` remains an open domain vocabulary and may even be
`PUnit`.  Actual authority, however, is this dependent seal: its only
constructor fixes the payload to the demand generated from the exact
obstruction.  Inhabited demand fibres therefore cannot be replayed across
sibling obstructions. -/
inductive SourceGeneratedU7DemandAt
    {N : WorldRelationNetwork.{u}} (U7 : U7ProducerCalculus N) :
    {support : N.Support} → (obstruction : N.ObstructionAt support) →
      U7.DemandAt obstruction → Type u
  | canonical {support : N.Support}
      (obstruction : N.ObstructionAt support) :
      SourceGeneratedU7DemandAt U7 obstruction (U7.generateDemand obstruction)

namespace SourceGeneratedU7DemandAt

/-- A generated-demand seal contains no second payload choice. -/
instance instSubsingleton
    {N : WorldRelationNetwork.{u}} {U7 : U7ProducerCalculus N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {demand : U7.DemandAt obstruction} :
    Subsingleton (SourceGeneratedU7DemandAt U7 obstruction demand) :=
  ⟨by
    intro left right
    cases left
    cases right
    rfl⟩

/-- The payload of an authoritative demand is exactly the source-generated
demand for its obstruction. -/
theorem payload_eq_generated
    {N : WorldRelationNetwork.{u}} {U7 : U7ProducerCalculus N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {demand : U7.DemandAt obstruction}
    (_generated : SourceGeneratedU7DemandAt U7 obstruction demand) :
    demand = U7.generateDemand obstruction := by
  cases _generated
  rfl

end SourceGeneratedU7DemandAt

end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
