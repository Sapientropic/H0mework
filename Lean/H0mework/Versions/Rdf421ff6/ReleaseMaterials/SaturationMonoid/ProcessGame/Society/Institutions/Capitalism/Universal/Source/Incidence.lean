import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.GeneratedPower
import Mathlib.Data.List.FinRange

/-!
# Primitive socioeconomic incidences of one original root occurrence

The source supplies its existing M0 face and action/relation compilers.
Inventory items and responsibility rows are the original source inventory;
an economic effect cannot select an unrelated bearer after classification.
There are no institutional channel names or capitalism-membership inputs.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle.Universal Relations Power

universe u

abbrev OriginalOccurrence {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) := Sigma (NativeEventAt source)

def originalOccurrence {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) : OriginalOccurrence source :=
  ⟨current, event.val⟩

/-- This is an exposure of existing source compilers, not an actor carrier.
Each action and relation below is compiled through the same original M0 face. -/
structure ExistingSocietyFace
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  State : Type u
  traceOf : OriginalOccurrence source → RootedAccountedUnfolding State
  actorFace : M0BoundaryFace traceOf
  controllersAt : (occurrence : OriginalOccurrence source) →
    SourceOwnedActionControllerCompiler ⟨occurrence⟩ actorFace
  relationsAt : (occurrence : OriginalOccurrence source) →
    SourceOwnedRelationRoleCompiler traceOf ⟨occurrence⟩ actorFace
  actionEquality : (occurrence : OriginalOccurrence source) →
    DecidableEq (controllersAt occurrence).ActionSeed
  lineageEquality : (occurrence : OriginalOccurrence source) →
    DecidableEq (actorFace.Lineage occurrence)
  relationEquality : (occurrence : OriginalOccurrence source) →
    DecidableEq ((relationsAt occurrence).RelationLineage occurrence)

abbrev OriginalInventoryItem
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) :=
  source.source.law.AffectedInventoryAt event.val.2

def originalRow
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) (item : OriginalInventoryItem event) :
    OpenResponsibilityAt N (source.source.toRootSource.account.supportOf event.val) :=
  (source.source.law.affectedInventoryPresentation event.val.2).forward item

theorem originalRow_recovers_item
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    (event : ContinuingEventAt source current) (item : OriginalInventoryItem event) :
    (source.source.law.affectedInventoryPresentation event.val.2).backward
        (originalRow event item) = item :=
  (source.source.law.affectedInventoryPresentation event.val.2).backward_forward item

namespace ExistingSocietyFace

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V} (society : ExistingSocietyFace source)
  {current : V.Current} (event : ContinuingEventAt source current)

abbrev controllers := society.controllersAt (originalOccurrence event)
abbrev relations := society.relationsAt (originalOccurrence event)
abbrev Actor := (society.controllers event).Actor
abbrev Relation := (society.relations event).GeneratedRelation

def actorEquality : DecidableEq (society.Actor event) := fun left right =>
  match society.lineageEquality (originalOccurrence event) left.val right.val with
  | .isTrue same => .isTrue (Subtype.ext same)
  | .isFalse different => .isFalse (fun same => different (congrArg Subtype.val same))

/-- A required authorization port read from the source operation's executed
guard.  Both pointers are exact seeds of this same occurrence. -/
structure RequiredAuthorityPort where
  action : (society.controllers event).ExactActionSeed
  relation : (society.relations event).ExactRelationSeed

/-- An actually invoked disposition right.  Its holder is the beneficiary
of the original purpose incidence; the actual authorization may be a
delegated execution or an explicit consent.  Zero realized profit does not
erase this source right.  The concrete decoder supplies its raw basis. -/
structure DispositionRightPort where
  actualAuthorization : (society.controllers event).ExactActionSeed
  purpose : (society.relations event).ExactRelationSeed
  originalUse : OriginalInventoryItem event

/-- A surplus/right disposition's authorizing port and purpose incidence.
The claim comes from its original inventory item, not a new financial book.
The quantity is used only for effectiveness, never added to physical stock. -/
structure SurplusDispositionPort (Quantity : Type u) where
  authorizedBy : (society.controllers event).ExactActionSeed
  actualAction : (society.controllers event).ExactActionSeed
  purpose : (society.relations event).ExactRelationSeed
  originalClaim : OriginalInventoryItem event
  effectiveAmount : Quantity

/-- A contribution can be labour, care, a material input, a public service
or an automated operation.  Its source relation phase supplies the role. -/
structure ContributionPort (Good Quantity : Type u) where
  action : (society.controllers event).ExactActionSeed
  purpose : (society.relations event).ExactRelationSeed
  amount : Good → Quantity

structure AcquisitionEffect (Good Quantity : Type u)
    (_item : OriginalInventoryItem event) where
  recipient : (society.relations event).ExactRelationSeed
  acquired : Good → Quantity
  physicallyProduced : Good → Quantity
  receivedForNecessities : Good → Quantity
  requiredPorts : List (society.RequiredAuthorityPort event)
  dispositionRights : List (society.DispositionRightPort event)
  surplusPorts : List (society.SurplusDispositionPort event Quantity)
  contributions : List (society.ContributionPort event Good Quantity)
  reproductionRequired : Good → Quantity
  reproductionPaid : Good → Quantity
  maintenanceActions : List (society.controllers event).ExactActionSeed
  selfRequestAllowed : Bool

namespace AcquisitionEffect

variable {Good Quantity : Type u} {item : OriginalInventoryItem event}
  (effect : society.AcquisitionEffect event Good Quantity item)

def bearerRow (_effect : society.AcquisitionEffect event Good Quantity item) : OpenResponsibilityAt N
    (source.source.toRootSource.account.supportOf event.val) := originalRow event item

def actualDisposition : LedgerEntryDispositionAt N (effect.bearerRow society event) :=
  (source.ledgerCompiler.compile event.val).entryDisposition (originalRow event item)

def recipientActor : society.Actor event := effect.recipient.actor (society.relations event)

theorem recipient_provenance :
    ∃ state ∈ (society.traceOf (originalOccurrence event)).trace,
      state = society.actorFace.state (originalOccurrence event) ∧
      (society.relations event).relationSeedAt (originalOccurrence event) state effect.recipient.val ∧
      society.actorFace.SeedAt (originalOccurrence event) state
        ((society.relations event).beneficiaryActorSeed effect.recipient.val) :=
  effect.recipient.exact_state_provenance (society.relations event)

end AcquisitionEffect

/-- The raw quantity exists before actor/relation recognition.  An unseeded
participant therefore leaves its actual acquisition on the original pending
row instead of disappearing from material balance. -/
structure RawEffectLaw (Good Quantity : Type u) where
  rawAcquired : {current : V.Current} → (event : ContinuingEventAt source current) →
    OriginalInventoryItem event → Good → Quantity
  decode : {current : V.Current} → (event : ContinuingEventAt source current) →
    (item : OriginalInventoryItem event) →
      Option (society.AcquisitionEffect event Good Quantity item)
  decoded_exact : {current : V.Current} → (event : ContinuingEventAt source current) →
    (item : OriginalInventoryItem event) → (effect : society.AcquisitionEffect event Good Quantity item) →
    decode event item = some effect → effect.acquired = rawAcquired event item

end ExistingSocietyFace

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source
