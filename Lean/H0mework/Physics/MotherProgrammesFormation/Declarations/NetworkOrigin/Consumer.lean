import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Coverage
import H0mework.Foundation.Authority.SourceProjectionInventory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherNetworkFactory
noncomputable section

def Field (N : WorldRelationNetwork.{0}) : Fin 11 → Type
  | 0 => N.Support
  | 1 => N.Anchor
  | 2 => N.Incidence
  | 3 => N.Lineage
  | 4 => N.Responsibility
  | 5 => N.Claim
  | 6 => Σ s r, N.OpenAt s r
  | 7 => Σ s c, N.HoldsAt s c
  | 8 => Σ s, N.ObstructionAt s
  | 9 => Σ s c d, N.SemanticChangeAt s c d
  | _ => Σ s k, N.DispositionAt s k

abbrev Total (N : WorldRelationNetwork.{0}) := Sigma (Field N)

def Encoding.ofTotal {N : WorldRelationNetwork.{0}} (encode : Total N ↪ B) : Encoding N where
  support := (Function.Embedding.sigmaMk 0).trans encode
  anchor := (Function.Embedding.sigmaMk 1).trans encode
  incidence := (Function.Embedding.sigmaMk 2).trans encode
  lineage := (Function.Embedding.sigmaMk 3).trans encode
  responsibility := (Function.Embedding.sigmaMk 4).trans encode
  claim := (Function.Embedding.sigmaMk 5).trans encode
  openAt := (Function.Embedding.sigmaMk 6).trans encode
  holdsAt := (Function.Embedding.sigmaMk 7).trans encode
  obstructionAt := (Function.Embedding.sigmaMk 8).trans encode
  semanticChangeAt := (Function.Embedding.sigmaMk 9).trans encode
  dispositionAt := (Function.Embedding.sigmaMk 10).trans encode

/-- A single formed material restores the full finite dependent network
declaration; the target and its joint address occur only in coverage. -/
theorem every_jointly_embedded_network (N : WorldRelationNetwork.{0}) (encode : Total N ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0},
      formNetwork m = some G ∧ Nonempty (Presentation N G) :=
  every_embedded_network N (.ofTotal encode)

/-- Both chart ends name the exact support carried by the original event.
The source's whole affected inventory enters the generated network through
the original shared-occurrence consumer. -/
def Presentation.sourceSpan {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current) :
    SharedOccurrenceSpan source.law.toOccurrenceChart p.chart where
  oldOccurrence := ⟨current, event⟩
  newOccurrence := event.1
  support_eq := rfl

def Presentation.inventory {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current) :
    ConstructivePresentation (source.law.AffectedInventoryAt event.2)
      (OpenResponsibilityAt G (p.support event.1)) :=
  (p.sourceSpan source event).responsibilityPresentation

theorem Presentation.inventory_forward {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (value : source.law.AffectedInventoryAt event.2) :
    (p.inventory source event).forward value =
      p.ledger event.1 ((source.law.affectedInventoryPresentation event.2).forward value) := rfl

/-- Complete original entries are recovered, including their witness values. -/
theorem Presentation.inventory_recovers_entry {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt N event.1) :
    (p.inventory source event).forward
        ((source.law.affectedInventoryPresentation event.2).backward entry) =
      p.ledger event.1 entry := by
  rw [p.inventory_forward, (source.law.affectedInventoryPresentation event.2).forward_backward]

/-- All current/event fibres of every already admitted source are consumed.
Neither this source nor a selected emitted event enters `formNetwork`. -/
theorem all_admitted_source_inventories (N : WorldRelationNetwork.{0}) (encode : Total N ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0}, ∃ p : Presentation N G,
      formNetwork m = some G ∧
      ∀ {V : ConstructiveRoot.Vocabulary.{0}}
        {represented : SourceNativeRestructuringLedgerSource N V}
        (admission : SourceNativeCompleteEventInventoryAdmission represented)
        {current : V.Current}
        (event : represented.source.toRootSource.actual.OccurrenceAt current),
        Nonempty (ConstructivePresentation
          (admission.actualSource.source.law.AffectedInventoryAt
            (admission.actualOccurrenceAt event).2)
          (OpenResponsibilityAt G (p.support (admission.actualOccurrenceAt event).1))) := by
  obtain ⟨m, G, formed, ⟨p⟩⟩ := every_jointly_embedded_network N encode
  refine ⟨m, G, p, formed, ?_⟩
  intro V represented admission current event
  exact ⟨p.inventory admission.actualSource.source (admission.actualOccurrenceAt event)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
