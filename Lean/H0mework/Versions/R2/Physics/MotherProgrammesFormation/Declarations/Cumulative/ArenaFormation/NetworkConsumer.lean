import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.NetworkCoverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Consumer

/-! The complete original relation-network declaration enters an actual
rank-material factory without a fixed-carrier address premise. Its native
presentation remains the already signed original presentation interface. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetworkOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherArenaNetwork
noncomputable section
variable {rank : Ordinal.{0}}

def Encoding.ofTotal {N : WorldRelationNetwork.{0}}
    (encode : MotherNetworkOrigin.Total N ↪ MotherArenaHigher.Base rank) : Encoding (rank := rank) N where
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

theorem every_network_retaining_original_material (N : WorldRelationNetwork.{0}) :
    ∃ rank : Ordinal.{0}, ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
      ∃ material : MotherArenaHigher.Material rank, ∃ G : WorldRelationNetwork.{0},
        formNetwork material = some G ∧ Nonempty (MotherNetworkOrigin.Presentation N G) ∧
        Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
          (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let Total := MotherNetworkOrigin.Total N ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let address : MotherNetworkOrigin.Total N ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨material, G, formed, presentation⟩ := every_embedded_network N (.ofTotal address)
  exact ⟨rank, originalAddress, material, G, formed, presentation,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

theorem every_network (N : WorldRelationNetwork.{0}) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, formNetwork material = some G ∧ Nonempty (MotherNetworkOrigin.Presentation N G) := by
  obtain ⟨rank, _address, material, G, formed, presentation, _retained⟩ := every_network_retaining_original_material N
  exact ⟨rank, material, G, formed, presentation⟩

/-- The consumer retains all original source events and complete Type-valued
affected inventories; it does not substitute an emitted trajectory. -/
theorem all_admitted_source_inventories (N : WorldRelationNetwork.{0}) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, ∃ p : MotherNetworkOrigin.Presentation N G,
        formNetwork material = some G ∧
        ∀ {V : ConstructiveRoot.Vocabulary.{0}}
          {represented : SourceNativeRestructuringLedgerSource N V}
          (admission : SourceNativeCompleteEventInventoryAdmission represented)
          {current : V.Current}
          (event : represented.source.toRootSource.actual.OccurrenceAt current),
          Nonempty (ConstructivePresentation
            (admission.actualSource.source.law.AffectedInventoryAt
              (admission.actualOccurrenceAt event).2)
            (OpenResponsibilityAt G (p.support (admission.actualOccurrenceAt event).1))) := by
  obtain ⟨rank, material, G, formed, ⟨p⟩⟩ := every_network N
  refine ⟨rank, material, G, p, formed, ?_⟩
  intro V represented admission current event
  exact ⟨p.inventory admission.actualSource.source (admission.actualOccurrenceAt event)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetworkOrigin
