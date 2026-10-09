import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Translation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Current

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

structure SourceSeed (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (path : CPS1Recycling.SplitSite) (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) where
  translation : TranslationEvent current water raw
  recycled : CPS1Recycling.ExecutionAt translation.generatedFrame
  actualRecycling : recycled = CPS1Recycling.run translation.generatedFrame events feed
  observed : CPS1StockRecursion.Source.Observation translation.generatedFrame
  observedSource : observed = CPS1StockRecursion.Source.observe translation.generatedFrame path []
    ⟨recycled.stock.map CPS1Reinitiation.Species.retained,[],0,none⟩
  captured : CPS1LocalChemicalExecution.Source.Occurrence translation.generatedFrame
  actualCapture : captured = CPS1LocalChemicalExecution.Source.fromCurrent translation.generatedFrame observed
  joined : CPS1EditingChemicalJoin.Source.Occurrence translation.generatedFrame
  noReload : joined.current = captured.current
  previousEditing : joined.editingFirst = (CPS1ReactiveField.editingSource current.old).editingFirst
  currentEditing : joined.editing = translation.genomic.event.result
  atomic : CPS1AtomicSource.Current.Occurrence translation.generatedFrame
  actualAtomic : atomic = CPS1AtomicSource.Current.fromActual translation.generatedFrame joined
  remainder : List (CPS1ReactiveField.LiveMaterial frame)
  remainderSource : remainder = translation.genomic.event.slice.remainder
  wholeInput : (CPS1ReactiveField.liveStock current).Perm (translation.genomic.event.slice.selected ++ remainder)

def sourceSeed (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (path : CPS1Recycling.SplitSite) (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (translation : TranslationEvent current water raw) : SourceSeed current water raw path events feed :=
  let generated := translation.generatedFrame
  let recycled := CPS1Recycling.run generated events feed
  let observed := CPS1StockRecursion.Source.observe generated path []
    ⟨recycled.stock.map CPS1Reinitiation.Species.retained,[],0,none⟩
  let captured := CPS1LocalChemicalExecution.Source.fromCurrent generated observed
  let previousEditing := CPS1ReactiveField.editingSource current.old
  let joined : CPS1EditingChemicalJoin.Source.Occurrence generated :=
    ⟨captured,previousEditing.editingFirst,translation.genomic.event.result,captured.current⟩
  let atomic := CPS1AtomicSource.Current.fromActual generated joined
  ⟨translation,recycled,rfl,observed,rfl,captured,rfl,joined,rfl,rfl,rfl,atomic,rfl,
    translation.genomic.event.slice.remainder,rfl,translation.genomic.event.slice.whole⟩

theorem seed_actual_stock (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (path : CPS1Recycling.SplitSite) (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (translation : TranslationEvent current water raw) :
    let seed := sourceSeed current water raw path events feed translation
    seed.observed.current.stock = seed.recycled.stock.map CPS1Reinitiation.Species.retained ∧
    seed.captured.current = CPS1LocalChemicalExecution.Source.start seed.translation.generatedFrame
      (seed.recycled.stock.map CPS1Reinitiation.Species.retained) ∧
    seed.joined.current = seed.captured.current ∧
    seed.joined.editing = seed.translation.genomic.event.result ∧
    seed.joined.current.stock = seed.captured.current.stock := ⟨rfl,rfl,rfl,rfl,rfl⟩

inductive SourceDisposition (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (path : CPS1Recycling.SplitSite) (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
  | rejected (original : TranslationDisposition current water raw)
  | generated (seed : SourceSeed current water raw path events feed)

def generateSource (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (path : CPS1Recycling.SplitSite) (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) :
    SourceDisposition current water raw path events feed :=
  match translateLive current water raw with
  | TranslationDisposition.genomicRejected original => .rejected (.genomicRejected original)
  | TranslationDisposition.decodingRejected genomic unspent source failure =>
    .rejected (.decodingRejected genomic unspent source failure)
  | TranslationDisposition.translated event => .generated (sourceSeed current water raw path events feed event)

end
end CPS1LiveEditing
