import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Safety
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Validation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

theorem occurrence_items_are_original (count : Nat) :
    (occurrences count).map Occurrence.item = Participation.receipts true count := by
  rw [Participation.receipt_machine]
  simp only [occurrences, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro ordinal _inside
  change (itemsAt ordinal).attach.map Subtype.val = itemsAt ordinal
  exact List.attach_map_subtype_val _

def occurrenceOrigin (event : Occurrence) : Financial.InstructionOrigin productionSource.input :=
  RootFace.original productionSource.input (ProgrammeHistory.visitAt productionSource.input event.ordinal)
    ⟨event.item, by
      change event.item ∈ law.rawItems (productionSource.currentAt event.ordinal)
        (ProgrammeSource.rawEvent productionSource.input (ProgrammeHistory.visitAt productionSource.input event.ordinal).current)
      rw [← items_are_the_original_execution]
      exact event.original⟩

theorem occurrence_origin_decodes_exactly (event : Occurrence) :
    (occurrenceOrigin event).instruction? productionSource.input = some event.item :=
  RootFace.original_decodes_exact_item productionSource.input (ProgrammeHistory.visitAt productionSource.input event.ordinal) _

theorem observation_outside_inventory (event : Observation) (actor : Party) (outside : 6 ≤ actor) (good : Good) :
    event.val.item.before.stock actor good = 0 ∧
      (law.step event.val.item.before event.val.item.request).stock actor good = 0 := by
  apply Participation.outside_at_every_cut true actor outside event.val.item
  have member : event.val.item ∈ (occurrences 25).map Occurrence.item :=
    List.mem_map.mpr ⟨event.val, event.property, rfl⟩
  rwa [occurrence_items_are_original] at member

/-- This law is independent of either audit algorithm. -/
theorem raw_balance (actor : Party) (good : Good) :
    (rawFrame 25).raw.stock actor good + law.totalDebit ((occurrences 25).map Occurrence.item) actor good =
      initial.stock actor good + law.totalCredit ((occurrences 25).map Occurrence.item) actor good := by
  rw [occurrence_items_are_original]
  have balance := SharedAudit.receipt_balance productionSource 25 actor good
  change (productionSource.frameAt 25).raw.stock actor good + law.totalDebit (Participation.receipts true 25) actor good =
    initial.stock actor good + law.totalCredit (Participation.receipts true 25) actor good at balance
  rw [← (productionSource.canonical_frame 25).1, Participation.actual_current_is_the_machine] at balance
  exact balance

theorem first_productions_exist : ∀ index : Fin 4,
    (productionsAt (born index) (if index.val = 0 then 6 else if index.val = 1 then 8 else if index.val = 2 then 9 else 10)).isEmpty = false := by
  decide +kernel

def firstProduction (index : Fin 4) : ProductionData (born index)
    (if index.val = 0 then 6 else if index.val = 1 then 8 else if index.val = 2 then 9 else 10) :=
  (productionsAt (born index) _).head (List.isEmpty_eq_false_iff.mp (first_productions_exist index))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero
