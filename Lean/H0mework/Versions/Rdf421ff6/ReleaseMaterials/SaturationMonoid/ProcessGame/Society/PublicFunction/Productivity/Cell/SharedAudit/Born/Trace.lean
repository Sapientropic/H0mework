import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

abbrev Item := ExecutionItem Party Good Port Technology Unit

def itemsAt (ordinal : Nat) : List Item :=
  law.rawItems (frameAt ordinal).raw (wordAt ordinal (frameAt ordinal))

theorem items_are_the_original_execution (ordinal : Nat) :
    itemsAt ordinal = law.rawItems (source.currentAt ordinal)
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current) := by
  change law.rawItems _ _ = law.rawItems _ _
  rw [current_is_generated_machine, actual_word_is_machine]

structure Occurrence where
  ordinal : Nat
  item : Item
  original : item ∈ itemsAt ordinal

def occurrences (count : Nat) : List Occurrence :=
  (List.range count).flatMap fun ordinal =>
    (itemsAt ordinal).attach.map fun item => ⟨ordinal, item.val, item.property⟩

structure Birth extends Occurrence where
  private mk ::
  parent : Party
  child : Party
  goods : Bundle Good
  transfer : item.request.operation = .transfer parent child goods
  accepted : law.Valid item.before item.request
  own_signature : item.request.signer = parent
  distinct : parent ≠ child
  empty_seed : item.before.stock child .seed = 0
  positive_credit : 0 < flowAt (law.actualCredit item.before item.request) child .seed
  actual_seed : 0 < (law.step item.before item.request).stock child .seed
  running : 0 < ordinal
  cell_operator : child ≠ 3

def recognizeBirth (occurrence : Occurrence) : Option Birth :=
  match operation : occurrence.item.request.operation with
  | .transfer parent child goods =>
    if checked : law.Valid occurrence.item.before occurrence.item.request ∧
        occurrence.item.request.signer = parent ∧ parent ≠ child ∧
        occurrence.item.before.stock child .seed = 0 ∧
        0 < flowAt (law.actualCredit occurrence.item.before occurrence.item.request) child .seed ∧
        0 < (law.step occurrence.item.before occurrence.item.request).stock child .seed ∧
        0 < occurrence.ordinal ∧ child ≠ 3 then
      some ⟨occurrence, parent, child, goods, operation, checked.1, checked.2.1,
        checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.1,
        checked.2.2.2.2.2.1, checked.2.2.2.2.2.2.1, checked.2.2.2.2.2.2.2⟩
    else none
  | _ => none

def births (count : Nat) : List Birth := (occurrences count).filterMap recognizeBirth

theorem recognition_preserves_the_occurrence (occurrence : Occurrence) (birth : Birth)
    (recognized : recognizeBirth occurrence = some birth) : birth.toOccurrence = occurrence := by
  unfold recognizeBirth at recognized
  split at recognized
  · split at recognized
    · cases recognized; rfl
    · cases recognized
  · cases recognized

theorem every_generated_birth_is_in_the_prefix (count : Nat) (birth : Birth) (member : birth ∈ births count) :
    birth.ordinal < count := by
  obtain ⟨occurrence, original, recognized⟩ := List.mem_filterMap.mp member
  have same := recognition_preserves_the_occurrence occurrence birth recognized
  obtain ⟨ordinal, before_cut, inside⟩ := List.mem_flatMap.mp original
  obtain ⟨item, _inside, equation⟩ := List.mem_map.mp inside
  have ordinal_eq := congrArg Occurrence.ordinal same
  rw [← equation] at ordinal_eq
  simpa only [ordinal_eq] using List.mem_range.mp before_cut

def discovered (ordinal : Nat) (index : Fin (births (ordinal + 1)).length) : Birth :=
  (births (ordinal + 1))[index.val]

theorem discovered_has_arrived (ordinal : Nat) (index : Fin (births (ordinal + 1)).length) :
    (discovered ordinal index).ordinal ≤ ordinal := by
  have present : discovered ordinal index ∈ births (ordinal + 1) := List.getElem_mem _
  have before_cut := every_generated_birth_is_in_the_prefix _ _ present
  omega

theorem Birth.original_item (birth : Birth) :
    birth.item ∈ law.rawItems (source.currentAt birth.ordinal)
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input birth.ordinal).current) := by
  rw [← items_are_the_original_execution]
  exact birth.original

open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

def Birth.instructionOrigin (birth : Birth) : Financial.InstructionOrigin source.input :=
  RootFace.original source.input (ProgrammeHistory.visitAt source.input birth.ordinal)
    ⟨birth.item, birth.original_item⟩

theorem Birth.instruction_decodes_the_original_item (birth : Birth) :
    birth.instructionOrigin.instruction? source.input = some birth.item :=
  RootFace.original_decodes_exact_item source.input (ProgrammeHistory.visitAt source.input birth.ordinal)
    ⟨birth.item, birth.original_item⟩

theorem Birth.original_row_and_next (birth : Birth) :
    ProgrammeLedger.transferReceiptOf source.input (source.taskWrite (birth.ordinal - 1)).2 =
      some (source.writtenReceipt (birth.ordinal - 1)) ∧
      (source.actualExecution (birth.ordinal - 1)).after = source.currentAt (birth.ordinal + 1) := by
  refine ⟨source.receipt_is_in_original_task_write _, ?_⟩
  have running := birth.running
  have same : birth.ordinal - 1 + 2 = birth.ordinal + 1 := by omega
  exact (source.actualExecution (birth.ordinal - 1)).root_next_exact.trans (congrArg source.currentAt same)

theorem four_actual_production_births :
    (births 11).map (fun birth => (birth.parent, birth.child, birth.ordinal, birth.item.index)) =
      [(0, 1, 4, 1), (0, 2, 7, 0), (1, 4, 9, 1), (2, 5, 10, 1)] := by
  decide +kernel

theorem four_births : (births 11).length = 4 := by
  have lengths := congrArg List.length four_actual_production_births
  simpa only [List.length_map, List.length_cons, List.length_nil] using lengths

def born (index : Fin 4) : Birth := (births 11)[index.val]'(by rw [four_births]; exact index.isLt)

def birthKey (birth : Birth) := (birth.ordinal, birth.item.index)

theorem actual_birth_keys_are_distinct : ((births 11).map birthKey).Nodup := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born
