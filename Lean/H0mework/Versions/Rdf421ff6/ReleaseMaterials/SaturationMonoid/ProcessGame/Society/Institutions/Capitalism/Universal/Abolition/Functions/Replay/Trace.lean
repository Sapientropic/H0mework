import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Request

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def itemAt (item : ExecutionItem Party Good Port Technology Instrument) :
    ExecutionItem Party Good Port Technology Instrument :=
  ⟨item.index, item.before, requestAt law item.before item.request⟩

/-- The next source current is the original actual step, including its
refusals. A failed request never becomes newly executable by opening gates. -/
def wordAt (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument → RawEvent Party Good Port Technology Instrument
  | [] => []
  | request :: remaining =>
      requestAt law current request :: wordAt (law.step current request) remaining

theorem replay_keeps_every_original_instruction_position
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument) :
    (wordAt law current original).length = original.length := by
  induction original generalizing current with
  | nil => rfl
  | cons request remaining ih =>
      exact congrArg Nat.succ (ih (law.step current request))

theorem replay_is_computed_from_the_original_actual_inventory
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (original : RawEvent Party Good Port Technology Instrument) :
    wordAt law current original =
      (law.execute current index original).items.map (fun item => requestAt law item.before item.request) := by
  induction original generalizing current index with
  | nil => rfl
  | cons request remaining ih =>
      exact congrArg (requestAt law current request :: ·) (ih (law.step current request) (index + 1))

theorem replay_execution_has_the_same_actual_currents
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (original : RawEvent Party Good Port Technology Instrument) :
    ((PublicFunction.physicalLaw law).execute current index (wordAt law current original)).final =
      (law.execute current index original).final ∧
    ((PublicFunction.physicalLaw law).execute current index (wordAt law current original)).items =
      (law.execute current index original).items.map (itemAt law) := by
  induction original generalizing current index with
  | nil => exact ⟨rfl, rfl⟩
  | cons request remaining ih =>
      have next := the_computed_request_preserves_the_original_actual_step law current request
      have later := ih (law.step current request) (index + 1)
      simp only [wordAt, RawLaw.execute, next, List.map_cons]
      exact ⟨later.1, congrArg (itemAt law ⟨index, current, request⟩ :: ·) later.2⟩

theorem replay_preserves_the_original_full_next
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).next current (wordAt law current original) = law.next current original := by
  unfold RawLaw.next
  rw [(replay_execution_has_the_same_actual_currents law current 0 original).1]
  rfl

theorem every_replay_item_is_lawful_and_has_no_controller_consents
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (original : RawEvent Party Good Port Technology Instrument) :
    ∀ item ∈ ((PublicFunction.physicalLaw law).execute current index (wordAt law current original)).items,
      (PublicFunction.physicalLaw law).Valid item.before item.request ∧ item.request.consents = [] := by
  rw [(replay_execution_has_the_same_actual_currents law current index original).2]
  intro item present
  obtain ⟨sourceItem, member, rfl⟩ := List.mem_map.mp present
  exact ⟨the_computed_request_is_lawful law sourceItem.before sourceItem.request,
    (the_computed_request_has_the_same_signer_and_no_consents law sourceItem.before sourceItem.request).2⟩

/-- This is a filter of the existing source trace, not a receipt or
liability registry. Each retained value is the complete original item. -/
def originalRefusals (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument) :=
  (law.rawItems current original).filter (fun item => decide (¬ law.Valid item.before item.request))

theorem refusal_metadata_is_exactly_the_original_failed_source_item
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) :
    item ∈ originalRefusals law current original ↔
      item ∈ law.rawItems current original ∧ ¬ law.Valid item.before item.request := by
  simp [originalRefusals]

theorem every_original_refusal_retains_its_position_before_and_signer
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (refused : item ∈ originalRefusals law current original) :
    itemAt law item ∈ (PublicFunction.physicalLaw law).rawItems current (wordAt law current original) ∧
    (itemAt law item).index = item.index ∧
    (itemAt law item).before = item.before ∧
    (itemAt law item).request.signer = item.request.signer ∧
    (itemAt law item).request.operation = .present ∧
    (itemAt law item).request.gates = [] := by
  obtain ⟨present, failed⟩ := (refusal_metadata_is_exactly_the_original_failed_source_item law current original item).mp refused
  have shape := an_original_rejection_keeps_a_zero_effect_presentation law item.before item.request failed
  refine ⟨?_, rfl, rfl, (the_computed_request_has_the_same_signer_and_no_consents law item.before item.request).1, shape.1, shape.2.1⟩
  change itemAt law item ∈ ((PublicFunction.physicalLaw law).execute current 0 (wordAt law current original)).items
  rw [(replay_execution_has_the_same_actual_currents law current 0 original).2]
  exact List.mem_map.mpr ⟨item, present, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.replay_execution_has_the_same_actual_currents
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.every_original_refusal_retains_its_position_before_and_signer
