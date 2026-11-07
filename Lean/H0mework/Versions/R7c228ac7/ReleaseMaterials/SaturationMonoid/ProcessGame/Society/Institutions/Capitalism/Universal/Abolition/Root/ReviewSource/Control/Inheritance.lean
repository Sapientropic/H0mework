import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (located : Located input depth count prefixLimit renewalLimit)
  (prepared : Prepared input depth count prefixLimit renewalLimit located)

/-- On the generated path the recognizer's equality branch is reflexivity.
The source chooses its opcode by its actual phase, never by an oracle about
an external technology value or a future successful material state. -/
theorem consuming_the_source_opcode_is_exactly_its_generated_advance
    (view : View input depth count prefixLimit renewalLimit located prepared) :
    consume input depth count prefixLimit renewalLimit located prepared view
        (expectedRaw input depth count prefixLimit renewalLimit located prepared view) =
      advance input depth count prefixLimit renewalLimit located prepared view := by
  rcases view with ⟨current, phase⟩
  cases phase <;> dsimp only [consume]
  all_goals first | rfl | rw [dif_pos rfl]

theorem a_different_active_opcode_cannot_become_a_material_success
    (view : View input depth count prefixLimit renewalLimit located prepared)
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (different : raw ≠ expectedRaw input depth count prefixLimit renewalLimit located prepared view)
    (active : match view.2 with | .materialPaid .. | .stopped _ => False | _ => True) :
    ∃ reason, (consume input depth count prefixLimit renewalLimit located prepared view raw).2 = .stopped reason := by
  rcases view with ⟨current, phase⟩
  cases phase <;> try exact False.elim active
  all_goals
    dsimp only [consume]
    rw [dif_neg different]
    exact ⟨_, rfl⟩

theorem replay_append
    (view : View input depth count prefixLimit renewalLimit located prepared)
    (past later : List (Compile.RawInput Party Good Port Technology Instrument)) :
    replay input depth count prefixLimit renewalLimit located prepared view (past ++ later) =
      replay input depth count prefixLimit renewalLimit located prepared
        (replay input depth count prefixLimit renewalLimit located prepared view past) later := by
  induction past generalizing view with
  | nil => rfl
  | cons raw rest ih => exact ih _

theorem every_consumed_input_extends_the_same_original_source_readout
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    atCursor input depth count prefixLimit renewalLimit located prepared (Physical.next (Physical.receive current raw)) =
      consume input depth count prefixLimit renewalLimit located prepared
        (atCursor input depth count prefixLimit renewalLimit located prepared current) raw := by
  obtain ⟨remaining, decomposition⟩ := recovery_uses_a_real_consumed_registration input depth count
    prefixLimit renewalLimit current located original
  have pastEq : current.past = (located.epoch input depth count prefixLimit renewalLimit).past ++ remaining := by
    rw [located.epoch_is_after_the_original_registration]
    exact decomposition
  have beforeDrop : current.past.drop (located.epoch input depth count prefixLimit renewalLimit).past.length = remaining := by
    rw [pastEq, List.drop_left]
  have afterDrop : (Physical.next (Physical.receive current raw)).past.drop
      (located.epoch input depth count prefixLimit renewalLimit).past.length = remaining ++ [raw] := by
    change (current.past ++ [raw]).drop _ = _
    rw [pastEq, List.append_assoc, List.drop_left]
  simp only [atCursor, beforeDrop, afterDrop, replay_append, replay]

theorem every_generated_pending_step_eliminates_the_code_comparison
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (original : recovered input depth count prefixLimit renewalLimit current = some located) :
    let view := atCursor input depth count prefixLimit renewalLimit located prepared current
    let raw := expectedRaw input depth count prefixLimit renewalLimit located prepared view
    recovered input depth count prefixLimit renewalLimit (Physical.next (Physical.receive current raw)) = some located ∧
      atCursor input depth count prefixLimit renewalLimit located prepared (Physical.next (Physical.receive current raw)) =
        advance input depth count prefixLimit renewalLimit located prepared view := by
  dsimp only
  constructor
  · exact later_registered_code_cannot_replace_the_original_epoch input depth count prefixLimit renewalLimit current located original _
  · rw [every_consumed_input_extends_the_same_original_source_readout input depth count prefixLimit renewalLimit located prepared current original,
      consuming_the_source_opcode_is_exactly_its_generated_advance]

#print axioms consuming_the_source_opcode_is_exactly_its_generated_advance
#print axioms a_different_active_opcode_cannot_become_a_material_success
#print axioms every_generated_pending_step_eliminates_the_code_comparison

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
