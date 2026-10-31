import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

open ResponsibilityLifecycle Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (past later : List (Compile.RawInput Party Good Port Technology Instrument))

theorem sourceAt_preserves_original_prefix (position : Fin past.length) :
    sourceAt source depth count prefixLimit renewalLimit (past ++ later)
        ⟨position.val, by simp; omega⟩ =
      sourceAt source depth count prefixLimit renewalLimit past position := by
  simp only [sourceAt, Physical.Prefix.eventCursor, List.get_eq_getElem,
    List.take_append_of_le_length (Nat.le_of_lt position.isLt), List.getElem_append_left position.isLt]

theorem history_preserves_original_prefix (index : source.Slot) (length : Nat) (within : length ≤ past.length) :
    history source depth count prefixLimit renewalLimit (past ++ later) index length =
      history source depth count prefixLimit renewalLimit past index length := by
  induction length with
  | zero => rfl
  | succ length prior =>
      have present : length < past.length := by omega
      have extended : length < (past ++ later).length := by simp; omega
      rw [history, history, dif_pos extended, dif_pos present, prior (by omega)]
      exact congrArg (fun input => (history source depth count prefixLimit renewalLimit past index length).advance input)
        (sourceAt_preserves_original_prefix source depth count prefixLimit renewalLimit past later ⟨length, present⟩)

variable (raw : Compile.RawInput Party Good Port Technology Instrument)

def appendedSource : SourceInput source :=
  ⟨inferInstance, depth, count, prefixLimit, renewalLimit, Physical.receive (Physical.Prefix.cursor past) raw⟩

theorem sourceAt_last_is_the_actual_next_input :
    sourceAt source depth count prefixLimit renewalLimit (past ++ [raw])
      ⟨past.length, by simp⟩ = appendedSource source depth count prefixLimit renewalLimit past raw := by
  simp only [sourceAt, appendedSource, Physical.Prefix.eventCursor, List.get_eq_getElem,
    List.take_append_of_le_length (Nat.le_refl _), List.take_length,
    List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]

theorem complete_append_is_one_original_native_boundary (index : source.Slot) :
    complete source depth count prefixLimit renewalLimit (past ++ [raw]) index =
      (complete source depth count prefixLimit renewalLimit past index).advance
        (appendedSource source depth count prefixLimit renewalLimit past raw) := by
  unfold complete
  simp only [List.length_append, List.length_singleton]
  rw [history, dif_pos (by simp),
    history_preserves_original_prefix source depth count prefixLimit renewalLimit past [raw] index past.length (Nat.le_refl _),
    sourceAt_last_is_the_actual_next_input]

theorem an_original_terminal_keeps_its_entire_generated_state (index : source.Slot)
    (terminal : (complete source depth count prefixLimit renewalLimit past index).state.current.TerminalAt 0) :
    (complete source depth count prefixLimit renewalLimit (past ++ [raw]) index).state =
      (complete source depth count prefixLimit renewalLimit past index).state := by
  rw [complete_append_is_one_original_native_boundary]
  exact (complete source depth count prefixLimit renewalLimit past index).terminal_keeps_the_complete_state _ terminal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.complete_append_is_one_original_native_boundary
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.an_original_terminal_keeps_its_entire_generated_state
