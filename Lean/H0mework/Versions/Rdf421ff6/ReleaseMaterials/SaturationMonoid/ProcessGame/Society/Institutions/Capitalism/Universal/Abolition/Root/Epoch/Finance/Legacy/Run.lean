import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Edges

/-! The new state is constructed by folding the old dependent Run and using
each translated native edge.target. Neither accountAt nor enteringAt is
restarted, and no target account is supplied by a caller. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def castEdge {V : ResponsibilityLifecycle.Vocabulary} (P : NativeResponsibilityProcess V)
    {first second : ResponsibilityState V} (same : first = second) (edge : P.Edge first) : P.Edge second :=
  same ▸ edge

private theorem castEdge_target {V : ResponsibilityLifecycle.Vocabulary} (P : NativeResponsibilityProcess V)
    {first second : ResponsibilityState V} (same : first = second) (edge : P.Edge first) :
    (castEdge P same edge).target = edge.target := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

structure Translated (first last : ResponsibilityState (Financial.vocabulary input)) where
  private mk ::
  target : ResponsibilityState (vocabulary input depth count)
  run : (process input depth count).Run (state input depth count first) target
  faithful : target = state input depth count last

def foldRun {first last : ResponsibilityState (Financial.vocabulary input)} :
    (Financial.process input).Run first last → Translated input depth count first last
  | .nil => ⟨state input depth count first, .nil, rfl⟩
  | .step prior original =>
      let prefixRun := foldRun prior
      let nextEdge := castEdge (process input depth count) prefixRun.faithful.symm
        (edge input depth count original)
      ⟨nextEdge.target, .step prefixRun.run nextEdge,
        (castEdge_target (process input depth count) prefixRun.faithful.symm
          (edge input depth count original)).trans
            (edge_target input depth count original)⟩

def generated (original : (Financial.process input).GeneratedState) :
    (process input depth count).GeneratedState :=
  let computed := foldRun input depth count original.generated
  ⟨computed.target, computed.run⟩

theorem generated_current (original : (Financial.process input).GeneratedState) :
    (generated input depth count original).current = state input depth count original.current :=
  (foldRun input depth count original.generated).faithful

theorem every_slot_and_history_entry_is_retained (original : (Financial.process input).GeneratedState) :
    (generated input depth count original).current.slots =
      original.current.slots.map (slot input depth count) ∧
    (generated input depth count original).current.history =
      original.current.history.map (lifecycle input depth count) := by
  rw [generated_current]
  exact ⟨rfl, rfl⟩

theorem old_live_slot_is_still_the_same_live_slot
    (original : (Financial.process input).GeneratedState) (index : Nat)
    (old : AdmittedObligation (Financial.vocabulary input))
    (present : original.current.slots[index]? = some (.live old)) :
    (generated input depth count original).current.slots[index]? =
      some (.live (obligation input depth count old)) := by
  rw [(every_slot_and_history_entry_is_retained input depth count original).1]
  simp only [List.getElem?_map, present, Option.map_some, slot]

theorem old_terminal_slot_keeps_its_original_receipt
    (original : (Financial.process input).GeneratedState) (index : Nat)
    (old : TerminalArchive (Financial.vocabulary input))
    (present : original.current.slots[index]? = some (.terminal old)) :
    (generated input depth count original).current.slots[index]? =
      some (.terminal (archive input depth count old)) := by
  rw [(every_slot_and_history_entry_is_retained input depth count original).1]
  simp only [List.getElem?_map, present, Option.map_some, slot]

theorem old_history_remains_a_prefix_of_every_native_extension
    (original : (Financial.process input).GeneratedState)
    {target : ResponsibilityState (vocabulary input depth count)}
    (continued : (process input depth count).Run
      (generated input depth count original).current target) :
    original.current.history.map (lifecycle input depth count) <+: target.history := by
  rw [continued.history_eq,
    (every_slot_and_history_entry_is_retained input depth count original).2]
  exact List.prefix_append _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.generated
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained
