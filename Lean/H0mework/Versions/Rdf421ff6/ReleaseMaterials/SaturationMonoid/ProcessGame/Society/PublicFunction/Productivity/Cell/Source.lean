import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Local

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program

def initial : Current where
  stock := fun actor good =>
    if actor = 0 then match good with
      | .seed => 1 | .feed => 24 | .life => 3 | .spare => 3
      | .energy => 8 | .labor => 8 | .waste => 0
    else if actor = 1 ∨ actor = 2 then match good with
      | .life | .spare => 3 | _ => 0
    else if actor = 3 then match good with
      | .feed => 40 | .energy | .labor => 12 | _ => 0
    else 0
  claims := fun _ _ _ => 0
  technology := (false, false)
  clock := 0
  round := 0

def task : PublicTaskSpec Party Good :=
  ⟨[⟨0, [(.life, 1)], .necessity⟩, ⟨0, [(.spare, 1)], .maintenance⟩,
    ⟨1, [(.life, 1)], .necessity⟩, ⟨1, [(.spare, 1)], .maintenance⟩,
    ⟨2, [(.life, 1)], .necessity⟩, ⟨2, [(.spare, 1)], .maintenance⟩], 1, 12, by decide +kernel⟩

def source : OutstandingSource Party Good Port Technology Unit where
  seed := {
    law := law
    initial := initial
    task := task
    actionsAt := fun _ => []
    budget := 0
    original := original
    refused := by
      let before := (law.execute (law.next initial []) 0 (original.take 8)).final
      refine ⟨⟨8, before, production 0⟩, ?_, ?_⟩
      · simp [before, original, RawLaw.rawItems, RawLaw.execute]
      · decide +kernel }
  positive := by
    intro slot inside
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact ⟨(.life, 1), by decide, by decide⟩
            | exact ⟨(.spare, 1), by decide, by decide⟩
  completionReport := fun current => .original current (Feedback.respond current).word

theorem raw_current_frame (ordinal : Nat) :
    source.currentAt ordinal = (source.frameAt ordinal).raw := (source.canonical_frame ordinal).1

theorem zero_financial_genesis : source.input.initial.claims = fun _ _ _ => 0 := rfl

theorem original_service_paid : source.pendingSlots (source.frameAt 2).payments = [] := by
  decide +kernel

theorem continuation_is_actual (ordinal : Nat) (started : 2 ≤ ordinal) :
    (source.actualExecution (ordinal - 1)).submitted = (Feedback.respond (source.currentAt ordinal)).word := by
  have same : ordinal - 1 + 1 = ordinal := by omega
  rw [source.actual_execution_word, same, ← (source.canonical_frame ordinal).2]
  have complete := source.completion_persists 2 (ordinal - 2) original_service_paid
  exact source.completed_word_is_source_continuation ordinal 0 started
    (by simpa only [Nat.add_sub_of_le started] using complete) rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
