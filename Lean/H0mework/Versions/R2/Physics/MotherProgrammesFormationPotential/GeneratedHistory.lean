import H0mework.Versions.R2.Physics.MotherProgrammesFormationPotential.GeneratedState

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory

open MotherFamilyOccurrence PotentialSourceFormation

noncomputable section

def emittedHistory : ℕ → List Points
  | 0 => []
  | index + 1 => emittedHistory index ++ [emit (stateAt index).1]

theorem history_succ (index : ℕ) :
    emittedHistory (index + 1) = emittedHistory index ++ [emit (stateAt index).1] := rfl

theorem history_length (index : ℕ) : (emittedHistory index).length = index := by
  induction index with
  | zero => rfl
  | succ index induction => simp [emittedHistory, induction]

theorem history_prefix (index : ℕ) : (emittedHistory index).IsPrefix (emittedHistory (index + 1)) :=
  ⟨[emit (stateAt index).1], rfl⟩

theorem history_prefix_of_le {earlier later : ℕ} (bound : earlier ≤ later) :
    (emittedHistory earlier).IsPrefix (emittedHistory later) := by
  induction later generalizing earlier with
  | zero =>
      have zero : earlier = 0 := by omega
      subst earlier
      exact ⟨[], List.append_nil _⟩
  | succ later induction =>
      by_cases before : earlier ≤ later
      · exact (induction before).trans (history_prefix later)
      · have same : earlier = later + 1 := by omega
        subst earlier
        exact ⟨[], List.append_nil _⟩

theorem points_from_full_history (index : ℕ) :
    (stateAt index).2 = initialPoints + (emittedHistory index).sum := by
  induction index with
  | zero => simp [stateAt, initialState, emittedHistory]
  | succ index induction =>
      rw [points_succ, induction, history_succ, List.sum_append]
      simp only [List.sum_cons, List.sum_nil, add_zero]
      exact add_assoc _ _ _

/-- Recovery uses complete point differences. It applies to every lawful
displacement, including ones that the deterministic emitter does not select. -/
theorem event_delta_recovered (before : State) (displacement : Points) :
    (act before displacement).2 - before.2 = displacement := by
  change (before.2 + displacement) - before.2 = displacement
  abel

theorem event_reconstructed (before after : State) (native : after.1 = targetVisit before.1) :
    act before (after.2 - before.2) = after := by
  apply Prod.ext
  · exact native.symm
  · change before.2 + (after.2 - before.2) = after.2
    abel

theorem full_event_fibre (before after : State) :
    (∃! displacement : Points, act before displacement = after) ↔ after.1 = targetVisit before.1 := by
  constructor
  · rintro ⟨displacement, generated, _⟩
    exact (congrArg Prod.fst generated).symm
  · intro native
    refine ⟨after.2 - before.2, event_reconstructed before after native, ?_⟩
    intro displacement generated
    exact (event_delta_recovered before displacement).symm.trans
      (congrArg (fun state : State => state.2 - before.2) generated)

theorem emitted_recovered (index : ℕ) :
    (stateAt (index + 1)).2 - (stateAt index).2 = emit (stateAt index).1 :=
  event_delta_recovered (stateAt index) (emit (stateAt index).1)

theorem state_spatial_zero (index : ℕ) : remainders (stateAt index).2 = 0 := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rw [points_succ, remainders_increment, induction, emit_spatial, add_zero]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory
