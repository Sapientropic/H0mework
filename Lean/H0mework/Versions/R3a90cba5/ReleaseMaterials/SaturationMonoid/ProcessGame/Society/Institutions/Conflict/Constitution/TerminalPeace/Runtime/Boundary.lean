import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Replay
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Factorization

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open ExposureGuard

noncomputable section

theorem protected_cut_is_the_literal_original_successor :
    endAt Original.seed protectedCut.history = Original.Replay.stopCut := by
  unfold protectedCut
  rw [the_original_installation_writes_its_literal_first_input]
  exact Original.Replay.stop_cut_is_the_original_extended_history

theorem the_original_installation_consumes_no_physical_time :
    (endAt Original.seed protectedCut.history).raw.clock = 4 := by
  rw [protected_cut_is_the_literal_original_successor, Original.Replay.stop_clock, Original.cut_raw]
  rfl

theorem exactly_the_original_harmless_authorized_inputs_are_forwarded
    (prior : WarVisit) (answers : OwnerAnswers Original.seed)
    (input : Reparation.Actual.Input Bool Bool Bool Unit Unit) :
    input ∈ (prior.verdict answers (damageGate Original.community) openProbe input).emitted ↔
      Admitted prior.roster answers prior.history input ∧
        Boundary.Actual.damages (endAt Original.seed prior.history) input Original.community = [] := by
  constructor
  · intro accepted
    exact ⟨((prior.verdict answers (damageGate Original.community) openProbe input).every_emitted_input_is_lawful
      input accepted).1, selected_input_has_no_actual_damage _ input accepted⟩
  · rintro ⟨lawful, harmless⟩
    have emitted := the_original_gate_keeps_every_safe_admissible_input
      (community := Original.community) (check := openProbe) lawful harmless rfl
    unfold Visit.verdict
    rw [emitted]
    exact List.mem_singleton_self _

/-- The unchanged raw request still has its original six-unit material
candidate at this cut. Its installed dispatch takes the original refusal. -/
theorem the_same_six_unit_attack_takes_the_typed_refusal (answers : OwnerAnswers Original.seed) :
    let selected := protectedCut.verdict answers (damageGate Original.community) openProbe Original.attack
    (∃ issue empty continued, selected = .stopped issue empty continued) ∧
    (protectedCut.step answers (damageGate Original.community) openProbe Original.attack).state.stack.balances =
      [(Original.occurrence, Original.balance)] := by
  let harm : Boundary.Actual.DamageAt (endAt Original.seed protectedCut.history) Original.attack Original.community :=
    protected_cut_is_the_literal_original_successor.symm ▸ Original.Replay.candidate_after_stop
  have refused := (an_original_damaging_attempt_is_returned_as_refused
    (roster := protectedCut.roster) (answers := answers) (check := openProbe) harm).2
  have exact : (firstWrite answers).state.stack.balances = [(Original.occurrence, Original.balance)] :=
    (the_revised_visit_keeps_the_exact_original_reparation_portfolio opening answers openProbe stop).trans
      Original.balances_exact
  refine ⟨?_, (the_revised_visit_keeps_the_exact_original_reparation_portfolio protectedCut answers openProbe Original.attack).trans
    (by rwa [← every_installation_reaches_the_same_whole_protected_cut answers])⟩
  rcases refused with stopped | ⟨_, denied, _⟩
  · exact stopped
  · exact (denied.elim (fun hasItems => hasItems (by
      change Boundary.Actual.items (endAt Original.seed protectedCut.history) stop = []
      rw [protected_cut_is_the_literal_original_successor]
      exact the_open_original_recourse_dispatches_a_material_free_stop _ Original.Replay.stop_review))
    (fun noContinuation => by cases noContinuation)).elim

theorem preserving_the_original_liability_alone_does_not_force_the_protected_cut :
    Reparation.Actual.SourceAuthority Original.cut [Original.attack, none] ∧
      Original.Replay.replayState.stack.balances =
        [(Original.occurrence, Original.balance), (Original.Replay.replayed_occurrence, Original.Replay.replayed_balance)] ∧
      ¬ protectedCut.history.IsPrefix Original.Replay.replayHistory := by
  refine ⟨Original.Replay.replayed_authority, Original.Replay.replayed_balances, ?_⟩
  rintro ⟨tail, history⟩
  unfold protectedCut at history
  rw [the_original_installation_writes_its_literal_first_input, Original.Replay.replayHistory, List.append_assoc] at history
  have first := List.append_cancel_left history
  change stop :: tail = [Original.attack, none] at first
  have impossible := (List.cons.inj first).1
  cases impossible

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
