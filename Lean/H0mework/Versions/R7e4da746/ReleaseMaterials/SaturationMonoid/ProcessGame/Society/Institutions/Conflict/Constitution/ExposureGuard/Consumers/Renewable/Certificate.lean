import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Round
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window timelyUses)
open Installed (scope)
open Quantities

noncomputable section

private theorem due_append (window : W) (first second : Word)
    (paid : Due.Checked start window first) (later : Due.Checked start (window.run first) second) :
    Due.Checked start window (first ++ second) := by
  induction first generalizing window with
  | nil => exact later
  | cons input rest prior =>
    exact ⟨paid.1, prior (window.write input) paid.2 later⟩

theorem original_window (n : Nat) : (Window.at start).run (history n) = Window.at (run n) := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [history, Window.run_append, prior]
    exact the_paid_cycle_opens_the_actual_next_window n

theorem history_paid (n : Nat) : MandateExit.PaidAt start [] (history n) := by
  change Due.Checked start (Window.at start) (history n)
  induction n with
  | zero => trivial
  | succ n prior =>
    rw [history]
    refine due_append (Window.at start) (history n) (wordAt (run n)) prior ?_
    rw [original_window n]
    exact Due.of_original_civilian_check start (Window.at (run n)) id true _ (paid_round n).own

private theorem standing_through_word (people : List Bool) (before word : Word) :
    Exit.StandingAlong people (Execution.endAt start before) word := by
  induction word generalizing before with
  | nil => exact fun person _ => standing before person
  | cons input rest prior =>
    refine ⟨fun person _ => standing before person, ?_⟩
    change Exit.StandingAlong people (Execution.endAt (Execution.endAt start before) [input]) rest
    rw [← Execution.endAt_append]
    exact prior (before ++ [input])

private theorem word_inventory (n : Nat) :
    Execution.inventory (run n) (wordAt (run n)) = Boundary.Actual.items (readyCut (run n)) service := by
  unfold wordAt
  rw [Execution.inventory_append, (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain (run n)).2.2.1]
  rfl

private theorem full_need_address (n : Nat) (cell : Cell)
    (listed : cell ∈ Exit.needCells start (id : Bool → Bool) [] (history n)) :
    ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  have cells := List.mem_dedup.mp listed
  let people := Exit.roster start (id : Bool → Bool) [] (history n)
  change cell ∈ Exit.needsAt start people ++ Exit.needsAt (Execution.endAt start (history n)) people at cells
  rw [run_is_its_own_native_fold n] at cells
  rcases List.mem_append.mp cells with original | current
  · unfold Exit.needsAt at original
    rw [start_input] at original
    exact native_cell _ _ cell original
  · unfold Exit.needsAt at current
    rw [(stage n).input] at current
    exact native_cell _ _ cell current

theorem live_certificate (n : Nat) :
    MandateExit.LiveCertificate start [] (history n) (id : Bool → Bool) base scope noControl (wordAt (run n)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨standing_through_word _ (history n) _, ?_, ?_, ?_⟩
    · rw [run_is_its_own_native_fold n, word_inventory]
      exact fun item listed => ⟨List.not_mem_nil, no_other_bearer_asked n item listed⟩
    · intro cell listed
      obtain ⟨person, rfl⟩ := full_need_address n cell listed
      have paid := original_renewal_pays_each_person n person
      unfold Window.timely at paid
      rw [service_window_origin n] at paid
      rw [run_is_its_own_native_fold n]
      exact paid
    · rw [run_is_its_own_native_fold n]
      exact paid_round n
  · rw [run_is_its_own_native_fold n, word_inventory]
    exact each_item_title_free n
  · exact history_paid (n + 1)

theorem live_available (n : Nat) :
    MandateExit.LiveAvailable start [] (history n) (id : Bool → Bool) base scope noControl :=
  ⟨wordAt (run n), live_certificate n⟩

theorem every_physical_horizon_has_a_same_root_paid_independent_exit (horizon : ℚ) :
    ∃ n, horizon < (Execution.endAt start (history n)).raw.clock ∧
      MandateExit.PaidAt start [] (history n) ∧
      MandateExit.LiveCertificate start [] (history n) (id : Bool → Bool) base scope noControl (wordAt (run n)) ∧
      Recorded start (history n) := by
  obtain ⟨n, earlier⟩ := exists_nat_gt horizon
  refine ⟨n, ?_, history_paid n, live_certificate n, record start _⟩
  rw [run_is_its_own_native_fold n, actual_clock]
  linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
