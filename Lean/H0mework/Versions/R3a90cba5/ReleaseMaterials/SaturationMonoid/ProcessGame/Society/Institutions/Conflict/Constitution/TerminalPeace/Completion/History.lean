import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion.Origin

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Renewal

noncomputable section

/-- The finite opening reserves the original recourse, delivery and
native accounting visits before the living law takes its first write. -/
inductive Phase where
  | loss
  | secured
  | delivered
  | accounted
  | living (visit : Visit anchor)

def Phase.whole : Phase → AnyAuthoritativeRootCurrent
  | .loss => Original.state.resident.erase
  | .secured => protectedCut.state.resident.erase
  | .delivered => Settlement.paidBody.resident.erase
  | .accounted => Settlement.settled.resident.erase
  | .living visit => visit.ready.val.state.resident.erase

def advance (policy : Interleaving anchor) : Phase → Phase
  | .loss => .secured
  | .secured => .delivered
  | .delivered => .accounted
  | .accounted => .living (policy.start peace)
  | .living prior => .living (policy.next prior)

def generated (policy : Interleaving anchor) : Nat → Phase
  | 0 => .loss
  | n + 1 => advance policy (generated policy n)

/-- Legality means taking the actual source's next disposition. This
condition specifies the next write and is independent of any safety claim. -/
structure ActualRun (policy : Interleaving anchor) where
  atVisit : Nat → Phase
  starts : atVisit 0 = .loss
  takesNext : ∀ n, atVisit (n + 1) = advance policy (atVisit n)

def realize (policy : Interleaving anchor) : ActualRun policy :=
  ⟨generated policy, rfl, fun _ => rfl⟩

variable (policy : Interleaving anchor)

theorem every_actual_run_is_the_source_run (actual : ActualRun policy) :
    actual.atVisit = generated policy := by
  funext n
  induction n with
  | zero => exact actual.starts
  | succ n exactPrior => rw [actual.takesNext, exactPrior, generated]

theorem every_actual_run_passes_the_same_original_whole_writes (actual : ActualRun policy) :
    (actual.atVisit 0).whole = Original.state.resident.erase ∧
    (actual.atVisit 1).whole = protectedCut.state.resident.erase ∧
    (actual.atVisit 2).whole = Settlement.paidBody.resident.erase ∧
    (actual.atVisit 3).whole = Settlement.settled.resident.erase ∧
    (actual.atVisit 4).whole = peace.val.state.resident.erase := by
  rw [every_actual_run_is_the_source_run policy actual]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem the_generated_future_replays_the_original_compiler (n : Nat) :
    generated policy (n + 4) = .living (policy.run peace n) := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    change advance policy (generated policy (n + 4)) = .living (policy.next (policy.run peace n))
    rw [earlier]
    rfl

def FactorsThroughPeace (actual : ActualRun policy) (tail : Nat → Visit anchor) : Prop :=
  ∀ n, actual.atVisit (n + 4) = .living (tail n)

theorem every_actual_future_has_the_unique_living_suffix (actual : ActualRun policy) :
    ∃! tail : Nat → Visit anchor, FactorsThroughPeace policy actual tail := by
  refine ⟨policy.run peace, ?_, ?_⟩
  · intro n
    rw [every_actual_run_is_the_source_run policy actual, the_generated_future_replays_the_original_compiler]
  · intro other actualTail
    funext n
    have compared := actualTail n
    rw [every_actual_run_is_the_source_run policy actual, the_generated_future_replays_the_original_compiler] at compared
    exact (Phase.living.inj compared).symm

private theorem every_cut_before_the_common_write_is_earlier (actual : ActualRun policy)
    (n : Nat) (early : n < 4) (visit : Visit anchor) :
    actual.atVisit n ≠ .living visit := by
  rw [every_actual_run_is_the_source_run policy actual]
  have possible : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases possible with rfl | rfl | rfl | rfl <;> intro impossible <;> cases impossible

theorem the_same_peace_world_is_the_unique_first_living_write (actual : ActualRun policy) :
    ∃! cut : Nat, actual.atVisit cut = .living (policy.start peace) ∧
      ∀ n < cut, ∀ visit, actual.atVisit n ≠ .living visit := by
  refine ⟨4, ⟨?_, every_cut_before_the_common_write_is_earlier policy actual⟩, ?_⟩
  · rw [every_actual_run_is_the_source_run policy actual]
    rfl
  · intro other witness
    have lower : 4 ≤ other := Nat.le_of_not_gt fun early =>
      every_cut_before_the_common_write_is_earlier policy actual other early _ witness.1
    have upper : other ≤ 4 := Nat.le_of_not_gt fun late =>
      witness.2 4 late (policy.start peace) (by rw [every_actual_run_is_the_source_run policy actual]; rfl)
    exact Nat.le_antisymm upper lower

theorem every_living_cut_records_its_exact_number_of_writes (n : Nat) :
    (policy.run peace n).inputs.length = n := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    obtain ⟨request, selected⟩ := policy.next_has_one_original_position (policy.run peace n)
    change (policy.next (policy.run peace n)).inputs.length = n + 1
    rw [selected, List.length_append, earlier, List.length_singleton]

theorem every_actual_future_has_its_unique_original_input_suffix (actual : ActualRun policy) (n : Nat) :
    ∃! tail : Original.Word, ∃ visit,
      actual.atVisit (n + 4) = .living visit ∧
      anchor ++ [some service] ++ visit.inputs = anchor ++ [some service] ++ tail ∧ tail.length = n := by
  refine ⟨(policy.run peace n).inputs, ⟨policy.run peace n, ?_, rfl,
    every_living_cut_records_its_exact_number_of_writes policy n⟩, ?_⟩
  · rw [every_actual_run_is_the_source_run policy actual, the_generated_future_replays_the_original_compiler]
  · rintro other ⟨visit, observed, whole, _⟩
    rw [every_actual_run_is_the_source_run policy actual, the_generated_future_replays_the_original_compiler] at observed
    rw [← Phase.living.inj observed] at whole
    exact (List.append_cancel_left whole).symm

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion
