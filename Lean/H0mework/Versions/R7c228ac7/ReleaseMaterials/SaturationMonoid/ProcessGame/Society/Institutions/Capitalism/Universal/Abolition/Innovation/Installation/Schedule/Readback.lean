import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Source.Program
open Abolition.Root.Registered

theorem a_prefix_without_a_public_execution_has_no_public_suffix
    (past : List InputAt) (original : ∀ raw ∈ past, beforePublic raw = true) : publicPast past = [] := by
  have cut : sourceCut past = past := by
    simpa only [sourceCut, List.append_nil, List.takeWhile_nil] using
      (List.takeWhile_append_of_pos (l₂ := []) original)
  simp only [publicPast, cut, List.drop_length]

theorem the_empty_actual_public_suffix_selects_only_common_work
    (nature : RequestAt) (past : List InputAt) (empty : publicPast past = []) :
    selected nature past = .execute Control.Scenario.commonWork := by
  unfold selected selectedWith
  rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, empty]
  rfl

theorem the_first_actual_public_execution_recovers_its_original_source_cut
    (oldPast : List InputAt) (word : RawEvent Party Good Bool Nat Unit) (remaining : List InputAt)
    (original : ∀ raw ∈ oldPast, beforePublic raw = true) :
    sourceCut (oldPast ++ .execute word :: remaining) = oldPast ∧
      publicPast (oldPast ++ .execute word :: remaining) = .execute word :: remaining := by
  have cut : sourceCut (oldPast ++ .execute word :: remaining) = oldPast := by
    induction oldPast with
    | nil => rfl
    | cons raw prior inherited =>
        have head := original raw List.mem_cons_self
        have tail := inherited (fun other inside => original other (List.mem_cons_of_mem _ inside))
        simpa only [sourceCut, List.cons_append, List.takeWhile_cons, head, ↓reduceIte,
          List.cons.injEq, true_and] using tail
  exact ⟨cut, by simp only [publicPast, cut, List.drop_left]⟩

theorem the_open_nature_is_submitted_only_after_the_real_preparation
    (nature : RequestAt) (oldPast : List InputAt)
    (original : ∀ raw ∈ oldPast, beforePublic raw = true) :
    selected nature (oldPast ++ .execute Control.Scenario.commonWork :: preparation.map Compile.RawInput.primitive) =
      .primitive nature := by
  have suffix := (the_first_actual_public_execution_recovers_its_original_source_cut oldPast
    Control.Scenario.commonWork (preparation.map Compile.RawInput.primitive) original).2
  unfold selected selectedWith
  rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, suffix]
  simp only [List.length_map, Nat.lt_irrefl, ↓reduceIte]

theorem the_first_submitted_funding_request_is_the_original_signed_issue
    (nature : RequestAt) (oldPast : List InputAt)
    (original : ∀ raw ∈ oldPast, beforePublic raw = true) :
    selected nature (oldPast ++ [.execute Control.Scenario.commonWork]) = .primitive Control.Scenario.issue := by
  have suffix := (the_first_actual_public_execution_recovers_its_original_source_cut oldPast
    Control.Scenario.commonWork [] original).2
  unfold selected selectedWith
  rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, suffix,
    the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
