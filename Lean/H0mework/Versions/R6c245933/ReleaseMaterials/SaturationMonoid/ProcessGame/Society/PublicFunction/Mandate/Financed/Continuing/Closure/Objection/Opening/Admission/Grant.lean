import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable (current : Current) (choice : Choice) (tail : List Action) (legal : Legal current choice)

theorem pair_in_full_word :
    proposalItem current choice ∈ law.rawItems current (candidate current choice ++ tail) ∧
    acceptanceItem current choice ∈ law.rawItems current (candidate current choice ++ tail) := by
  unfold RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ (actual_pair current choice).1,
    List.mem_append_left _ (actual_pair current choice).2⟩

def proposalEvent : ActualCommand base scope current (candidate current choice ++ tail) :=
  (recognize base scope current (candidate current choice ++ tail) ⟨proposalItem current choice, (pair_in_full_word current choice tail).1⟩).get (by
    have accepted := legal _ (actual_pair current choice).1
    simp_all only [law, recognize, proposalItem, proposal, request, Mandate.advance,
      Option.isSome_some, ↓reduceDIte])

def acceptanceEvent : ActualCommand base scope current (candidate current choice ++ tail) :=
  (recognize base scope current (candidate current choice ++ tail) ⟨acceptanceItem current choice, (pair_in_full_word current choice tail).2⟩).get (by
    have accepted := legal _ (actual_pair current choice).2
    simp_all only [law, recognize, acceptanceItem, acceptance, request, Mandate.advance,
      Option.isSome_some, ↓reduceDIte])

theorem proposal_is_read :
    recognize base scope current (candidate current choice ++ tail) ⟨proposalItem current choice, (pair_in_full_word current choice tail).1⟩ =
      some (proposalEvent current choice tail legal) := (Option.some_get _).symm

theorem acceptance_is_read :
    recognize base scope current (candidate current choice ++ tail) ⟨acceptanceItem current choice, (pair_in_full_word current choice tail).2⟩ =
      some (acceptanceEvent current choice tail legal) := (Option.some_get _).symm

private theorem recognized_item
    (item : {item // item ∈ law.rawItems current (candidate current choice ++ tail)})
    (event : ActualCommand base scope current (candidate current choice ++ tail))
    (found : recognize base scope current (candidate current choice ++ tail) item = some event) : event.item = item := by
  unfold recognize at found
  split at found
  · split at found
    · cases found
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  · cases found

theorem pair_items :
    (proposalEvent current choice tail legal).item.val = proposalItem current choice ∧
    (acceptanceEvent current choice tail legal).item.val = acceptanceItem current choice :=
  ⟨congrArg Subtype.val (recognized_item current choice tail _ _ (proposal_is_read current choice tail legal)),
   congrArg Subtype.val (recognized_item current choice tail _ _ (acceptance_is_read current choice tail legal))⟩

theorem pair_kinds_and_order :
    (proposalEvent current choice tail legal).command = .propose choice.candidate ∧
    (acceptanceEvent current choice tail legal).command = .accept ∧
    (proposalEvent current choice tail legal).item.val.index < (acceptanceEvent current choice tail legal).item.val.index ∧
    (proposalEvent current choice tail legal).after.technology = (acceptanceEvent current choice tail legal).item.val.before.technology := by
  have items := pair_items current choice tail legal
  have firstOp := (proposalEvent current choice tail legal).operation
  have secondOp := (acceptanceEvent current choice tail legal).operation
  rw [items.1] at firstOp
  rw [items.2] at secondOp
  have firstTarget := (Operation.revise.inj firstOp).2
  have secondTarget := (Operation.revise.inj secondOp).2
  have firstKind := (proposalEvent current choice tail legal).marked
  have secondKind := (acceptanceEvent current choice tail legal).marked
  rw [← firstTarget] at firstKind
  rw [← secondTarget] at secondKind
  have kinds : (proposalEvent current choice tail legal).command = .propose choice.candidate ∧
      (acceptanceEvent current choice tail legal).command = .accept :=
    ⟨(Option.some.inj firstKind).symm, (Option.some.inj secondKind).symm⟩
  refine ⟨kinds.1, kinds.2, ?_, ?_⟩
  · rw [items.1, items.2]; simp only [proposalItem, acceptanceItem]; omega
  · simp only [ActualCommand.after, items.1, items.2]; rfl

include legal in
theorem legal_pair_has_an_actual_grant : (grantsAt base scope current (candidate current choice ++ tail)).isEmpty = false := by
  have first : proposalEvent current choice tail legal ∈ commandsAt base scope current (candidate current choice ++ tail) :=
    List.mem_filterMap.mpr ⟨_, List.mem_attach _ _, proposal_is_read current choice tail legal⟩
  have second : acceptanceEvent current choice tail legal ∈ commandsAt base scope current (candidate current choice ++ tail) :=
    List.mem_filterMap.mpr ⟨_, List.mem_attach _ _, acceptance_is_read current choice tail legal⟩
  by_contra empty
  have nil : grantsAt base scope current (candidate current choice ++ tail) = [] := by simpa using empty
  unfold grantsAt at nil
  have branch := List.flatMap_eq_nil_iff.mp nil _ first
  have absent := List.filterMap_eq_nil_iff.mp branch _ second
  have facts := pair_kinds_and_order current choice tail legal
  split at absent
  · split at absent
    · cases absent
    · rename_i denied
      exact denied ⟨facts.2.2.1, facts.2.2.2⟩
  · simp_all

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission
