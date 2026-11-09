import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Bypass

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open OriginalSource (Current Write Policy currentAt writeAt)

noncomputable section

private theorem opening_is_policy_independent (left right : Policy) (tick : Nat) (early : tick < 3) :
    currentAt left tick = currentAt right tick ∧ writeAt left tick = writeAt right tick := by
  have slots : tick = 0 ∨ tick = 1 ∨ tick = 2 := by omega
  rcases slots with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem the_external_replay_does_not_read_the_interior_policy (left right : Policy) :
    externalReplay left = externalReplay right := by
  unfold externalReplay
  congr 1
  · funext tick
    by_cases early : tick < 3
    · rw [if_pos early, if_pos early, (opening_is_policy_independent left right tick early).1]
    · rw [if_neg early, if_neg early]
  · funext tick
    by_cases early : tick < 3
    · rw [if_pos early, if_pos early, (opening_is_policy_independent left right tick early).2]
    · rw [if_neg early, if_neg early]

private def emptyInteriorQueue : Policy where
  scheduler := ⟨fun _ _ => .rival, fun _ _ => none, fun _ _ => none, fun _ _ _ => []⟩
  queueLength := fun _ _ => 0
  firstPerson := fun _ _ => false
  replies := fun _ _ _ _ _ _ _ => false

/-- One causal external continuation of the original paid visit, chosen
independently of every protected policy tested against it. -/
def commonExternalReplay : Trace Current Write :=
  externalReplay emptyInteriorQueue

theorem the_same_actual_external_replay_bypasses_every_protected_policy (policy : Policy) :
    commonExternalReplay.current 0 = currentAt policy 0 ∧
    (∀ tick < 3, commonExternalReplay.Check (currentAt policy) (writeAt policy) tick) ∧
    ¬ ∃ index, commonExternalReplay.Factors (currentAt policy) (writeAt policy) index := by
  unfold commonExternalReplay
  rw [the_external_replay_does_not_read_the_interior_policy emptyInteriorQueue policy]
  exact ⟨replay_starts_on_the_original_root policy, replay_keeps_all_checks_before_the_splice policy,
    the_actual_responsibility_preserving_replay_does_not_factor policy⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
