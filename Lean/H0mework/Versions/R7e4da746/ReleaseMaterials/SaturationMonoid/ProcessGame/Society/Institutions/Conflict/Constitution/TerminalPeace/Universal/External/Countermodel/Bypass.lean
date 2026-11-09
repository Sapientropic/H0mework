import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Repetition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Source.Program
open Conflict.Consumers.Evolving (levy)
open OriginalSource (Current Write Policy currentAt writeAt NoActualDamage)

noncomputable section

def oldCurrent (tick : Nat) : Current :=
  ((visitAt tick).resident.erase, (before (historyAt tick)).raw.clock)

def oldWrite (tick : Nat) : Write :=
  ((visitAt (tick + 1)).resident.erase, Boundary.Actual.items (before (historyAt tick)) (inputAt tick))

/-- The trace consumes the three original settlement writes before the
unregulated compiler takes its next input from the same paid visit. -/
def externalReplay (policy : Policy) : Trace Current Write where
  current := fun tick => if tick < 3 then currentAt policy tick else oldCurrent (tick - 3)
  effect := fun tick => some (if tick < 3 then writeAt policy tick else oldWrite (tick - 3))

theorem replay_ordinal (policy : Policy) (tick : Nat) : (externalReplay policy).ordinal tick = tick := by
  induction tick with
  | zero => rfl
  | succ tick earlier =>
    change (externalReplay policy).ordinal tick + 1 = tick + 1
    rw [earlier]

theorem replay_starts_on_the_original_root (policy : Policy) :
    (externalReplay policy).current 0 = currentAt policy 0 :=
  rfl

theorem replay_consumes_the_same_paid_opening (policy : Policy) :
    (externalReplay policy).current 3 = currentAt policy 3 :=
  rfl

theorem replay_keeps_all_checks_before_the_splice (policy : Policy) (tick : Nat) (early : tick < 3) :
    (externalReplay policy).Check (currentAt policy) (writeAt policy) tick := by
  have wrote : (externalReplay policy).effect tick = some (writeAt policy tick) := by
    change some (if tick < 3 then writeAt policy tick else oldWrite (tick - 3)) = _
    rw [if_pos early]
  unfold Trace.Check
  rw [wrote, replay_ordinal]
  refine ⟨rfl, ?_⟩
  by_cases earlier : tick + 1 < 3
  · change (if tick + 1 < 3 then currentAt policy (tick + 1) else oldCurrent (tick + 1 - 3)) = _
    rw [if_pos earlier]
  · have exactCut : tick + 1 = 3 := by omega
    rw [exactCut]
    exact replay_consumes_the_same_paid_opening policy

theorem replay_keeps_the_legacy_physical_clock (policy : Policy) (tick : Nat) (late : 3 ≤ tick) :
    ((externalReplay policy).current tick).2 = 4 := by
  change (if tick < 3 then currentAt policy tick else oldCurrent (tick - 3)).2 = 4
  rw [if_neg (not_lt_of_ge late)]
  exact physical_clock_is_four_at_every_external_visit (tick - 3)

theorem the_first_external_mismatch_is_the_next_physical_write (policy : Policy) :
    ¬ (externalReplay policy).Check (currentAt policy) (writeAt policy) 3 := by
  intro checked
  have emitted : (externalReplay policy).effect 3 = some (oldWrite 0) := rfl
  unfold Trace.Check at checked
  rw [emitted, replay_ordinal] at checked
  have clocks := congrArg Prod.snd checked.2
  have peaceful : (currentAt policy 4).2 = 5 :=
    congrArg (fun raw : Original.Raw => raw.clock) Completion.the_first_peace_write_reads_the_paid_current
  rw [replay_keeps_the_legacy_physical_clock policy 4 (by omega), peaceful] at clocks
  norm_num at clocks

theorem the_actual_responsibility_preserving_replay_does_not_factor (policy : Policy) :
    ¬ ∃ index, (externalReplay policy).Factors (currentAt policy) (writeAt policy) index := by
  rintro ⟨_, factor⟩
  exact the_first_external_mismatch_is_the_next_physical_write policy
    (((externalReplay policy).checks_of_factor _ _ factor).2 3)

theorem replay_writes_unbounded_original_ordinals (policy : Policy) :
    (externalReplay policy).Progress := by
  intro cut
  exact ⟨cut, (replay_ordinal policy cut).ge⟩

theorem replay_cannot_cross_a_new_physical_hour (policy : Policy) :
    ¬ ∃ tick ≥ 3, 4 < ((externalReplay policy).current tick).2 := by
  rintro ⟨tick, late, advanced⟩
  rw [replay_keeps_the_legacy_physical_clock policy tick late] at advanced
  exact (lt_irrefl _ advanced)

theorem each_external_cycle_writes_its_actual_six_unit_assault (policy : Policy) (n : Nat) :
    let item : Original.Item := ⟨0, (roundCut n).raw, levy⟩
    (externalReplay policy).effect (3 + 4 * n) =
      some ((visitAt (4 * n + 1)).resident.erase, [item]) ∧
      Reparation.loss Supply.physical Original.community item (false, true, false) = 6 := by
  dsimp only
  constructor
  · have arithmetic : 3 + 4 * n - 3 = 4 * n := by omega
    change some (if 3 + 4 * n < 3 then writeAt policy (3 + 4 * n) else oldWrite (3 + 4 * n - 3)) = _
    rw [if_neg (show ¬ 3 + 4 * n < 3 by omega), arithmetic]
    unfold oldWrite
    rw [starts_with_levy, original_levy_items (recurring_cuts_use_the_same_original_material n)]
  · rw [(recurring_cuts_use_the_same_original_material n).physical]
    decide +kernel

theorem external_assaults_keep_reopening_after_arbitrarily_late_visits (policy : Policy) (start : Nat) :
    ∃ tick ≥ start, ¬ NoActualDamage ((externalReplay policy).effect tick) := by
  refine ⟨3 + 4 * start, by omega, ?_⟩
  have actual := each_external_cycle_writes_its_actual_six_unit_assault policy start
  rw [actual.1]
  intro noDamage
  have absent := noDamage _ (List.mem_singleton_self _) (false, true, false)
  rw [actual.2] at absent
  norm_num at absent

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
