import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Uniform
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (ActualAndIndependent OriginalNeedFloor)
open OriginalSource (Current Write Policy currentAt writeAt)

noncomputable section

abbrev afterRaidCut := before (historyAt 4)
abbrev afterRaidVisit := visitAt 4
abbrev afterRaidOrigin := afterRaidCut.raw

theorem the_recovered_stock_can_pay_the_same_recipe : TerminalPeace.Supply.Stocked afterRaidOrigin := by
  have raw : afterRaidOrigin = Original.snapshot 117 107 :=
    (recurring_cuts_use_the_same_original_material 1).physical
  rw [raw]
  intro person
  cases person <;> decide +kernel

private abbrev recipe := TerminalPeace.Supply.revisedInput
private abbrev persons : List Bool := [false, true]
abbrev RaidMenus := Runtime.Menus Bool Bool Bool Unit Unit

/-- Three common writes, then the old four-input raid and return. Every
later projection reads the supplied runtime on that same retained account. -/
def afterRaidTrace (menus : RaidMenus) : Trace Current Write where
  current := fun visit => if visit < 7 then commonExternalReplay.current visit else
    Runtime.currentAt afterRaidVisit recipe afterRaidOrigin persons menus (visit - 7)
  effect := fun visit => if visit < 7 then commonExternalReplay.effect visit else
    some (Runtime.writeAt afterRaidVisit recipe afterRaidOrigin persons menus (visit - 7))

theorem raid_trace_reads_its_original_prefix (menus : RaidMenus) (visit : Nat) (early : visit < 7) :
    (afterRaidTrace menus).current visit = commonExternalReplay.current visit := by
  change (if visit < 7 then commonExternalReplay.current visit else _) = _
  exact if_pos early

theorem raid_trace_writes_its_original_prefix (menus : RaidMenus) (visit : Nat) (early : visit < 7) :
    (afterRaidTrace menus).effect visit = commonExternalReplay.effect visit := by
  change (if visit < 7 then commonExternalReplay.effect visit else _) = _
  exact if_pos early

theorem raid_trace_reads_the_paid_tail (menus : RaidMenus) (n : Nat) :
    (afterRaidTrace menus).current (7 + n) =
      Runtime.currentAt afterRaidVisit recipe afterRaidOrigin persons menus n := by
  change (if 7 + n < 7 then commonExternalReplay.current (7 + n) else
    Runtime.currentAt afterRaidVisit recipe afterRaidOrigin persons menus (7 + n - 7)) = _
  rw [if_neg (by omega : ¬ 7 + n < 7), show 7 + n - 7 = n by omega]

theorem raid_trace_writes_the_paid_tail (menus : RaidMenus) (n : Nat) :
    (afterRaidTrace menus).effect (7 + n) =
      some (Runtime.writeAt afterRaidVisit recipe afterRaidOrigin persons menus n) := by
  change (if 7 + n < 7 then commonExternalReplay.effect (7 + n) else
    some (Runtime.writeAt afterRaidVisit recipe afterRaidOrigin persons menus (7 + n - 7))) = _
  rw [if_neg (by omega : ¬ 7 + n < 7), show 7 + n - 7 = n by omega]

theorem raid_trace_enters_the_same_whole_cut (menus : RaidMenus) :
    (afterRaidTrace menus).current 7 = commonExternalReplay.current 7 :=
  rfl

private theorem raid_trace_width (menus : RaidMenus) (visit : Nat) : (afterRaidTrace menus).width visit = 1 := by
  unfold Trace.width
  by_cases early : visit < 7
  · rw [raid_trace_writes_its_original_prefix menus visit early]
    rfl
  · let n := visit - 7
    have position : visit = 7 + n := by omega
    rw [position, raid_trace_writes_the_paid_tail]

theorem raid_trace_ordinal (menus : RaidMenus) (visit : Nat) : (afterRaidTrace menus).ordinal visit = visit := by
  induction visit with
  | zero => rfl
  | succ visit earlier => rw [Trace.ordinal, earlier, raid_trace_width]

private theorem common_replay_ordinal (n : Nat) : commonExternalReplay.ordinal n = n :=
  replay_ordinal _ n

theorem raid_trace_starts_on_the_original_root (menus : RaidMenus) (policy : Policy) :
    (afterRaidTrace menus).current 0 = currentAt policy 0 :=
  (raid_trace_reads_its_original_prefix menus 0 (by omega)).trans
    (the_same_actual_external_replay_bypasses_every_protected_policy policy).1

theorem raid_trace_keeps_checks_before_the_original_mismatch (menus : RaidMenus) (policy : Policy)
    (visit : Nat) (early : visit < 3) :
    (afterRaidTrace menus).Check (currentAt policy) (writeAt policy) visit := by
  have same := (the_same_actual_external_replay_bypasses_every_protected_policy policy).2.1 visit early
  simpa only [Trace.Check, raid_trace_writes_its_original_prefix menus visit (by omega),
    raid_trace_reads_its_original_prefix menus visit (by omega),
    raid_trace_reads_its_original_prefix menus (visit + 1) (by omega),
    raid_trace_ordinal, common_replay_ordinal] using same

theorem raid_trace_keeps_the_first_original_mismatch (menus : RaidMenus) (policy : Policy) :
    ¬ (afterRaidTrace menus).Check (currentAt policy) (writeAt policy) 3 := by
  intro checked
  have written : (afterRaidTrace menus).effect 3 = some (oldWrite 0) := rfl
  unfold Trace.Check at checked
  rw [written, raid_trace_ordinal] at checked
  have clocks := congrArg Prod.snd checked.2
  have old : ((afterRaidTrace menus).current 4).2 = 4 :=
    physical_clock_is_four_at_every_external_visit 1
  have peace : (currentAt policy 4).2 = 5 :=
    congrArg (fun raw : Original.Raw => raw.clock) Completion.the_first_peace_write_reads_the_paid_current
  rw [old, peace] at clocks
  norm_num at clocks

theorem the_paid_tail_cannot_erase_the_original_external_mismatch (menus : RaidMenus) (policy : Policy) :
    ¬ ∃ index, (afterRaidTrace menus).Factors (currentAt policy) (writeAt policy) index := by
  rintro ⟨_, factor⟩
  exact raid_trace_keeps_the_first_original_mismatch menus policy
    (((afterRaidTrace menus).checks_of_factor _ _ factor).2 3)

theorem the_raid_tail_keeps_both_original_rows (menus : RaidMenus) (n : Nat) :
    (Runtime.run afterRaidVisit recipe afterRaidOrigin persons menus n).state.stack.balances =
      [(Original.occurrence, Settlement.clearedBalance), roundRow 0] :=
  (Runtime.every_actual_visit_keeps_the_original_rows afterRaidVisit recipe afterRaidOrigin persons menus n).trans
    (every_repeated_assault_keeps_the_first_paid_row_and_all_new_rows 1)

theorem the_raid_tail_reads_both_original_rows (menus : RaidMenus) (n : Nat)
    (row : Row) (old : row ∈ [(Original.occurrence, Settlement.clearedBalance), roundRow 0]) :
    let current := (Runtime.run afterRaidVisit recipe afterRaidOrigin persons menus n).state
    ∃ entry, current.read entry = .inr row := by
  apply Reparation.Actual.StateAt.every_balance_is_a_row_of_the_current
  rwa [the_raid_tail_keeps_both_original_rows]

theorem the_raid_trace_inherits_the_paid_tail_clock (menus : RaidMenus)
    (paid : Runtime.ClockCofinal afterRaidVisit recipe afterRaidOrigin persons menus) :
    ∀ start bound, ∃ visit ≥ start, bound < ((afterRaidTrace menus).current visit).2 := by
  intro start bound
  obtain ⟨n, past, beyond⟩ := paid start bound
  refine ⟨7 + n, by omega, ?_⟩
  rw [raid_trace_reads_the_paid_tail]
  exact beyond

/-- One external raid is actually filed before the same available
productive menu begins paying every subsequent physical hour. -/
def cofinalExternalReplay : Trace Current Write :=
  afterRaidTrace Runtime.OriginalProgramme.menus

theorem the_external_raid_is_followed_by_real_cofinal_paid_time :
    ∀ start bound, ∃ visit ≥ start, bound < (cofinalExternalReplay.current visit).2 :=
  the_raid_trace_inherits_the_paid_tail_clock Runtime.OriginalProgramme.menus
    (Runtime.OriginalProgramme.the_original_paid_hours_are_cofinal_from_each_real_cut
      afterRaidVisit the_recovered_stock_can_pay_the_same_recipe)

theorem the_after_raid_tail_clock_is_exact (n : Nat) :
    (cofinalExternalReplay.current (7 + n)).2 = 4 + (n : ℚ) := by
  change ((afterRaidTrace Runtime.OriginalProgramme.menus).current (7 + n)).2 = _
  rw [raid_trace_reads_the_paid_tail]
  exact (Runtime.OriginalProgramme.the_cofinal_clock_is_the_literal_original_paid_hour
    afterRaidVisit the_recovered_stock_can_pay_the_same_recipe n).trans
    (congrArg (fun clock : ℚ => clock + (n : ℚ)) (physical_clock_is_four_at_every_external_visit 4))

theorem each_external_tail_visit_pays_and_keeps_both_independent_exits (n : Nat) :
    let menus := Runtime.OriginalProgramme.menus
    let attempt := Runtime.eventAt afterRaidVisit recipe afterRaidOrigin persons menus n
    (∃ position : Fin attempt.offers.length,
      let word := attempt.offers[position]
      Supply.Period recipe afterRaidOrigin attempt.before.raw persons word ∧
        attempt.items = recipe.law.rawItems attempt.before.raw word) ∧
    ∀ person : Bool, ∃ word ∈ attempt.offers,
      ActualAndIndependent recipe attempt.before.raw word ∧
        OriginalNeedFloor recipe afterRaidOrigin attempt.before.raw [person] word ∧
        OriginalNeedFloor recipe attempt.before.raw attempt.before.raw [person] word := by
  let menus := Runtime.OriginalProgramme.menus
  let attempt := Runtime.eventAt afterRaidVisit recipe afterRaidOrigin persons menus n
  have ready := Runtime.OriginalProgramme.every_due_visit_and_each_personal_exit_are_generated
    afterRaidVisit the_recovered_stock_can_pay_the_same_recipe n
  obtain ⟨position, paid, items, _⟩ := attempt.accepted_effect ready.1
  exact ⟨⟨position, paid, items⟩, fun person =>
    Runtime.a_ready_cut_has_a_source_generated_personal_exit afterRaidVisit recipe afterRaidOrigin persons menus n
      ready person (by cases person <;> decide)⟩

theorem one_physically_cofinal_external_replay_retains_the_original_mismatch (policy : Policy) :
    cofinalExternalReplay.current 0 = currentAt policy 0 ∧
    (∀ visit < 3, cofinalExternalReplay.Check (currentAt policy) (writeAt policy) visit) ∧
    ¬ cofinalExternalReplay.Check (currentAt policy) (writeAt policy) 3 := by
  let menus := Runtime.OriginalProgramme.menus
  exact ⟨raid_trace_starts_on_the_original_root menus policy,
    raid_trace_keeps_checks_before_the_original_mismatch menus policy,
    raid_trace_keeps_the_first_original_mismatch menus policy⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

-- Its exact dependent row type is too deep for the automatic premise index.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "the_raid_tail_reads_both_original_rows"
