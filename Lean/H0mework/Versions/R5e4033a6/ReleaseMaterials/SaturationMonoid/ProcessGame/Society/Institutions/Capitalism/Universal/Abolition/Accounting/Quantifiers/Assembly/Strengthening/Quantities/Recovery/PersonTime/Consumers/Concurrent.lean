import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consumers.OriginalLife
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Residual
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TightBound
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Reader.Stream

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consumers

open Abolition.Root Abolition.Root.Registered
open Quantities.Consumers (lifeSource firstPaidPeriod lifePeriod
  the_original_period_uses_the_actual_food_stock
  the_original_full_period_pays_life_and_finishes_its_native_work)
open Innovation.Contribution.Pricing.Consumers.Actual
  (the_repair_really_funds_both_original_lives the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open OriginalLife Intervals

noncomputable section

def concurrentMeter : Meter.{0} lifeSource where
  OccupiedAt := fun script person phase opens performs closes =>
    PLift (script = firstPaidPeriod ∧ (phase = .exposure ∨ person = false ∧ phase = .recovery) ∧
      opens.val = index person ∧ performs.val = index person ∧ closes.val = index person)

private def measured (person : Bool) (phase : Phase)
    (kind : phase = .exposure ∨ person = false ∧ phase = .recovery) :
    Observation lifeSource concurrentMeter firstPaidPeriod where
  person := person
  phase := phase
  opens := slot person
  performs := slot person
  closes := slot person
  operation := own_action person
  measured := ⟨rfl, kind, rfl, rfl, rfl⟩
  withinSource := (starts_at_original_clock person).ge
  starts := le_rfl
  enacted := by
    rw [starts_at_original_clock, commits_at_original_clock]
    exact Execution.the_actual_script_never_runs_the_clock_backwards _ _
  finishes := le_rfl

private def whole : Span :=
  ⟨lifeSource.raw.clock, (Execution.endAt lifeSource firstPaidPeriod).raw.clock,
    Execution.the_actual_script_never_runs_the_clock_backwards _ _⟩

private theorem same_span (person : Bool) (phase : Phase) (kind) :
    (measured person phase kind).span = whole := by
  unfold Observation.span whole
  change Span.mk (opensAt lifeSource firstPaidPeriod (slot person))
    (commitsAt lifeSource firstPaidPeriod (slot person)) _ = _
  simp only [starts_at_original_clock, commits_at_original_clock]

private def firstExposure := measured false .exposure (.inl rfl)
private def secondExposure := measured true .exposure (.inl rfl)
private def simultaneousRecovery := measured false .recovery (.inr ⟨rfl, rfl⟩)
private def reports := [firstExposure, secondExposure, simultaneousRecovery]

private theorem one_hour : length [whole] = 1 :=
  (length_one whole).trans the_original_full_period_pays_life_and_finishes_its_native_work.2

private theorem meter_spans_original_hour
    (observation : Observation lifeSource concurrentMeter firstPaidPeriod) :
    observation.span = whole := by
  obtain ⟨_, _, opens, _, closes⟩ := observation.measured.down
  have start : observation.opens = slot observation.person := Fin.ext opens
  have finish : observation.closes = slot observation.person := Fin.ext closes
  unfold Observation.span whole
  simp only [start, finish, starts_at_original_clock, commits_at_original_clock]

theorem each_concurrent_reading_has_original_clock_values
    (observation : Observation lifeSource concurrentMeter firstPaidPeriod) :
    observation.span.start = 4 ∧ observation.span.finish = 5 := by
  rw [meter_spans_original_hour observation]
  have opening : lifeSource.raw.clock = 4 := by
    rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    decide +kernel
  have one := the_original_full_period_pays_life_and_finishes_its_native_work.2
  change (Execution.endAt lifeSource firstPaidPeriod).raw.clock - lifeSource.raw.clock = 1 at one
  refine ⟨opening, ?_⟩
  change (Execution.endAt lifeSource firstPaidPeriod).raw.clock = 5
  linarith only [opening, one]

def concurrentSourceStream : SourceStream lifeSource concurrentMeter firstPaidPeriod where
  emitted := reports
  exhaustive := by
    intro original
    obtain ⟨_, kind, opens, performs, closes⟩ := original.measured.down
    have key : original.stamp =
        ⟨original.person, original.phase, slot original.person, slot original.person, slot original.person⟩ := by
      have opening : original.opens = slot original.person := Fin.ext opens
      have work : original.performs = slot original.person := Fin.ext performs
      have finish : original.closes = slot original.person := Fin.ext closes
      simp only [Observation.stamp, opening, work, finish]
    rcases kind with exposure | ⟨who, recovery⟩
    · cases who : original.person
      · exact ⟨firstExposure, List.mem_cons_self, by rw [key, who, exposure]; rfl⟩
      · exact ⟨secondExposure, List.mem_cons_of_mem _ List.mem_cons_self,
          by rw [key, who, exposure]; rfl⟩
    · exact ⟨simultaneousRecovery, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by rw [key, who, recovery]; rfl⟩

theorem each_original_person_has_exactly_one_hour_of_source_exposure (person : Bool) :
    originalExposure lifeSource concurrentMeter firstPaidPeriod person = 1 := by
  apply Eq.trans _ one_hour
  apply length_eq_of_same_cover
  ext time
  change time ∈ cover (spansFor (roster lifeSource concurrentMeter firstPaidPeriod) person
    (fun phase => decide (phase = .exposure))) ↔ time ∈ cover [whole]
  rw [roster_covers_exactly_the_source_occupations]
  constructor
  · rintro ⟨observation, _, _, occurs⟩
    exact ⟨whole, List.mem_cons_self, meter_spans_original_hour observation ▸ occurs⟩
  · rintro ⟨span, listed, occurs⟩
    rcases List.mem_singleton.mp listed with rfl
    exact ⟨measured person .exposure (.inl rfl), rfl, rfl,
      (same_span person .exposure (.inl rfl)).symm ▸ occurs⟩

/-- Both measured people use their own original event slots. Concurrent
persons each accrue an hour, while simultaneous uses by one person
occupy one hour of that person's clock. -/
theorem the_two_original_people_each_occupy_their_own_hour :
    phaseHours reports false .exposure = 1 ∧
      phaseHours reports true .exposure = 1 ∧
      exposureAndRecovery reports false = 1 ∧ conversion reports false = some 1 ∧
      Settled lifeSource firstPaidPeriod := by
  have first : phaseHours reports false .exposure = 1 := by
    change length [firstExposure.span] = 1
    rw [firstExposure, same_span]
    exact one_hour
  have second : phaseHours reports true .exposure = 1 := by
    change length [secondExposure.span] = 1
    rw [secondExposure, same_span]
    exact one_hour
  have combined : exposureAndRecovery reports false = 1 := by
    change length [firstExposure.span, simultaneousRecovery.span] = 1
    rw [firstExposure, simultaneousRecovery, same_span, same_span]
    exact (duplicate_occupations_leave_the_same_length [whole]).trans one_hour
  refine ⟨first, second, combined, ?_, the_original_full_period_pays_life_and_finishes_its_native_work.1⟩
  norm_num [conversion, first, combined]

private def uninstrumented : Meter.{0} lifeSource where
  OccupiedAt := fun _ _ _ _ _ _ => PEmpty

theorem two_paid_actions_alone_cannot_supply_occupation :
    IsEmpty (Observation lifeSource uninstrumented firstPaidPeriod) :=
  ⟨fun observed => PEmpty.elim observed.measured⟩

theorem no_food_credit_leaves_the_original_named_shortage
    (repair : List (Option (Compile.RawInput Bool Bool Bool Unit Unit)))
    (unfunded : repairCredit lifeSource lifePeriod repair false true = 0) :
    ∃ loss : Loss lifeSource lifePeriod repair, loss.address = (false, true) ∧
      Recorded lifeSource (lifePeriod ++ repair) := by
  apply original_repair_credit_below_gap_keeps_its_named_loss
  rw [unfunded, the_original_period_uses_the_actual_food_stock, the_repair_really_funds_both_original_lives.1]
  norm_num

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consumers
