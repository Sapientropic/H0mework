import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Production
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifePeriod

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers

open Abolition.Root Abolition.Root.Registered Execution
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord source_ready source_review)

noncomputable section

local notation "C" => Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)
local notation "Script" => List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

def firstPaidPeriod := periodAndAccounting lifeSource lifeWord

theorem the_original_full_period_pays_life_and_finishes_its_native_work :
    Settled lifeSource firstPaidPeriod ∧ elapsed lifeSource firstPaidPeriod = 1 := by
  have paid := the_original_paid_period_retains_all_native_rows lifeSource lifeWord
    source_ready source_review checked_living_period
  refine ⟨paid.1, ?_⟩
  have same : (endAt lifeSource firstPaidPeriod).raw = (endAt lifeSource lifePeriod).raw :=
    paid.2.trans the_original_life_period_pays_its_actual_material_body.symm
  unfold elapsed
  rw [same]
  exact the_original_period_advances_one_actual_hour

def stopAfterFirst : Nat → C → Script
  | 0, current => periodAndAccounting current lifeWord
  | _ + 1, _ => []

def noExtraCheck (_stage : Nat) (_current : C) (_word : Script) : Option Unit := none

private theorem stopped_stages_keep_the_first_paid_current (later : Nat) :
    stageAt lifeSource stopAfterFirst (later + 1) = endAt lifeSource firstPaidPeriod := by
  induction later with
  | zero => rfl
  | succ later ih =>
    rw [next_stage_is_the_literal_original_next]
    exact ih

theorem infinitely_many_stages_after_one_paid_period_leave_a_real_clock_obstruction :
    Settled lifeSource (stageBody lifeSource stopAfterFirst 0) ∧
      Bounds.Cofinal.Failure lifeSource stopAfterFirst (fun _ _ _ => Unit) noExtraCheck ∧
      ¬ Bounds.Cofinal.ClockCofinal lifeSource stopAfterFirst := by
  have first := the_original_full_period_pays_life_and_finishes_its_native_work
  have strict (stage : Nat) : (stageAt lifeSource stopAfterFirst stage).raw.clock < lifeSource.raw.clock + 2 := by
    cases stage with
    | zero => change lifeSource.raw.clock < lifeSource.raw.clock + 2; linarith
    | succ later =>
      rw [stopped_stages_keep_the_first_paid_current]
      have hour := first.2
      unfold elapsed at hour
      linarith
  refine ⟨first.1, .boundedClock _ strict, ?_⟩
  intro reaches
  obtain ⟨stage, enough⟩ := reaches (lifeSource.raw.clock + 2)
  exact (not_lt_of_ge enough) (strict stage)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
