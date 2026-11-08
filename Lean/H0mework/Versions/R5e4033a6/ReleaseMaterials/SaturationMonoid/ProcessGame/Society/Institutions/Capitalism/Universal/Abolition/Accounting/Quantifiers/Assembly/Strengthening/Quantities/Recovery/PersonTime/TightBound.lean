import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Roster

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Abolition.Root Abolition.Root.Registered
open Intervals

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def originalExposure (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) : ℚ :=
  phaseHours (roster origin meter exposure) person .exposure

private def burden : Phase → Bool
  | .ordinary => false
  | .exposure | .recovery => true

/-- A continuation cannot erase an exposure already observed on its
original prefix. New exposure and repair hours join that person's clock
union, including any new exposure incurred by the repair itself. -/
def hoursThroughRepair (origin : C) (meter : Meter.{u} origin) (exposure repair : Script)
    (person : Party) : ℚ :=
  length (phaseSpans (roster origin meter exposure) person .exposure ++
    spansFor (roster origin meter (exposure ++ repair)) person burden)

theorem original_exposure_is_preserved_in_every_continuation
    (origin : C) (meter : Meter.{u} origin) (exposure repair : Script) (person : Party) :
    originalExposure origin meter exposure person ≤ hoursThroughRepair origin meter exposure repair person := by
  unfold originalExposure phaseHours hoursThroughRepair
  apply length_mono
  rw [cover_append]
  exact Set.subset_union_left

def readRatio (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party)
    (repair : Script) : EReal :=
  (((hoursThroughRepair origin meter exposure repair person /
    originalExposure origin meter exposure person : ℚ) : ℝ) : EReal)

theorem a_positive_original_exposure_has_at_least_unit_ratio
    (origin : C) (meter : Meter.{u} origin) (exposure repair : Script) (person : Party)
    (positive : 0 < originalExposure origin meter exposure person) :
    (1 : EReal) ≤ readRatio origin meter exposure person repair := by
  change ((1 : ℝ) : EReal) ≤ _
  rw [readRatio, EReal.coe_le_coe_iff, ← Rat.cast_one, Rat.cast_le, le_div_iff₀ positive, one_mul]
  exact original_exposure_is_preserved_in_every_continuation origin meter exposure repair person

structure PaidRecovery (origin : C) (exposure repair : Script) : Prop where
  settled : Settled (Execution.endAt origin exposure) repair
  restored : Restored origin exposure repair
  whole : Recorded origin (exposure ++ repair)

private theorem recovered (origin : C) (exposure repair : Script)
    (paid : Settled (Execution.endAt origin exposure) repair)
    (inspected : Recovery.inspect origin exposure repair = none) :
    PaidRecovery origin exposure repair :=
  ⟨paid, (cleared_exactly_when_no_original_actor_loses_stock origin exposure repair).mp inspected, record origin _⟩

def cutoff (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) : WithTop EReal :=
  Bounds.Restriction.cutoff (Execution.endAt origin exposure) (Recovery.inspect origin exposure)
    (readRatio origin meter exposure person)

theorem exact_measured_repair_value_image
    (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) (value : EReal) :
    (value : WithTop EReal) ∈ Bounds.values (Execution.endAt origin exposure)
      (Bounds.Restriction.restrict (Recovery.inspect origin exposure) (readRatio origin meter exposure person)) ↔
    ∃ repair, PaidRecovery origin exposure repair ∧ readRatio origin meter exposure person repair = value := by
  rw [Bounds.Restriction.exact_qualified_image]
  constructor
  · rintro ⟨repair, paid, cleared, exactValue⟩
    exact ⟨repair, recovered origin exposure repair paid cleared, exactValue⟩
  · rintro ⟨repair, paid, exactValue⟩
    exact ⟨repair, paid.settled, (cleared_exactly_when_no_original_actor_loses_stock _ _ _).mpr paid.restored,
      exactValue⟩

inductive Minimum (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) : Prop
  | noExposure (zero : originalExposure origin meter exposure person = 0)
      (original : Recorded origin exposure)
  | attained (positive : 0 < originalExposure origin meter exposure person)
      (repair : Script) (paid : PaidRecovery origin exposure repair)
      (exactValue : (readRatio origin meter exposure person repair : WithTop EReal) =
        cutoff origin meter exposure person)
  | approached (positive : 0 < originalExposure origin meter exposure person)
      (strict : ∀ repair, PaidRecovery origin exposure repair →
        cutoff origin meter exposure person < (readRatio origin meter exposure person repair : WithTop EReal))
      (near : ∀ limit, cutoff origin meter exposure person < limit →
        ∃ repair, PaidRecovery origin exposure repair ∧
          (readRatio origin meter exposure person repair : WithTop EReal) < limit)
      (existsPaid : ∃ repair, PaidRecovery origin exposure repair)
  | obstructed (positive : 0 < originalExposure origin meter exposure person)
      (issues : ∀ repair, Recorded origin (exposure ++ repair) ∧
        (Nonempty (Obstruction (Execution.endAt origin exposure) repair) ∨
          ∃ loss, Recovery.inspect origin exposure repair = some loss))

theorem the_original_persons_recovery_has_its_exact_paid_minimum_or_approach_or_obstruction
    (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) :
    Minimum origin meter exposure person := by
  rcases eq_or_lt_of_le (length_nonnegative (phaseSpans (roster origin meter exposure) person .exposure)) with
    zero | positive
  · exact .noExposure zero.symm (record origin exposure)
  · cases Bounds.Restriction.resolve (Execution.endAt origin exposure)
      (Recovery.inspect origin exposure) (readRatio origin meter exposure person) with
    | attained repair paid cleared exactValue =>
      exact .attained positive repair (recovered origin exposure repair paid cleared) exactValue
    | approached strict near available =>
      refine .approached positive ?_ ?_ ?_
      · intro repair paid
        exact strict repair paid.settled
          ((cleared_exactly_when_no_original_actor_loses_stock _ _ _).mpr paid.restored)
      · intro limit beyond
        obtain ⟨repair, paid, cleared, close⟩ := near limit beyond
        exact ⟨repair, recovered origin exposure repair paid cleared, close⟩
      · obtain ⟨repair, paid, cleared⟩ := available
        exact ⟨repair, recovered origin exposure repair paid cleared⟩
    | blocked issues =>
      exact .obstructed positive (fun repair => ⟨record origin _, (issues repair).2⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
