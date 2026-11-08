import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Length
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive

open Abolition.Root Abolition.Root.Registered
open Intervals

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def originalLongest (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) : ℚ :=
  longest (phaseSpans (roster origin meter exposure) person .exposure)

theorem a_consecutive_exposure_never_exceeds_total_personal_exposure
    (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) :
    originalLongest origin meter exposure person ≤ originalExposure origin meter exposure person := by
  let measured := phaseSpans (roster origin meter exposure) person .exposure
  change longest measured ≤ length measured
  by_cases positive : 0 < longest measured
  · obtain ⟨run, _, _, covered, exactWidth⟩ := positive_longest_is_attained_between_original_endpoints measured positive
    rw [← exactWidth, ← length_one]
    apply length_mono
    intro time present
    obtain ⟨interval, listed, inside⟩ := present
    rcases List.mem_singleton.mp listed with rfl
    exact covered inside
  · exact (le_of_not_gt positive).trans (length_nonnegative _)

def exposureValue (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party) : EReal :=
  ((originalLongest origin meter exposure person : ℝ) : EReal)

/-- One exposure length is available precisely when the original
continuation pays and restores every affected material address. -/
def attainable (origin : C) (meter : Meter.{u} origin) (person : Party) : Set EReal :=
  fun value => ∃ exposure repair, PaidRecovery origin exposure repair ∧
    exposureValue origin meter exposure person = value

def upper (origin : C) (meter : Meter.{u} origin) (person : Party) : EReal :=
  sSup (attainable origin meter person)

theorem upper_is_the_exact_recovery_backed_bound
    (origin : C) (meter : Meter.{u} origin) (person : Party) (limit : EReal) :
    upper origin meter person ≤ limit ↔
      ∀ exposure repair, PaidRecovery origin exposure repair → exposureValue origin meter exposure person ≤ limit := by
  constructor
  · intro bound exposure repair paid
    exact (le_sSup (show exposureValue origin meter exposure person ∈ attainable origin meter person
      from ⟨exposure, repair, paid, rfl⟩)).trans bound
  · intro all
    apply sSup_le
    rintro value ⟨exposure, repair, paid, rfl⟩
    exact all exposure repair paid

inductive Maximum (origin : C) (meter : Meter.{u} origin) (person : Party) : Prop
  | attained (exposure repair : Script) (paid : PaidRecovery origin exposure repair)
      (exactValue : exposureValue origin meter exposure person = upper origin meter person)
  | approached (available : (attainable origin meter person).Nonempty)
      (notAttained : upper origin meter person ∉ attainable origin meter person)
      (near : ∀ limit, limit < upper origin meter person →
        ∃ exposure repair, PaidRecovery origin exposure repair ∧ limit < exposureValue origin meter exposure person)
  | obstructed (issues : ∀ exposure repair, Recorded origin (exposure ++ repair) ∧
      (Nonempty (Obstruction (Execution.endAt origin exposure) repair) ∨ Nonempty (Loss origin exposure repair)))

theorem the_maximum_recovery_backed_exposure_is_paid_approached_or_originally_blocked
    (origin : C) (meter : Meter.{u} origin) (person : Party) :
    Maximum origin meter person := by
  classical
  by_cases greatest : upper origin meter person ∈ attainable origin meter person
  · obtain ⟨exposure, repair, paid, exactValue⟩ := greatest
    exact .attained exposure repair paid exactValue
  by_cases available : (attainable origin meter person).Nonempty
  · refine .approached available greatest ?_
    intro limit below
    obtain ⟨value, ⟨exposure, repair, paid, rfl⟩, strict⟩ := lt_sSup_iff.mp below
    exact ⟨exposure, repair, paid, strict⟩
  · refine .obstructed fun exposure repair => ⟨record origin _, ?_⟩
    cases decideAt (Execution.endAt origin exposure) repair with
    | blocked issue => exact Or.inl ⟨issue⟩
    | feasible actual =>
      cases inspected : Recovery.inspect origin exposure repair with
      | some loss => exact Or.inr ⟨loss⟩
      | none =>
        have paid : PaidRecovery origin exposure repair :=
          ⟨settle _ _ actual, (cleared_exactly_when_no_original_actor_loses_stock _ _ _).mp inspected, record origin _⟩
        exact (available ⟨_, exposure, repair, paid, rfl⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive
