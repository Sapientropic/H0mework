import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual.ClockBound
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.OpeningBudget

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Numerical

open Quantities Actual
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint

noncomputable section

abbrev oldAddress : Bool × Bool := (true, false)

theorem observed_opening_equals_the_required_unit : Allocation.opening source budget oldAddress = 1 := by
  unfold Allocation.opening
  rw [source_reads_the_paid_opening]
  decide +kernel

private theorem one_unit_fits_the_original_word :
    Allocation.FitsAt source word ordered task (reserved word) held budget oldAddress 1 assigned := by
  have funded := (Allocation.with_available_stock_at_the_target_uses_the_same_joint_contract
    source word ordered task (reserved word) held budget oldAddress assigned).mpr
      ⟨the_two_services_are_funded_at_the_tight_opening, by rw [observed_opening_equals_the_required_unit]; norm_num⟩
  rwa [observed_opening_equals_the_required_unit] at funded

private theorem each_joint_stock_candidate_requires_one_unit (amount : ℚ)
    (allocation : Assignment source ordered task proposal)
    (fits : Allocation.FitsAt source word ordered task (reserved word) held budget oldAddress amount allocation) :
    1 ≤ amount := by
  have watched : oldAddress ∈ Allocation.watched source word ordered task :=
    Due.Settlement.every_due_address_is_watched source word ordered task (row false)
  have exactProtection := fits.2.2 oldAddress watched
  change Reserve.Protects _ _ _ _ _ (Allocation.stockAt source budget oldAddress amount oldAddress)
    at exactProtection
  rw [Allocation.stockAt, if_pos rfl] at exactProtection
  have opening := (Reserve.openingNeed_fits_iff _ _ _ _ _ _).mpr exactProtection
  exact (no_allocation_can_lower_the_original_one_unit_opening allocation).trans opening

theorem the_exact_stock_projection_generates_the_one_unit_original_handoff :
    ∃ allocation paid least,
      Allocation.leastOpeningAt source word ordered task (reserved word) held budget oldAddress =
        .attained 1 allocation paid least ∧
      valid source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) ⟨proposal, allocation⟩ ∧
      Evolving.Epoch.Current.ClosedAt (completed source proposal) := by
  cases computed : Allocation.leastOpeningAt source word ordered task (reserved word) held budget oldAddress with
  | blocked impossible => exact (impossible ⟨1, assigned, one_unit_fits_the_original_word⟩).elim
  | attained amount allocation paid least =>
    have exactAmount : amount = 1 :=
      le_antisymm (least 1 assigned one_unit_fits_the_original_word)
        (each_joint_stock_candidate_requires_one_unit amount allocation paid)
    subst amount
    exact ⟨allocation, paid, least, rfl,
      an_opening_witness_is_consumed_by_the_original_handoff source ordered task reserved held budget
        ((6 : ℚ) : WithTop ℚ) proposal oldAddress 1 allocation paid (by rw [observed_opening_equals_the_required_unit])
        Actual.paid original_demands_are_nonnegative the_original_handoff_has_paid_its_native_settlement
        the_same_original_handoff_is_admitted_at_clock_six.2⟩

theorem the_same_handoff_attains_the_earliest_time_with_its_tight_opening :
    ∃ allocation paid least,
      Allocation.leastOpeningAt source word ordered task (reserved word) held budget oldAddress =
        .attained 1 allocation paid least ∧
      valid source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) ⟨proposal, allocation⟩ ∧
      (completed source proposal).raw.clock = 6 ∧
      Evolving.Epoch.Current.ClosedAt (completed source proposal) ∧
      ∀ other, Checked source other → 6 ≤ handoffTime source other := by
  obtain ⟨allocation, paid, least, computed, valid, closed⟩ :=
    the_exact_stock_projection_generates_the_one_unit_original_handoff
  exact ⟨allocation, paid, least, computed, valid,
    the_same_original_root_pays_two_periods_at_clocks_five_and_six.2.2.2.1, closed,
    any_checked_handoff_on_the_original_source_takes_until_clock_six⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Numerical
