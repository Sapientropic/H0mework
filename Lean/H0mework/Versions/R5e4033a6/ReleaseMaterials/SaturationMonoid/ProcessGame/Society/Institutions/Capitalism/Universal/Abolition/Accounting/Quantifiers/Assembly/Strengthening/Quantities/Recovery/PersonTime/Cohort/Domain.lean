import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Profile
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort

open Abolition.Root Abolition.Root.Registered
open Bounds System

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def repairCheck (origin : C) (exposure : Script) (_ : Unit) (repair : Script) :
    Option (Loss origin exposure repair) :=
  Recovery.inspect origin exposure repair

theorem repair_passes_iff_original_stock_is_restored (origin : C) (exposure repair : Script) :
    Passes (repairCheck origin exposure) repair ↔ Restored origin exposure repair := by
  rw [← cleared_exactly_when_no_original_actor_loses_stock]
  constructor
  · intro all
    exact all ()
  · intro restored _
    exact restored

abbrev domain (origin : C) (meter : Meter.{u} origin) (exposure : Script) :
    Set (Address origin meter exposure → EReal) :=
  System.values (Execution.endAt origin exposure) id (repairCheck origin exposure) (profile origin meter exposure)

/-- The joint image contains the exact hours and every meaningful ratio
from a single paid repair, with restoration at all original addresses. -/
theorem mem_domain_iff_one_original_paid_repair (origin : C) (meter : Meter.{u} origin)
    (exposure : Script) (values : Address origin meter exposure → EReal) :
    values ∈ domain origin meter exposure ↔
      ∃ repair, PaidRecovery origin exposure repair ∧ profile origin meter exposure repair = values := by
  rw [an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it]
  constructor
  · rintro ⟨repair, paid, restored, exactValue⟩
    exact ⟨repair, ⟨paid, (repair_passes_iff_original_stock_is_restored origin exposure repair).mp restored,
      record origin _⟩, exactValue⟩
  · rintro ⟨repair, paid, exactValue⟩
    exact ⟨repair, paid.settled, (repair_passes_iff_original_stock_is_restored origin exposure repair).mpr
      paid.restored, exactValue⟩

theorem the_joint_repair_domain_has_tight_original_envelopes (origin : C) (meter : Meter.{u} origin)
    (exposure : Script) :
    IsGLB (domain origin meter exposure) (sInf (domain origin meter exposure)) ∧
      IsLUB (domain origin meter exposure) (sSup (domain origin meter exposure)) :=
  original_joint_envelope_is_tight _ _ _ _

theorem each_persons_coordinate_resolves_within_the_same_repair_domain (origin : C) (meter : Meter.{u} origin)
    (exposure : Script) (address : Address origin meter exposure) :
    let cut := Execution.endAt origin exposure
    let check := System.inspect (repairCheck origin exposure)
    Bounds.Compiled.Minimum cut id check (fun repair => profile origin meter exposure repair address) ∧
      Bounds.Compiled.Minimum cut id check (fun repair => OrderDual.toDual (profile origin meter exposure repair address)) :=
  every_coordinate_resolves_on_the_same_joint_feasible_domain _ _ _ _ address

/-- If the componentwise ideal cannot be implemented, every admissible
repair has a specific person's coordinate strictly above that ideal. -/
theorem the_joint_ideal_is_paid_or_every_original_repair_has_a_named_gap
    (origin : C) (meter : Meter.{u} origin) (exposure : Script) :
    (∃ repair, PaidRecovery origin exposure repair ∧
      profile origin meter exposure repair = sInf (domain origin meter exposure)) ∨
    (∀ repair, PaidRecovery origin exposure repair →
      ∃ address, sInf (domain origin meter exposure) address < profile origin meter exposure repair address) := by
  classical
  let attainable := domain origin meter exposure
  by_cases exactIdeal : sInf attainable ∈ attainable
  · exact .inl ((mem_domain_iff_one_original_paid_repair origin meter exposure _).mp exactIdeal)
  · right
    intro repair paid
    have within : profile origin meter exposure repair ∈ attainable :=
      (mem_domain_iff_one_original_paid_repair origin meter exposure _).mpr ⟨repair, paid, rfl⟩
    by_contra! noGap
    have exactly : profile origin meter exposure repair = sInf attainable :=
      le_antisymm noGap (sInf_le within)
    exact exactIdeal (exactly ▸ within)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort
