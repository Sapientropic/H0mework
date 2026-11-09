import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Conservation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Transport

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Registration

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (C conflict)
open Quantities.Execution (endAt primitiveScript)
open Reparation.Consumers (warCut original recordsActualBirth firstBirthPrefix secondBirthPrefix)
open Transport (NativeWork registrationAt)
open Allocation

noncomputable section

abbrev RegistrationScript := Script Bool Bool Bool Unit Unit

abbrev beforeBirth (tail : RegistrationScript) : RegistrationScript :=
  primitiveScript conflict ++ tail

abbrev originalCut (tail : RegistrationScript) : C := endAt warCut (beforeBirth tail)

def balances (past : RegistrationScript) :=
  (run warCut (id : Bool → Bool) past).stack.balances

private theorem prefix_has_the_original_cut (tail : RegistrationScript) :
    originalCut tail = Transport.originalAt original tail :=
  Quantities.Execution.endAt_append warCut (primitiveScript conflict) tail

def DispatcherRegistration (cut : C) : Prop :=
  ∃ (work : NativeWork cut) (registered : Transport.Admission.Registration cut.native)
    (selected : registrationAt cut = some registered),
    Transport.inspect cut = .registration work registered selected

/-- Read the native admission and its exact joint write at one original tick. -/
def RegistrationAt (tail : RegistrationScript) : Prop :=
  let past := beforeBirth tail
  DispatcherRegistration (originalCut tail) ∧
  balances (past ++ [none]) = balances past ∧
  ∀ good, paidAt warCut id good past none = 0 ∧ inputQuantity (seed := warCut) past none good = 0

private theorem original_dispatcher (tail : RegistrationScript) (found : recordsActualBirth tail) :
    DispatcherRegistration (originalCut tail) := by
  apply Eq.mpr (congrArg DispatcherRegistration (prefix_has_the_original_cut tail))
  obtain ⟨work, registered, selected, _⟩ := found
  exact ⟨work, registered, selected, Transport.inspect_registration (claim := original) (past := tail) none work selected⟩

set_option maxHeartbeats 700000 in
private theorem native_keeps_rows (past : RegistrationScript) (work : NativeWork (endAt warCut past)) :
    balances (past ++ [none]) = balances past ∧
    ∀ good, paidAt warCut id good past none = 0 ∧ inputQuantity (seed := warCut) past none good = 0 := by
  let before := run warCut (id : Bool → Bool) past
  have empty : Boundary.Actual.items (endAt warCut past) none = [] :=
    Transport.native_step_has_no_material_items none work
  have noOpening : openings warCut id past none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ empty]
    rfl
  constructor
  · unfold balances
    rw [run_snoc, written_balances, noOpening, List.map_nil, List.append_nil]
    exact (no_original_items_keeps_rows past none before.stack.balances empty).1
  · intro good
    refine ⟨(no_original_items_keeps_rows past none (posted before none).stack.balances empty).2 good, ?_⟩
    have noPositions : itemPositions (seed := warCut) past none = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [itemPositions, List.length_finRange, empty, List.length_nil]
    unfold inputQuantity
    rw [noPositions]
    rfl

private theorem registration_on_the_original_history (tail : RegistrationScript)
    (found : recordsActualBirth tail) : RegistrationAt tail := by
  have dispatcher := original_dispatcher tail found
  refine ⟨dispatcher, ?_⟩
  obtain ⟨work, _, _, _⟩ := dispatcher
  exact native_keeps_rows _ work

theorem both_original_financial_registrations_keep_the_entire_reparation_ledger :
    RegistrationAt firstBirthPrefix ∧ RegistrationAt secondBirthPrefix :=
  ⟨registration_on_the_original_history _ Reparation.Consumers.first_actual_birth_preserves_the_four_due_and_generates_next.1,
    registration_on_the_original_history _ Reparation.Consumers.second_actual_birth_preserves_the_paid_row_and_generates_next.1⟩

theorem the_second_registration_extends_the_first_joint_run :
    (beforeBirth firstBirthPrefix ++ [none]).IsPrefix (beforeBirth secondBirthPrefix) := by
  change ((primitiveScript conflict ++ firstBirthPrefix) ++ [none]).IsPrefix
    (primitiveScript conflict ++ secondBirthPrefix)
  rw [List.append_assoc, List.prefix_append_right_inj,
    Reparation.Consumers.the_second_birth_follows_the_first_on_the_same_trajectory]
  exact List.prefix_append_of_prefix (List.prefix_append _ _)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Registration
