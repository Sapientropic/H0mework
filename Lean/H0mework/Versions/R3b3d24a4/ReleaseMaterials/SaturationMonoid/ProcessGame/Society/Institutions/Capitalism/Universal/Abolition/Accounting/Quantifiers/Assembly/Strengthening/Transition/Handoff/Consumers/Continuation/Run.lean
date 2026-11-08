import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Word
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch Actual Handoff.Continuation

noncomputable section

abbrev TraceWord := List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

private theorem the_same_cut_accepts_its_installed_query (cut : C) (n : Nat) (installed : InstalledAt cut n) :
    InstalledAt (installedQuery cut) n := by
  have control : (installedQuery cut).control = cut.control :=
    (cut.requery_keeps_control_and_complete_account (fun _ _ => .advance)).1
  exact ⟨installed.originalInput, installed.raw, installed.ready, rfl,
    (congrArg (fun c : ControlAt => c.phase) control).trans installed.phase,
    (congrArg (fun c : ControlAt => c.review) control).trans installed.review⟩

theorem installed_query_is_paid (cut : C) (n : Nat) (installed : InstalledAt cut n) :
    InstalledPaid cut ∧ PaidBody (installedQuery cut) n := by
  have query := the_same_cut_accepts_its_installed_query cut n installed
  have paid := the_original_advance_pays_its_installed_word _ _ query
  exact ⟨⟨the_reader_selects_its_paid_renewal _ _ query, paid.paid⟩, paid⟩

private theorem the_actual_drain_keeps_the_installed_word (cut : C) (n : Nat) (installed : InstalledAt cut n) :
    InstalledAt (Execution.endAt cut (renewalSuffix cut)) (n + 1) := by
  let body := (installedQuery cut).advance
  have paid := (installed_query_is_paid cut n installed).2
  have drain := Execution.the_first_exhausted_native_cut_is_the_original_paid_drain body
  rw [renewalSuffix_ends_at_the_original_native_drain]
  refine ⟨(Execution.endAt_input body _).trans ((installedQuery cut).advance_parameters.1.trans installed.originalInput),
    drain.2.1.trans paid.successor, drain.1, ?_, ?_, ?_⟩
  · exact native_payments_keep_the_actual_reader body (advance_keeps_the_actual_reader _ rfl) _
  · rw [drain_preserves_control]
    exact paid.phase
  · rw [drain_preserves_control]
    exact paid.review

/-- Each successor is produced by the installed proposal and its native
drain, starting at the paid two-period handoff. -/
def run : Nat → C
  | 0 => start
  | n + 1 => Execution.endAt (run n) (renewalSuffix (run n))

theorem run_is_installed (n : Nat) : InstalledAt (run n) n := by
  induction n with
  | zero => exact start_is_installed
  | succ n prior => exact the_actual_drain_keeps_the_installed_word _ _ prior

def actualPrefix : Nat → TraceWord
  | 0 => []
  | n + 1 => actualPrefix n ++ renewalSuffix (run n)

theorem the_actual_prefix_ends_at_run (n : Nat) : Execution.endAt start (actualPrefix n) = run n := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [actualPrefix, Execution.endAt_append, prior]
    rfl

theorem the_run_clock (n : Nat) : (run n).raw.clock = 6 + (n : ℚ) := by
  rw [(run_is_installed n).raw, material_has_its_actual_clock]

theorem the_run_keeps_its_exact_material (n : Nat) :
    (∀ bearer good, (run n).raw.stock bearer good = opening.stock bearer good +
      ((n + 2 : Nat) : ℚ) * gain bearer good) ∧ (run n).raw.claims = opening.claims := by
  rw [(run_is_installed n).raw]
  exact each_material_restriction_has_exact_stock_and_claims n

theorem the_renewal_commits_the_original_inventory (cut : C) (n : Nat) (installed : InstalledAt cut n) :
    Execution.timedInventory cut (renewalSuffix cut) =
      (publicLaw.rawItems (materialAt n) period).map (fun item => (item, 6 + ((n + 1 : Nat) : ℚ))) := by
  let query := installedQuery cut
  let body := query.advance
  have ready := (the_same_cut_accepts_its_installed_query cut n installed).ready
  have paid := (installed_query_is_paid cut n installed).2
  have drain : Execution.timedInventory body (Execution.drain body) = [] :=
    List.map_eq_nil_iff.mp ((Execution.timedInventory_is_the_original_inventory _ _).trans
      (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain body).2.2.1)
  have items : Optimality.Programme.Epoch.materialItems query = publicLaw.rawItems (materialAt n) period := by
    unfold Optimality.Programme.Epoch.materialItems
    rw [if_neg ready]
    exact paid.inventory
  change (Optimality.Programme.Epoch.materialItems query).map (fun item => (item, body.raw.clock)) ++
      Execution.timedInventory body (Execution.drain body) = _
  rw [items, drain, List.append_nil, show body.raw = materialAt (n + 1) from paid.successor,
    material_has_its_actual_clock]

theorem each_original_renewal_is_settled (n : Nat) :
    InstalledPaid (run n) ∧ Settled (run n) (renewalSuffix (run n)) := by
  let cut := run n
  have installed := run_is_installed n
  have timed := the_renewal_commits_the_original_inventory cut n installed
  have actual : Execution.inventory cut (renewalSuffix cut) =
      (Physical.Public.interpreter cut.native.input).rawItems cut.raw period := by
    rw [← Execution.timedInventory_is_the_original_inventory, timed, List.map_map,
      show Prod.fst ∘ (fun item => (item, (6 : ℚ) + ((n + 1 : Nat) : ℚ))) = id from rfl,
      List.map_id, show Physical.Public.interpreter cut.native.input = publicLaw from
        congrArg Physical.Public.interpreter installed.originalInput, installed.raw]
  refine ⟨(installed_query_is_paid cut n installed).1, settle cut _ ⟨?_, (run_is_installed (n + 1)).ready⟩⟩
  apply (Demand.covers_iff_original_floor_of_paid_inventory _ period ExecutionItem.index (by simpa using actual)).mpr
  rw [show Public.Scope.checkInput cut.native.input = checkInput from
      congrArg Public.Scope.checkInput installed.originalInput, installed.raw]
  exact (each_material_restriction_checks_the_original_period _ _ n).2.1

theorem every_horizon_has_a_paid_original_successor (deadline : ℚ) :
    ∃ n, deadline < (run n).raw.clock ∧
      Execution.endAt source (script source proposal ++ actualPrefix n) = run n ∧
      Recorded source (script source proposal ++ actualPrefix n) ∧
      Settled (run n) (renewalSuffix (run n)) := by
  obtain ⟨n, past⟩ := exists_nat_gt deadline
  refine ⟨n, ?_, (Execution.endAt_append _ _ _).trans (the_actual_prefix_ends_at_run n),
    record source _, (each_original_renewal_is_settled n).2⟩
  rw [the_run_clock]
  linarith

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
