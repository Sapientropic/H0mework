import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Payments
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlPayments

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus

noncomputable section

def positionsAt (entry : PublicFunction.Costs.Visits.Window sources) :=
  Payments.positions (sources entry.1).law
    (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)

def atVisit (entry : PublicFunction.Costs.Visits.Window sources)
    (selected credit : Bool) (party : Bool) (good : Good) : ℚ :=
  Payments.amount (sources entry.1).law
    (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) selected credit party good

def side (credit : Bool) : Financial.Family.Migration.Posting.Side := if credit then .credit else .debit

theorem atVisit_partition (entry : PublicFunction.Costs.Visits.Window sources) (credit : Bool) (party : Bool) (good : Good) :
    atVisit entry true credit party good + atVisit entry false credit party good =
      Financial.Family.Migration.Posting.atVisit sources entry (side credit) party good := by
  have partition := Payments.exact_partition (sources entry.1).law
    (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) credit party good
  change _ + _ = _ at partition
  change _ + _ = _
  rw [show atVisit entry true credit party good + atVisit entry false credit party good =
    Payments.settlementTotal (sources entry.1).law
      (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
      (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) credit party good from partition]
  cases credit with
  | false =>
      change (((sources entry.1).law.rawItems
        (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
        (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)).attach.map
        (fun position => Financial.Family.Migration.Posting.rawAmount sources entry.1 position.val .debit party good)).sum = _
      rw [List.attach_map_val (f := fun item => Financial.Family.Migration.Posting.rawAmount sources entry.1 item .debit party good)]
      rfl
  | true =>
      change (((sources entry.1).law.rawItems
        (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
        (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)).attach.map
        (fun position => Financial.Family.Migration.Posting.rawAmount sources entry.1 position.val .credit party good)).sum = _
      rw [List.attach_map_val (f := fun item => Financial.Family.Migration.Posting.rawAmount sources entry.1 item .credit party good)]
      rfl

theorem positionsAt_have_distinct_indices (entry : PublicFunction.Costs.Visits.Window sources) :
    ((positionsAt entry).map (fun position => position.val.index)).Nodup :=
  Payments.positions_have_distinct_original_indices _ _ _

def total : List (PublicFunction.Costs.Visits.Window sources) → Bool → Bool → Bool → Good → ℚ
  | [], _, _, _, _ => 0
  | entry :: rest, selected, credit, party, good =>
      atVisit entry selected credit party good + total rest selected credit party good

theorem total_partition (entries : List (PublicFunction.Costs.Visits.Window sources)) (credit : Bool) (party : Bool) (good : Good) :
    total entries true credit party good + total entries false credit party good =
      Financial.Family.Migration.Posting.total sources entries (side credit) party good := by
  induction entries with
  | nil => simp only [total, Financial.Family.Migration.Posting.total, add_zero]
  | cons entry rest ih =>
      change (atVisit entry true credit party good + total rest true credit party good) +
        (atVisit entry false credit party good + total rest false credit party good) =
        Financial.Family.Migration.Posting.atVisit sources entry (side credit) party good + Financial.Family.Migration.Posting.total sources rest (side credit) party good
      have head := atVisit_partition entry credit party good
      linarith

def actual {first last : Packet} (path : Evolution first last) := total (Costs.records path)

theorem actual_partition {first last : Packet} (path : Evolution first last) (credit : Bool) (party : Bool) (good : Good) :
    actual path true credit party good + actual path false credit party good = Posting.actual path (side credit) party good := by
  rw [Posting.exact_amount]
  exact total_partition (Costs.records path) credit party good

theorem actual_debit_is_partitioned_once {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    actual path true false party good + actual path false false party good = Costs.cost path party (.debtPayment good) := by
  rw [actual_partition]
  exact Posting.debit_is_the_same_material_payment path party good

theorem total_nonnegative (entries : List (PublicFunction.Costs.Visits.Window sources))
    (selected credit : Bool) (party : Bool) (good : Good) :
    0 ≤ total entries selected credit party good := by
  induction entries with
  | nil => exact le_rfl
  | cons entry rest ih => exact add_nonneg (Payments.amount_nonnegative _ _ _ selected credit party good) ih

theorem actual_selected_bounded {first last : Packet} (path : Evolution first last) (credit : Bool) (party : Bool) (good : Good) :
    actual path true credit party good ≤ Posting.actual path (side credit) party good := by
  have partition := actual_partition path credit party good
  have positive := total_nonnegative (Costs.records path) false credit party good
  change 0 ≤ actual path false credit party good at positive
  linarith

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlPayments
