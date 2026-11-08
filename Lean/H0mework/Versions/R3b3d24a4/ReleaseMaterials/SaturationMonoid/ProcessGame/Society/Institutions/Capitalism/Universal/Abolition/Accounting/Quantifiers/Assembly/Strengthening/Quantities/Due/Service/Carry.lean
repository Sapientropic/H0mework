import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Execution
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ids : Finset TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {booked : Finset (Ordinal source past)}

/-- Later allocation sees the literal successor and only new receipt ordinals.
The original tasks and windows persist and the paid part cannot become need again. -/
def carryNetwork (receipt : (network source past ids task booked).Certificate)
    (future : Script) (reserved : Finset (Ordinal (endAt source past) future)) :
    Network (Need ids task) (Supply (endAt source past) future ids task) :=
  { network (endAt source past) future ids task reserved with
    need := remaining receipt
    need_nonnegative := fun line => sub_nonneg.mpr (receipt.admitted.2.1 line) }

def carryRemaining (receipt : (network source past ids task booked).Certificate)
    (future : Script) (reserved : Finset (Ordinal (endAt source past) future))
    (later : (carryNetwork receipt future reserved).Certificate) (line : Need ids task) : ℚ :=
  (carryNetwork receipt future reserved).need line - Network.rowTotal later.allocation line

theorem cumulative_payment_and_remainder_keep_the_same_original_need
    (receipt : (network source past ids task booked).Certificate)
    (future : Script) (reserved : Finset (Ordinal (endAt source past) future))
    (later : (carryNetwork receipt future reserved).Certificate) (line : Need ids task)
    (original : OriginalDemands ids task) :
    0 ≤ carryRemaining receipt future reserved later line ∧
      Network.rowTotal receipt.allocation line + Network.rowTotal later.allocation line +
        carryRemaining receipt future reserved later line =
        amount Good line.1.spec.goods line.2.val := by
  have read := (allocated_and_remaining_are_the_original_quantity receipt line original).2
  refine ⟨sub_nonneg.mpr (later.admitted.2.1 line), ?_⟩
  change Network.rowTotal receipt.allocation line + Network.rowTotal later.allocation line +
    (remaining receipt line - Network.rowTotal later.allocation line) = _
  linarith only [read]

theorem a_fully_paid_line_does_not_reappear_in_the_later_need
    (receipt : (network source past ids task booked).Certificate)
    (future : Script) (reserved : Finset (Ordinal (endAt source past) future)) (line : Need ids task)
    (paid : Network.rowTotal receipt.allocation line = (network source past ids task booked).need line) :
    (carryNetwork receipt future reserved).need line = 0 := by
  change (network source past ids task booked).need line - Network.rowTotal receipt.allocation line = 0
  rw [paid, sub_self]

def priorOrdinal (source : C) (past future : Script) (ordinal : Ordinal source past) :
    Ordinal source (past ++ future) :=
  ⟨ordinal.val, by rw [inventory_append, List.length_append]; omega⟩

def laterOrdinal (source : C) (past future : Script) (ordinal : Ordinal (endAt source past) future) :
    Ordinal source (past ++ future) :=
  ⟨(inventory source past).length + ordinal.val, by rw [inventory_append, List.length_append]; omega⟩

theorem prior_and_later_service_ordinals_are_disjoint
    (source : C) (past future : Script) (left : Ordinal source past) (right : Ordinal (endAt source past) future) :
    priorOrdinal source past future left ≠ laterOrdinal source past future right := by
  intro equal
  have same := congrArg Fin.val equal
  change left.val = (inventory source past).length + right.val at same
  have inside := left.isLt
  omega

private theorem timed_length (source : C) (script : Script) :
    (timedInventory source script).length = (inventory source script).length := by
  rw [← timedInventory_is_the_original_inventory source script, List.length_map]

private theorem timed_get (source : C) (script : Script) (ordinal : Ordinal source script) :
    (timedInventory source script)[ordinal.val]? = some (timedAt source script ordinal) := by
  unfold timedAt
  exact List.getElem?_eq_getElem _

theorem prior_ordinal_keeps_its_exact_original_receipt_and_clock
    (source : C) (past future : Script) (ordinal : Ordinal source past) :
    timedAt source (past ++ future) (priorOrdinal source past future ordinal) = timedAt source past ordinal := by
  have proof := timed_get source (past ++ future) (priorOrdinal source past future ordinal)
  rw [timedInventory_append] at proof
  change ((timedInventory source past) ++ (timedInventory (endAt source past) future))[ordinal.val]? = _ at proof
  rw [List.getElem?_append_left (by rw [timed_length]; exact ordinal.isLt), timed_get] at proof
  exact (Option.some.inj proof).symm

theorem later_ordinal_keeps_its_exact_original_receipt_and_clock
    (source : C) (past future : Script) (ordinal : Ordinal (endAt source past) future) :
    timedAt source (past ++ future) (laterOrdinal source past future ordinal) =
      timedAt (endAt source past) future ordinal := by
  have proof := timed_get source (past ++ future) (laterOrdinal source past future ordinal)
  rw [timedInventory_append] at proof
  change ((timedInventory source past) ++
    (timedInventory (endAt source past) future))[(inventory source past).length + ordinal.val]? = _ at proof
  rw [List.getElem?_append_right (by rw [timed_length]; omega), timed_length,
    Nat.add_sub_cancel_left, timed_get] at proof
  exact (Option.some.inj proof).symm

theorem the_carried_service_has_the_same_original_whole_next (source : C) (past future : Script) :
    Recorded source (past ++ future) ∧ endAt source (past ++ future) = endAt (endAt source past) future :=
  ⟨record source _, endAt_append source past future⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
