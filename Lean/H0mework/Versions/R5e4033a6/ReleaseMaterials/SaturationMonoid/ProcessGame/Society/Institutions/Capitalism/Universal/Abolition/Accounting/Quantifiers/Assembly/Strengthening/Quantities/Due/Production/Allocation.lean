import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Delivery
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline.Capacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open scoped BigOperators
open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}

local notation "Rows" => Service.Need ordered.toFinset task

variable {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {dueBy : ℚ}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}
  {held : RawEvent Party Good Port Technology Instrument}

local notation "Now" => Execution.endAt source past
local notation "Suffix" => Execution.primitiveScript (residualWord receipt dueBy sign)
local notation "Paid" => PaymentAt Now (residualWord receipt dueBy sign) held
local notation "Supplies" => Service.Supply Now Suffix ordered.toFinset task
local notation "Carry" => Service.carryNetwork receipt Suffix ∅

def assignedResidual (payment : Paid) (line : Rows) (item : Supplies) : ℚ :=
  if paidRow payment item.1 = line ∧ item.2 = Settlement.originalUnit line then
    Service.remaining receipt line else 0

theorem a_native_residual_pays_exactly_the_rows_it_submits (payment : Paid) (line : Rows) :
    Network.rowTotal (assignedResidual payment) line =
      if line ∈ residualRows receipt dueBy then Service.remaining receipt line else 0 := by
  unfold Network.rowTotal
  by_cases listed : line ∈ residualRows receipt dueBy
  · obtain ⟨ordinal, original⟩ := (every_selected_row_gets_its_own_new_ordinal payment line).mp listed
    let item : Supplies := (ordinal, Settlement.originalUnit line)
    rw [if_pos listed, Finset.sum_eq_single item]
    · simp [assignedResidual, item, original]
    · intro other _ unequal
      unfold assignedResidual
      refine if_neg (fun ⟨row, unit⟩ => unequal (Prod.ext ?_ unit))
      exact paidRow_is_injective payment (row.trans original.symm)
    · simp
  · rw [if_neg listed]
    apply Finset.sum_eq_zero
    intro item _
    unfold assignedResidual
    apply if_neg
    rintro ⟨same, _⟩
    exact listed (same ▸ paidRow_is_original payment item.1)

theorem the_original_suffix_pays_every_requested_unpaid_due_row
    (payment : Paid) (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line) :
    Deadline.ServedThrough Carry Settlement.deadline dueBy := by
  have nonnegative (line : Rows) : 0 ≤ Service.remaining receipt line :=
    sub_nonneg.mpr (receipt.admitted.2.1 line)
  refine ⟨assignedResidual payment, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro line item
    unfold assignedResidual
    split
    · rename_i linked
      refine ⟨nonnegative line, fun denied => ?_⟩
      have own : item = (item.1, Settlement.originalUnit (paidRow payment item.1)) := by
        exact Prod.ext rfl (linked.2.trans (congrArg Settlement.originalUnit linked.1).symm)
      have allowed := (paid_residual_is_eligible_for_its_original_window payment timely item.1).1
      rw [← own, linked.1] at allowed
      have authorized := (Service.network_allows_iff Now Suffix ordered.toFinset task ∅ line item).mpr allowed
      change (Service.network Now Suffix ordered.toFinset task ∅).allows line item = false at denied
      rw [authorized] at denied
      cases denied
    · exact ⟨le_rfl, fun _ => rfl⟩
  · intro line
    rw [a_native_residual_pays_exactly_the_rows_it_submits]
    split
    · exact le_rfl
    · exact nonnegative line
  · intro item
    unfold Network.columnTotal
    rw [Finset.sum_eq_single (paidRow payment item.1)]
    · by_cases good : item.2 = Settlement.originalUnit (paidRow payment item.1)
      · have own : item = (item.1, Settlement.originalUnit (paidRow payment item.1)) := Prod.ext rfl good
        have exactAmount := (paid_residual_is_eligible_for_its_original_window payment timely item.1).2
        rw [← own] at exactAmount
        simp [assignedResidual, good, exactAmount]
      · simpa [assignedResidual, good] using (Carry).capacity_nonnegative item
    · intro line _ other
      simp [assignedResidual, Ne.symm other]
    · simp
  · intro line matured
    rw [a_native_residual_pays_exactly_the_rows_it_submits]
    by_cases positive : 0 < Service.remaining receipt line
    · exact if_pos ((original_due_and_unpaid_iff_listed receipt dueBy line).mpr ⟨of_decide_eq_true matured, positive⟩)
    · have zero := le_antisymm (le_of_not_gt positive) (nonnegative line)
      change _ = Service.remaining receipt line
      simp [zero]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
