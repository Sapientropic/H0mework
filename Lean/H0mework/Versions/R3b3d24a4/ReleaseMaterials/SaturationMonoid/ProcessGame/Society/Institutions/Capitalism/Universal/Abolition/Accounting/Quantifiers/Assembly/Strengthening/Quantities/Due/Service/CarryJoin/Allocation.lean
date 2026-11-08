import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.CarryJoin.Incidence
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline.Capacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Execution
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past future : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ids : Finset TaskId} {task : TaskId → PublicTaskSpec Party Good} {booked : Finset (Ordinal source past)}

local notation "Old" => network source past ids task booked
local notation "Combined" => network source (past ++ future) ids task (carryReservations source past future booked)
local notation "Later" => Supply (endAt source past) future ids task

def joinedAllocation (receipt : Network.Certificate Old) (later : Need ids task → Later → ℚ)
    (line : Need ids task) (item : Supply source (past ++ future) ids task) : ℚ :=
  Sum.elim (receipt.allocation line) (later line) ((carriedSupply source past future ids task).symm item)

theorem the_joined_row_is_the_sum_of_its_old_and_new_payments
    (receipt : Network.Certificate Old) (later : Need ids task → Later → ℚ) (line : Need ids task) :
    Network.rowTotal (joinedAllocation receipt later) line =
      Network.rowTotal receipt.allocation line + Network.rowTotal later line := by
  let original := carriedSupply source past future ids task
  unfold Network.rowTotal
  calc
    _ = ∑ item : Supply source past ids task ⊕ Later,
        Sum.elim (receipt.allocation line) (later line) item := by
      symm
      apply Fintype.sum_equiv original
      intro item
      simp [joinedAllocation, original]
    _ = _ := by rw [Fintype.sum_sum_type]; rfl

theorem joined_original_allocations_are_conservative
    (receipt : Network.Certificate Old) {later : Need ids task → Later → ℚ}
    (fresh : (carryNetwork receipt future ∅).Admissible later) :
    (Combined).Admissible (joinedAllocation receipt later) := by
  let original := carriedSupply source past future ids task
  refine ⟨?_, ?_, ?_⟩
  · intro line item
    obtain ⟨old | new, rfl⟩ := original.surjective item
    · have same := (carried_left_incidence source past future ids task booked line old).1
      change 0 ≤ joinedAllocation receipt later line (original (.inl old)) ∧ _
      simp only [joinedAllocation, original, Equiv.symm_apply_apply, Sum.elim_inl]
      refine ⟨(receipt.admitted.1 line old).1, fun denied => ?_⟩
      exact (receipt.admitted.1 line old).2 (same.symm.trans denied)
    · have same := (carried_right_incidence source past future ids task booked line new).1
      change 0 ≤ joinedAllocation receipt later line (original (.inr new)) ∧ _
      simp only [joinedAllocation, original, Equiv.symm_apply_apply, Sum.elim_inr]
      refine ⟨(fresh.1 line new).1, fun denied => ?_⟩
      exact (fresh.1 line new).2 (same.symm.trans denied)
  · intro line
    rw [the_joined_row_is_the_sum_of_its_old_and_new_payments]
    have fits := fresh.2.1 line
    change Network.rowTotal later line ≤ (Old).need line - Network.rowTotal receipt.allocation line at fits
    change _ ≤ (Old).need line
    linarith only [fits]
  · intro item
    obtain ⟨old | new, rfl⟩ := original.surjective item
    · rw [carried_left_capacity source past future ids task booked old]
      simpa only [Network.columnTotal, joinedAllocation, original, Equiv.symm_apply_apply, Sum.elim_inl]
        using receipt.admitted.2.2 old
    · rw [carried_right_capacity source past future ids task booked new]
      have bound := fresh.2.2 new
      change Network.columnTotal later new ≤ (network (endAt source past) future ids task ∅).capacity new at bound
      simpa only [Network.columnTotal, joinedAllocation, original, Equiv.symm_apply_apply, Sum.elim_inr] using bound

/-- A newly paid remainder and the old amount fund the original row on
two disjoint sets of native ordinals. No prior payment is reallocated. -/
theorem paying_the_residual_pays_the_same_original_due_prefix
    (receipt : Network.Certificate Old) (due : Need ids task → ℚ) (time : ℚ)
    (fresh : Deadline.ServedThrough (carryNetwork receipt future ∅) due time) :
    Deadline.ServedThrough (Combined) due time := by
  obtain ⟨later, admitted, paid⟩ := fresh
  refine ⟨joinedAllocation receipt later, joined_original_allocations_are_conservative receipt admitted, ?_⟩
  intro line matured
  rw [the_joined_row_is_the_sum_of_its_old_and_new_payments]
  have exactAmount := paid line matured
  change Network.rowTotal later line = (Old).need line - Network.rowTotal receipt.allocation line at exactAmount
  change _ = (Old).need line
  linarith only [exactAmount]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
