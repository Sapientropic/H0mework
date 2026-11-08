import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past future : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Due.Service.Ordinal source past)}
  {newReserved : Finset (Due.Service.Ordinal (Execution.endAt source past) future)}
  {held : Finset (Due.Service.Need ordered.toFinset task)} {budget : Party × Good → ℚ}

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "NewLot" => Due.Service.Supply (Execution.endAt source past) future ordered.toFinset task
local notation "Split" => Due.Service.carriedSupply source past future ordered.toFinset task

theorem Extension.original_row_is_prior_payment_plus_the_new_ordinals
    {old : PaidPrefix source past ordered task reserved held budget}
    (paid : Extension old future newReserved) (row : Row) :
    Network.rowTotal paid.combined.allocation row = Network.rowTotal old.allocation row +
      ∑ lot : NewLot, paid.combined.allocation row (Split (.inr lot)) := by
  unfold Network.rowTotal
  calc
    _ = ∑ lot, paid.combined.allocation row (Split lot) := by
      symm
      apply Fintype.sum_equiv Split
      intro lot
      rfl
    _ = _ := by
      rw [Fintype.sum_sum_type]
      apply congrArg (fun value => value + _)
      apply Finset.sum_congr rfl
      intro lot _
      rw [Due.Service.carriedSupply_left]
      exact paid.kept row lot

theorem Extension.a_fully_paid_original_row_cannot_draw_from_a_new_debit
    {old : PaidPrefix source past ordered task reserved held budget}
    (paid : Extension old future newReserved) (row : Row) (lot : NewLot)
    (closed : Network.rowTotal old.allocation row =
      (Due.Service.network source past ordered.toFinset task reserved).need row) :
    paid.combined.allocation row (Split (.inr lot)) = 0 := by
  have admitted := paid.combined.fits.1.1
  have total := admitted.2.1 row
  rw [paid.original_row_is_prior_payment_plus_the_new_ordinals row, closed] at total
  change (Due.Service.network source past ordered.toFinset task reserved).need row +
      (∑ item : NewLot, paid.combined.allocation row (Split (.inr item))) ≤
      (Due.Service.network source past ordered.toFinset task reserved).need row at total
  have nonnegative (item : NewLot) := (admitted.1 row (Split (.inr item))).1
  have part : paid.combined.allocation row (Split (.inr lot)) ≤
      ∑ item : NewLot, paid.combined.allocation row (Split (.inr item)) :=
    Finset.single_le_sum (fun item _ => nonnegative item) (Finset.mem_univ lot)
  exact le_antisymm (part.trans (by linarith only [total])) (nonnegative lot)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation
