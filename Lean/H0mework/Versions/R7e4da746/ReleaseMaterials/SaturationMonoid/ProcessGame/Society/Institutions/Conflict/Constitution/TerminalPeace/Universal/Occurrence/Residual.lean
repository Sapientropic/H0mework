import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Write

/-!
The cleared or outstanding disposition reads the unique original address
in the actual whole ledger after an arbitrary finite dual-signed suffix.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community
local notation "Row" => Loss × Balance

private def findRow (loss : Loss) (rows : List Row) : Option Row :=
  rows.find? fun row => decide (row.1.address = loss.address)

private theorem row_found (loss : Loss) (rows : List Row) (listed : loss ∈ rows.map Prod.fst) :
    (findRow loss rows).isSome := by
  obtain ⟨⟨found, before⟩, mem, same⟩ := List.mem_map.mp listed
  change found = loss at same
  subst found
  exact List.find?_isSome.mpr ⟨(loss, before), mem, by simp⟩

/-- Scan the existing rows at the loss's original address. Membership
comes from the dispatcher, so the scan has no synthetic default. -/
def balanceIn (loss : Loss) (rows : List Row) (listed : loss ∈ rows.map Prod.fst) : Balance :=
  ((findRow loss rows).get (row_found loss rows listed)).2

theorem balanceIn_mem (loss : Loss) (rows : List Row) (listed : loss ∈ rows.map Prod.fst)
    (unique : (rows.map fun row => row.1.address).Nodup) :
    (loss, balanceIn loss rows listed) ∈ rows := by
  let row := (findRow loss rows).get (row_found loss rows listed)
  have read : findRow loss rows = some row := (Option.some_get (row_found loss rows listed)).symm
  have actual : row ∈ rows := List.mem_of_find?_eq_some read
  have key : row.1.address = loss.address := of_decide_eq_true
    (List.find?_some (p := fun (candidate : Row) => decide (candidate.1.address = loss.address)) read)
  obtain ⟨⟨found, before⟩, mem, same⟩ := List.mem_map.mp listed
  change found = loss at same
  subst found
  have sameRow : row = (loss, before) := List.inj_on_of_nodup_map unique actual mem key
  have origin : row.1 = loss := congrArg Prod.fst sameRow
  change (loss, row.2) ∈ rows
  have aligned : row = (loss, row.2) := Prod.ext origin rfl
  exact aligned ▸ actual

theorem an_address_has_only_its_original_balance (rows : List Row)
    (unique : (rows.map fun row => row.1.address).Nodup)
    (loss : Loss) {left right : Balance}
    (first : (loss, left) ∈ rows) (second : (loss, right) ∈ rows) : left = right :=
  congrArg Prod.snd (List.inj_on_of_nodup_map unique first second rfl)

variable (answers : ReceiptAnswers seed) (loss : Reparation.Actual.Occurrence seed community)
  (suffix : Reparation.Actual.Script Party Good Port Technology Instrument)

theorem the_origin_is_in_the_reached_rows :
    loss ∈ (reached answers loss suffix).stack.balances.map Prod.fst := by
  rw [reached_origins answers loss suffix]
  exact the_original_occurrence_stays_listed (history loss) suffix loss (origin_in_material_history loss)

def balance : Balance :=
  balanceIn loss (reached answers loss suffix).stack.balances (the_origin_is_in_the_reached_rows answers loss suffix)

theorem balance_is_in_the_reached_rows :
    (loss, balance answers loss suffix) ∈ (reached answers loss suffix).stack.balances :=
  balanceIn_mem loss _ _ (reached_has_one_row_per_original_address answers loss suffix)

theorem reached_reads_exact_origin :
    ∃ row, (reached answers loss suffix).read row = .inr (loss, balance answers loss suffix) :=
  (reached answers loss suffix).every_balance_is_a_row_of_the_current _
    (balance_is_in_the_reached_rows answers loss suffix)

def residual : Party × Good × ℚ :=
  (loss.key.1, loss.key.2.2, (balance answers loss suffix).remaining)

/-- Inspect the old row's own paid or obstruction face after the actual
whole write. Even zero stays at the original occurrence address. -/
def inspect : Paid (.live (balance answers loss suffix)) ⊕ Obstruction (.live (balance answers loss suffix)) :=
  if settled : (balance answers loss suffix).remaining = 0 then .inl ⟨settled⟩
  else .inr ⟨lt_of_le_of_ne (balance answers loss suffix).nonnegative (Ne.symm settled)⟩

theorem a_cleared_original_row_is_still_readable
    (cleared : Paid (.live (balance answers loss suffix))) :
    ∃ row, (reached answers loss suffix).read row = .inr (loss, balance answers loss suffix) ∧
      (balance answers loss suffix).remaining = 0 := by
  obtain ⟨row, exactRow⟩ := reached_reads_exact_origin answers loss suffix
  exact ⟨row, exactRow, cleared.down⟩

theorem a_blocked_original_row_has_its_exact_named_residual
    (blocked : Obstruction (.live (balance answers loss suffix))) :
    ∃ row, (reached answers loss suffix).read row = .inr (loss, balance answers loss suffix) ∧
      residual answers loss suffix =
        (loss.key.1, loss.key.2.2, (balance answers loss suffix).remaining) ∧
      0 < (residual answers loss suffix).2.2 := by
  obtain ⟨row, exactRow⟩ := reached_reads_exact_origin answers loss suffix
  exact ⟨row, exactRow, rfl, blocked.down⟩

theorem every_actual_suffix_returns_its_original_settlement_or_named_shortfall :
    ((balance answers loss suffix).remaining = 0 ∨ 0 < (residual answers loss suffix).2.2) ∧
      (∃ row, (reached answers loss suffix).read row = .inr (loss, balance answers loss suffix)) := by
  refine ⟨?_, reached_reads_exact_origin answers loss suffix⟩
  cases inspect answers loss suffix with
  | inl paid => exact Or.inl paid.down
  | inr blocked => exact Or.inr blocked.down

#print axioms balance_is_in_the_reached_rows
#print axioms every_actual_suffix_returns_its_original_settlement_or_named_shortfall

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
