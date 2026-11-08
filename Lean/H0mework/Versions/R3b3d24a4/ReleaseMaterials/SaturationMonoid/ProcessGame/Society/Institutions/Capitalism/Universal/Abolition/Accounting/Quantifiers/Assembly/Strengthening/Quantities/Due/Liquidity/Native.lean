import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.FirstFailure
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Row : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
abbrev OriginalOrdinal (source : C) (script : Script) := Fin (Execution.inventory source script).length

/-- The latest original query prefix with material committed by this time.
All queries sharing the boundary clock are included in their actual order. -/
def committedPrefix (time : ℚ) : C → Script → Script
  | _, [] => []
  | source, proposal :: tail =>
    let next := Execution.next source proposal
    if next.raw.clock ≤ time then
      proposal :: committedPrefix time next tail
    else []

theorem committedPrefix_is_prefix (time : ℚ) (source : C) (script : Script) :
    ∃ rest, script = committedPrefix time source script ++ rest := by
  induction script generalizing source with
  | nil => exact ⟨[], rfl⟩
  | cons proposal tail step =>
    by_cases fits : (Execution.next source proposal).raw.clock ≤ time
    · obtain ⟨rest, split⟩ := step (Execution.next source proposal)
      exact ⟨rest, by simp only [committedPrefix, if_pos fits, List.cons_append]; rw [← split]⟩
    · exact ⟨proposal :: tail, by simp [committedPrefix, fits]⟩

theorem committedPrefix_all (time : ℚ) (source : C) (script : Script)
    (finished : (Execution.endAt source script).raw.clock ≤ time) :
    committedPrefix time source script = script := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail step =>
    let next := Execution.next source proposal
    have tailDone : (Execution.endAt next tail).raw.clock ≤ time := finished
    have fits : next.raw.clock ≤ time :=
      (Execution.the_actual_script_never_runs_the_clock_backwards next tail).trans tailDone
    change (if next.raw.clock ≤ time then proposal :: committedPrefix time next tail else []) = proposal :: tail
    rw [if_pos fits, step next tailDone]

theorem committed_items_are_the_actual_prefix (time : ℚ) (source : C) (script : Script) :
    (Execution.timedInventory source script).filter (fun item => decide (item.2 ≤ time)) =
      Execution.timedInventory source (committedPrefix time source script) := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail step =>
    let next := Execution.next source proposal
    let first := Optimality.Programme.Epoch.materialItems (Execution.query source proposal)
    change ((first.map (·, next.raw.clock)) ++ Execution.timedInventory next tail).filter
      (fun item => decide (item.2 ≤ time)) = _
    rw [List.filter_append]
    by_cases fits : next.raw.clock ≤ time
    · have firstAll : (first.map (·, next.raw.clock)).filter (fun item => decide (item.2 ≤ time)) =
          first.map (·, next.raw.clock) := by
        apply List.filter_eq_self.mpr
        intro item original
        obtain ⟨raw, _, rfl⟩ := List.mem_map.mp original
        exact decide_eq_true fits
      rw [firstAll, step next]
      simp [committedPrefix, next, fits, Execution.timedInventory, first]
    · have firstNone : (first.map (·, next.raw.clock)).filter (fun item => decide (item.2 ≤ time)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro item original
        obtain ⟨raw, _, rfl⟩ := List.mem_map.mp original
        simpa using fits
      have tailNone : (Execution.timedInventory next tail).filter (fun item => decide (item.2 ≤ time)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro item listed present
        exact fits ((Execution.every_original_service_commits_between_source_and_terminal_clock next tail item listed).1.trans
          (of_decide_eq_true present))
      rw [firstNone, tailNone]
      simp [committedPrefix, next, fits, Execution.timedInventory]

/-- Read the exact material ledger and the exact committing ordinals.
The due allocation can use the same ordinal type as the fractional service certificate. -/
def profile (source : C) (script : Script) (address : Row → Party × Good) (deadline required : Row → ℚ)
    (paid : Row → OriginalOrdinal source script → ℚ) : Profile (Party × Good) Row (OriginalOrdinal source script) where
  start := source.raw.clock
  opening := fun key => source.raw.stock key.1 key.2
  commit := fun i => (Execution.timedAt source script i).2
  credit := fun i key =>
    let item := (Execution.timedAt source script i).1
    flowAt (source.native.handlerFace.rootRead.actualCredit item.before item.request) key.1 key.2
  debit := fun i key =>
    let item := (Execution.timedAt source script i).1
    flowAt (source.native.handlerFace.rootRead.actualDebit item.before item.request) key.1 key.2
  address := address
  deadline := deadline
  required := required
  paid := paid

private theorem sum_timed (source : C) (script : Script) (read : Item × ℚ → ℚ) :
    (∑ i : OriginalOrdinal source script, read (Execution.timedAt source script i)) =
      ((Execution.timedInventory source script).map read).sum := by
  have length : (Execution.inventory source script).length = (Execution.timedInventory source script).length := by
    rw [← Execution.timedInventory_is_the_original_inventory source script, List.length_map]
  calc
    _ = ∑ i : Fin (Execution.timedInventory source script).length,
          read ((Execution.timedInventory source script).get i) :=
      Fintype.sum_equiv (finCongr length) _ _ (fun _ => rfl)
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map _ _

private theorem sum_committed {A : Type*} (items : List (A × ℚ)) (time : ℚ) (read : A → ℚ) :
    (items.map (fun item => if item.2 ≤ time then read item.1 else 0)).sum =
      (((items.filter (fun item => decide (item.2 ≤ time))).map Prod.fst).map read).sum := by
  induction items with
  | nil => rfl
  | cons item tail step =>
    by_cases fits : item.2 ≤ time <;> simp [fits, step]

theorem profile_stock_is_original_stock_at_the_commit_cut
    (source : C) (script : Script) (address : Row → Party × Good) (deadline required : Row → ℚ)
    (paid : Row → OriginalOrdinal source script → ℚ) (time : ℚ) (key : Party × Good) :
    (profile source script address deadline required paid).actualStock time key =
      (Execution.endAt source (committedPrefix time source script)).raw.stock key.1 key.2 := by
  let law := source.native.handlerFace.rootRead
  let credit := fun item : Item => flowAt (law.actualCredit item.before item.request) key.1 key.2
  let debit := fun item : Item => flowAt (law.actualDebit item.before item.request) key.1 key.2
  have committed (read : Item → ℚ) :
      (∑ i : OriginalOrdinal source script, if (Execution.timedAt source script i).2 ≤ time
        then read (Execution.timedAt source script i).1 else 0) =
        ((Execution.inventory source (committedPrefix time source script)).map read).sum := by
    rw [sum_timed source script (fun item => if item.2 ≤ time then read item.1 else 0), sum_committed,
      committed_items_are_the_actual_prefix, Execution.timedInventory_is_the_original_inventory]
  change source.raw.stock key.1 key.2 +
    (∑ i : OriginalOrdinal source script, if (Execution.timedAt source script i).2 ≤ time
      then credit (Execution.timedAt source script i).1 else 0) -
    (∑ i : OriginalOrdinal source script, if (Execution.timedAt source script i).2 ≤ time
      then debit (Execution.timedAt source script i).1 else 0) = _
  rw [committed credit, committed debit]
  have balance := all_capacity_is_paid_from_the_original_stock_and_actual_credits
    source (committedPrefix time source script) key.1 key.2
  change _ + ((Execution.inventory source (committedPrefix time source script)).map debit).sum =
    _ + ((Execution.inventory source (committedPrefix time source script)).map credit).sum at balance
  exact (eq_sub_of_add_eq balance).symm

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity
