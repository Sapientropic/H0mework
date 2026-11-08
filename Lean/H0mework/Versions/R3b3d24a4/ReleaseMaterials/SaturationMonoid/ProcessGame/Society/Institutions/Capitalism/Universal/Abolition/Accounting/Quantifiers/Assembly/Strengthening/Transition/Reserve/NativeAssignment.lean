import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Assignment
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

open Source.Program Abolition.Root Abolition.Root.Registered Quantities

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
variable {Row : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Address" => Party × Good

/-- Legacy and replacement payments use one original ordinal type, across
both the already paid prefix and the remaining bridge. -/
noncomputable def originalRemainingAfter (source : C) (prior script : Script) (required : Row → ℚ)
    (paid : Row → Due.Liquidity.OriginalOrdinal source (prior ++ script) → ℚ) : Row → ℚ :=
  initialRemaining required (paidBefore paid (Execution.timedInventory source prior).length)

theorem originalRemainingAfter_nonnegative [Fintype Row] (source : C) (prior script : Script)
    (address : Row → Address) (deadline required : Row → ℚ)
    (paid : Row → Due.Liquidity.OriginalOrdinal source (prior ++ script) → ℚ)
    (accounted : (Due.Liquidity.profile source (prior ++ script) address deadline required paid).Conservative)
    (row : Row) :
    0 ≤ originalRemainingAfter source prior script required paid row :=
  sub_nonneg.mpr (original_prefix_payment_le_required accounted _ row)

theorem the_original_material_step_preserves_the_exact_unpaid_row
    (source : C) (script : Script) (required : Row → ℚ)
    (paid : Row → Due.Liquidity.OriginalOrdinal source script → ℚ)
    (i : Due.Liquidity.OriginalOrdinal source script) :
    let step := readStep source.native.handlerFace.rootRead (assignedAt paid)
      (Execution.timedAt source script i) i.val
    step.after (initialRemaining required (paidBefore paid i.val)) =
      initialRemaining required (paidBefore paid (i.val + 1)) := by
  funext row
  simp only [Step.after, initialRemaining, readStep, assignedAt_original, paidBefore_next]
  exact sub_sub _ _ _

theorem the_original_material_step_cannot_pay_two_rosters_with_one_debit
    [Fintype Row] [DecidableEq Row] (source : C) (script : Script) (address : Row → Address)
    (deadline required : Row → ℚ) (paid : Row → Due.Liquidity.OriginalOrdinal source script → ℚ)
    (accounted : (Due.Liquidity.profile source script address deadline required paid).Conservative)
    (rows : List Row) (once : rows.Nodup)
    (i : Due.Liquidity.OriginalOrdinal source script) (key : Address)
    (step : Step Row Address (ℕ × Item))
    (actual : (originalSteps source script (assignedAt paid))[i.val]? = some step) :
    held rows address step.paid key ≤ step.debit key := by
  have same := Option.some.inj ((originalSteps_at source script (assignedAt paid) i).symm.trans actual)
  rw [← same]
  exact debit_pays_the_old_and_new_rows_only_once accounted rows once i key

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
