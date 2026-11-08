import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Stock" => Party → Good → ℚ

/-- The original pre-item stocks and terminal stock form one ordered
physical trace, including adjacent material items at the same commit time. -/
def StockTrace (law : RawLaw Party Good Port Technology Instrument) :
    List Item → Stock → Stock → Prop
  | [], opening, closing => opening = closing
  | item :: tail, opening, closing =>
      item.before.stock = opening ∧ StockTrace law tail (law.step item.before item.request).stock closing

theorem StockTrace.append {law : RawLaw Party Good Port Technology Instrument}
    {first second : List Item} {opening middle closing : Stock}
    (front : StockTrace law first opening middle)
    (back : StockTrace law second middle closing) :
    StockTrace law (first ++ second) opening closing := by
  induction first generalizing opening with
  | nil =>
      change opening = middle at front
      simpa only [List.nil_append, front] using back
  | cons item tail ih =>
      exact ⟨front.1, ih front.2⟩

theorem rawExecution_stock_trace (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (index : ℕ)
    (word : RawEvent Party Good Port Technology Instrument) :
    StockTrace law (law.execute before index word).items
      before.stock (law.execute before index word).final.stock := by
  induction word generalizing before index with
  | nil => rfl
  | cons request tail ih => exact ⟨rfl, ih (law.step before request) (index + 1)⟩

private theorem compiler_stock_trace
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    let result := Physical.Public.compile input before raw
    StockTrace (Physical.Public.interpreter input) result.execution.items
      before.raw.stock result.next.raw.stock := by
  dsimp only
  cases Physical.Public.compile input before raw with
  | accepted word selected checked =>
      have trace := rawExecution_stock_trace (Physical.Public.interpreter input) before.raw 0 word
      cases raw <;> exact trace
  | refused word selected item listed failed => rfl
  | metadata selected => rfl

private theorem programme_stock_trace
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (code : Optimality.Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    StockTrace (Physical.Public.interpreter input) (Optimality.Programme.items input before code)
      before.raw.stock (Optimality.Programme.run input before code).raw.stock := by
  induction code generalizing before with
  | nil => rfl
  | cons raw tail ih => exact (compiler_stock_trace input before raw).append (ih _)

variable [DecidableEq Port]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem original_inventory_follows_stock (source : C) (script : Script) :
    StockTrace source.native.handlerFace.rootRead (Quantities.Execution.inventory source script)
      source.raw.stock (Quantities.Execution.endAt source script).raw.stock := by
  have trace := programme_stock_trace source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Quantities.Execution.programme source script)
  rw [Quantities.Execution.material_is_the_folded_actual_inventory,
    Quantities.Execution.physical_is_the_folded_actual_end] at trace
  exact trace

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
