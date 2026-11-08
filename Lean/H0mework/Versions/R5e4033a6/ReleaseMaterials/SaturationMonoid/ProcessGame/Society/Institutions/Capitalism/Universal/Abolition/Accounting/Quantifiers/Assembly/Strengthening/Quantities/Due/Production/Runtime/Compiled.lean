import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Plan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "FloorRows" => List ((Party × Use × Good × ℚ) × ℚ)

private def checkWord {A : Type*} (current : Raw) (floor : FloorRows) (law : Law)
    (opening : ∀ party good, 0 ≤ current.stock party good) :
    Sum A Word → Sum A (Σ word, RawPaymentInspection current floor law word)
  | .inl row => .inl row
  | .inr word => .inr ⟨word, inspectRawPayment current floor law word opening⟩

/-- Executable calendar, stock and authorization scan over literal
source readings. The successful branch returns the exact native word. -/
def readAndInspect {A : Type*} (clock : ℚ) (due : List A) (remaining earliest deadline : A → ℚ)
    (request : A → Request) (current : Raw) (floor : FloorRows) (law : Law)
    (opening : ∀ party good, 0 ≤ current.stock party good) :
    Sum A (Σ word, RawPaymentInspection current floor law word) :=
  checkWord current floor law opening (readWord clock due remaining earliest deadline request)

variable {TaskId : Type*} [DecidableEq TaskId]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}
  {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}

theorem the_compiled_scan_is_the_same_original_runtime_inspection
    (input : ScheduleRead receipt sign) (read : Service.Floor.Runtime.Snapshot source past)
    (authority : LawRead (Execution.endAt source past))
    (opening : ∀ party good, 0 ≤ read.current.stock party good) :
    (readAndInspect input.clock input.rows RowRead.remaining RowRead.earliest RowRead.deadline
      RowRead.request read.current read.rows authority.law opening).map RowRead.row id =
      match inspectDue input read authority opening with
      | ⟨.window row _ _, _⟩ => .inl row
      | ⟨.ready word _ _, result⟩ => .inr ⟨word, result⟩ := by
  let numeric := readWord input.clock input.rows RowRead.remaining RowRead.earliest RowRead.deadline RowRead.request
  change (checkWord read.current read.rows authority.law opening numeric).map RowRead.row id = _
  calc
    _ = checkWord read.current read.rows authority.law opening (numeric.map RowRead.row id) := by
      cases numeric <;> rfl
    _ = _ := by
      rw [show numeric.map RowRead.row id = _ from readWord_is_the_exact_schedule_readout input]
      unfold inspectDue
      cases schedule input <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime
