import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Residual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}

local notation "Rows" => Service.Need ordered.toFinset task
local notation "Receipt" => Network.Certificate (Service.network source past ordered.toFinset task reserved)
local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Now" => Execution.endAt source past

/-- Values extracted from one original service row. The runtime uses
only the explicit data, with each value authenticated at that row. -/
structure RowRead (receipt : Receipt) (sign : Rows → Request) where
  row : Rows
  remaining : ℚ
  earliest : ℚ
  deadline : ℚ
  bearer : Party
  good : Good
  purpose : Use
  signed : Request
  remaining_exact : remaining = Service.remaining receipt row
  earliest_exact : earliest = (task row.1.1.val).earliest
  deadline_exact : deadline = (task row.1.1.val).deadline
  bearer_exact : bearer = row.1.spec.bearer
  good_exact : good = row.2.val
  purpose_exact : purpose = row.1.spec.purpose
  signed_exact : signed = sign row

structure ScheduleRead (receipt : Receipt) (sign : Rows → Request) where
  clock : ℚ
  clock_exact : clock = (Now).raw.clock
  rows : List (RowRead receipt sign)
  rows_exact : rows.map RowRead.row = (Service.needList ordered.toFinset task ordered rfl).dedup

variable {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}

def nativeRequest (signed : Request) (bearer : Party) (good : Good) (remaining : ℚ) (purpose : Use) : Request :=
  { signed with consents := [], operation := .use bearer [(good, remaining)] purpose }

def RowRead.request (read : RowRead receipt sign) : Request :=
  nativeRequest read.signed read.bearer read.good read.remaining read.purpose

private theorem RowRead.request_exact (read : RowRead receipt sign) :
    read.request = residualUse receipt read.row (sign read.row) := by
  simp only [request, nativeRequest, residualUse, read.signed_exact, read.bearer_exact, read.good_exact,
    read.remaining_exact, read.purpose_exact]

def selectRows {A : Type*} (clock : ℚ) (rows : List A) (remaining deadline : A → ℚ) : List A :=
  rows.filter fun read => decide (deadline read ≤ clock ∧ 0 < remaining read)

private def numericWindow {A : Type*} (clock : ℚ) (earliest deadline : A → ℚ) (read : A) : Prop :=
  earliest read ≤ clock ∧ clock ≤ deadline read

private instance {A : Type*} (clock : ℚ) (earliest deadline : A → ℚ) (read : A) :
    Decidable (numericWindow clock earliest deadline read) := by
  unfold numericWindow
  infer_instance

def scanRows {A : Type*} (clock : ℚ) (rows : List A) (remaining earliest deadline : A → ℚ) :=
  Abolition.Material.inspectList (numericWindow clock earliest deadline) (selectRows clock rows remaining deadline)

/-- Executable projection of the checked scheduler using already-read
row values. The loaded clock and rows are its only runtime inputs. -/
def readWord {A B : Type*} (clock : ℚ) (rows : List A) (remaining earliest deadline : A → ℚ)
    (request : A → B) : Sum A (List B) :=
  match scanRows clock rows remaining earliest deadline with
  | .failure read _ _ => .inl read
  | .clear _ => .inr ((selectRows clock rows remaining deadline).map request)

private def selected (input : ScheduleRead receipt sign) : List (RowRead receipt sign) :=
  selectRows input.clock input.rows RowRead.remaining RowRead.deadline

private theorem selected_rows_exact (input : ScheduleRead receipt sign) :
    (selected input).map RowRead.row = residualRows receipt input.clock := by
  let numeric := fun (read : RowRead receipt sign) => decide (read.deadline ≤ input.clock ∧ 0 < read.remaining)
  let original := fun (row : Rows) =>
    decide ((task row.1.1.val).deadline ≤ input.clock ∧ 0 < Service.remaining receipt row)
  have same (read : RowRead receipt sign) : numeric read = original read.row := by
    simp only [numeric, original, read.deadline_exact, read.remaining_exact]
  change (input.rows.filter numeric).map RowRead.row =
    ((Service.needList ordered.toFinset task ordered rfl).dedup).filter original
  rw [← input.rows_exact, List.filter_map]
  congr 1
  apply List.filter_congr
  intro read _
  exact same read

private theorem requests_are_the_original_word (input : ScheduleRead receipt sign) :
    (selected input).map RowRead.request = residualWord receipt input.clock sign := by
  unfold residualWord
  rw [← selected_rows_exact input, List.map_map]
  exact List.map_congr_left (fun read _ => read.request_exact)

private theorem window_exact (input : ScheduleRead receipt sign) (read : RowRead receipt sign) :
    numericWindow input.clock RowRead.earliest RowRead.deadline read ↔ InWindow (Now).raw.clock read.row := by
  unfold numericWindow InWindow
  rw [input.clock_exact, read.earliest_exact, read.deadline_exact]

inductive ScheduleDecision (receipt : Receipt) (sign : Rows → Request) (input : ScheduleRead receipt sign)
  | window (row : Rows) (original : row ∈ residualRows receipt input.clock)
      (unavailable : ¬ InWindow (Now).raw.clock row)
  | ready (word : Word) (exactWord : word = residualWord receipt input.clock sign)
      (timely : ∀ row ∈ residualRows receipt input.clock, InWindow (Now).raw.clock row)

def ScheduleDecision.readout {input : ScheduleRead receipt sign} :
    ScheduleDecision receipt sign input → Sum Rows Word
  | .window row _ _ => .inl row
  | .ready word _ _ => .inr word

/-- Scan the authenticated clock and rows, retaining either the literal
native word or the selected original row that cannot be paid now. -/
def schedule (input : ScheduleRead receipt sign) : ScheduleDecision receipt sign input :=
  match scanRows input.clock input.rows RowRead.remaining RowRead.earliest RowRead.deadline with
  | .failure read original blocked =>
    .window read.row (selected_rows_exact input ▸ List.mem_map.mpr ⟨read, original, rfl⟩)
      (fun timely => blocked ((window_exact input read).mpr timely))
  | .clear timely => .ready ((selected input).map RowRead.request) (requests_are_the_original_word input) (by
    intro row original
    rw [← selected_rows_exact input] at original
    obtain ⟨read, listed, rfl⟩ := List.mem_map.mp original
    exact (window_exact input read).mp (timely read listed))

theorem readWord_is_the_exact_schedule_readout (input : ScheduleRead receipt sign) :
    (readWord input.clock input.rows RowRead.remaining RowRead.earliest RowRead.deadline RowRead.request).map
        RowRead.row id = (schedule input).readout := by
  unfold readWord schedule
  cases scanRows input.clock input.rows RowRead.remaining RowRead.earliest RowRead.deadline <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime
