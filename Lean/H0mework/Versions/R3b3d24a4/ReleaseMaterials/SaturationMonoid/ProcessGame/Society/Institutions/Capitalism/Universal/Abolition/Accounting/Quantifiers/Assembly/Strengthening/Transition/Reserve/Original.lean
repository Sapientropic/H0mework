import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Opening
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.StockTrace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

open Source.Program Abolition.Root Abolition.Root.Registered

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]
variable {Row : Type*}

local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Stock" => Party → Good → ℚ
local notation "BridgeStep" => Step Row (Party × Good) (ℕ × Item)

def readStep (law : RawLaw Party Good Port Technology Instrument)
    (paid : Row → ℕ → ℚ) (entry : Item × ℚ) (position : ℕ) : BridgeStep where
  item := (position, entry.1)
  clock := entry.2
  debit := fun key => flowAt (law.actualDebit entry.1.before entry.1.request) key.1 key.2
  credit := fun key => flowAt (law.actualCredit entry.1.before entry.1.request) key.1 key.2
  paid := fun row => paid row position

/-- The input is the ordered native material inventory. The ordinal keeps
distinct actions at one clock value and is global across the original cut. -/
def readSteps (law : RawLaw Party Good Port Technology Instrument)
    (paid : Row → ℕ → ℚ) : List (Item × ℚ) → ℕ → List BridgeStep
  | [], _ => []
  | item :: tail, position =>
      readStep law paid item position :: readSteps law paid tail (position + 1)

theorem readSteps_at (law : RawLaw Party Good Port Technology Instrument)
    (paid : Row → ℕ → ℚ) (items : List (Item × ℚ)) (offset index : ℕ) :
    (readSteps law paid items offset)[index]? =
      items[index]?.map (fun entry => readStep law paid entry (offset + index)) := by
  induction items generalizing offset index with
  | nil => rfl
  | cons item tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simpa only [readSteps, List.getElem?_cons_succ, Nat.succ_eq_add_one,
            Nat.add_right_comm offset 1 index, Nat.add_assoc] using ih (offset + 1) index

theorem readSteps_append (law : RawLaw Party Good Port Technology Instrument)
    (paid : Row → ℕ → ℚ) (first second : List (Item × ℚ)) (offset : ℕ) :
    readSteps law paid (first ++ second) offset =
      readSteps law paid first offset ++ readSteps law paid second (offset + first.length) := by
  induction first generalizing offset with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.cons_append, readSteps, List.length_cons, ih,
        Nat.add_right_comm offset 1 tail.length, Nat.add_assoc]

/-- Real pre-item stocks are reconstructed by the very same balances used
by the reserve scan. The terminal stock is the original raw successor. -/
def ReadsStock (key : Party × Good) : List BridgeStep → ℚ → ℚ → Prop
  | [], opening, closing => opening = closing
  | step :: tail, opening, closing =>
      step.item.2.before.stock key.1 key.2 = opening ∧
        ReadsStock key tail (step.balance key opening) closing

variable [DecidableEq Instrument]

theorem readSteps_reads_stock (law : RawLaw Party Good Port Technology Instrument)
    (paid : Row → ℕ → ℚ) (items : List (Item × ℚ)) (offset : ℕ)
    (key : Party × Good) (opening closing : Stock)
    (original : StockTrace law (items.map Prod.fst) opening closing) :
    ReadsStock key (readSteps law paid items offset) (opening key.1 key.2) (closing key.1 key.2) := by
  induction items generalizing opening offset with
  | nil => exact congrFun (congrFun original key.1) key.2
  | cons item tail ih =>
      change item.1.before.stock = opening ∧
        StockTrace law (tail.map Prod.fst) (law.step item.1.before item.1.request).stock closing at original
      change item.1.before.stock key.1 key.2 = opening key.1 key.2 ∧
        ReadsStock key (readSteps law paid tail (offset + 1))
          ((readStep law paid item offset).balance key (opening key.1 key.2)) (closing key.1 key.2)
      refine ⟨congrFun (congrFun original.1 key.1) key.2, ?_⟩
      have balance := law.material_step_balance item.1.before item.1.request key.1 key.2
      have same :
          (readStep law paid item offset).balance key (opening key.1 key.2) =
            (law.step item.1.before item.1.request).stock key.1 key.2 := by
        rw [← original.1]
        exact sub_eq_of_eq_add (by
          simpa only [Step.balance, readStep] using balance.symm)
      rw [same]
      exact ih (offset + 1) _ original.2

section Native

noncomputable section

variable [DecidableEq Port]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

open Quantities

def originalSteps (source : C) (script : Script) (paid : Row → ℕ → ℚ) : List BridgeStep :=
  readSteps source.native.handlerFace.rootRead paid (Execution.timedInventory source script) 0

def stepsAfter (source : C) (prior script : Script) (paid : Row → ℕ → ℚ) : List BridgeStep :=
  readSteps source.native.handlerFace.rootRead paid
    (Execution.timedInventory (Execution.endAt source prior) script)
    (Execution.timedInventory source prior).length

theorem originalSteps_append (source : C) (prior script : Script) (paid : Row → ℕ → ℚ) :
    originalSteps source (prior ++ script) paid =
      originalSteps source prior paid ++ stepsAfter source prior script paid := by
  unfold originalSteps stepsAfter
  rw [Execution.timedInventory_append]
  simpa only [Nat.zero_add] using readSteps_append source.native.handlerFace.rootRead paid
    (Execution.timedInventory source prior) (Execution.timedInventory (Execution.endAt source prior) script) 0

theorem originalSteps_at (source : C) (script : Script) (paid : Row → ℕ → ℚ)
    (ordinal : Fin (Execution.inventory source script).length) :
    (originalSteps source script paid)[ordinal.val]? = some
      (readStep source.native.handlerFace.rootRead paid (Execution.timedAt source script ordinal) ordinal.val) := by
  have bounded : ordinal.val < (Execution.timedInventory source script).length := by
    rw [← List.length_map Prod.fst, Execution.timedInventory_is_the_original_inventory]
    exact ordinal.isLt
  unfold originalSteps
  rw [readSteps_at source.native.handlerFace.rootRead paid (Execution.timedInventory source script) 0 ordinal.val,
    Nat.zero_add, List.getElem?_eq_getElem bounded]
  rfl

theorem originalSteps_reads_stock (source : C) (script : Script)
    (paid : Row → ℕ → ℚ) (key : Party × Good) :
    ReadsStock key (originalSteps source script paid)
      (source.raw.stock key.1 key.2) ((Execution.endAt source script).raw.stock key.1 key.2) := by
  apply readSteps_reads_stock
  rw [Execution.timedInventory_is_the_original_inventory]
  exact original_inventory_follows_stock source script

theorem stepsAfter_reads_stock (source : C) (prior script : Script)
    (paid : Row → ℕ → ℚ) (key : Party × Good) :
    ReadsStock key (stepsAfter source prior script paid)
      ((Execution.endAt source prior).raw.stock key.1 key.2)
      ((Execution.endAt source (prior ++ script)).raw.stock key.1 key.2) := by
  rw [Execution.endAt_append]
  apply readSteps_reads_stock
  rw [Execution.timedInventory_is_the_original_inventory]
  have law : (Execution.endAt source prior).native.handlerFace.rootRead =
      source.native.handlerFace.rootRead := by
    change Physical.Public.interpreter (Execution.endAt source prior).native.input =
      Physical.Public.interpreter source.native.input
    rw [Execution.endAt_input]
  rw [← law]
  exact original_inventory_follows_stock (Execution.endAt source prior) script

end
end Native

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
