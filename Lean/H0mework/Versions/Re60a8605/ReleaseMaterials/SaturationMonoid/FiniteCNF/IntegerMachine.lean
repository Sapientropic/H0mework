import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JoinMachine
import Mathlib.Data.Int.Bitwise
import Mathlib.Tactic.Ring

/-! Signed binary words store their sign-extension bit first and their payload
least-significant bit first. The raw stream starts with a subtraction flag,
then the existing reversed-left/forward-right pair encoding. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.IntegerMachine

open Turing StateTransition
open WordMachine (pairCode)

def bitValue (bit : Bool) : ℤ := if bit then 1 else 0

def payloadValue (sign : Bool) : List Bool → ℤ
  | [] => -bitValue sign
  | bit :: rest => bitValue bit + 2 * payloadValue sign rest

def wordValue : List Bool → Option ℤ
  | [] => none
  | sign :: payload => some (payloadValue sign payload)

def sumBit (a b carry : Bool) : Bool := a ^^ (b ^^ carry)
def nextCarry (a b carry : Bool) : Bool := (a && b) || ((a ^^ b) && carry)
def finalSign (a b carry : Bool) : Bool := sumBit a b (nextCarry a b carry)

theorem bit_sum (a b carry : Bool) :
    bitValue a + bitValue b + bitValue carry =
      bitValue (sumBit a b carry) + 2 * bitValue (nextCarry a b carry) := by
  cases a <;> cases b <;> cases carry <;> rfl

theorem final_value (a b carry : Bool) :
    payloadValue (finalSign a b carry) [sumBit a b carry] =
      -bitValue a - bitValue b + bitValue carry := by
  cases a <;> cases b <;> cases carry <;> rfl

theorem sign_extension (sign : Bool) :
    payloadValue sign [] = bitValue sign + 2 * payloadValue sign [] := by
  simp only [payloadValue]
  ring

theorem payload_complement (sign : Bool) (payload : List Bool) :
    payloadValue (!sign) (payload.map Bool.not) = -payloadValue sign payload - 1 := by
  induction payload with
  | nil => cases sign <;> rfl
  | cons bit payload ih =>
      cases bit <;> simp [payloadValue, ih, bitValue] <;> ring

def addPayload (leftSign rightSign carry : Bool) : List Bool → List Bool → Bool × List Bool
  | [], [] => (finalSign leftSign rightSign carry, [sumBit leftSign rightSign carry])
  | a :: left, [] =>
      let tail := addPayload leftSign rightSign (nextCarry a rightSign carry) left []
      (tail.1, sumBit a rightSign carry :: tail.2)
  | [], b :: right =>
      let tail := addPayload leftSign rightSign (nextCarry leftSign b carry) [] right
      (tail.1, sumBit leftSign b carry :: tail.2)
  | a :: left, b :: right =>
      let tail := addPayload leftSign rightSign (nextCarry a b carry) left right
      (tail.1, sumBit a b carry :: tail.2)
termination_by left right => left.length + right.length

theorem addPayload_value (leftSign rightSign carry : Bool) (left right : List Bool) :
    payloadValue (addPayload leftSign rightSign carry left right).1
        (addPayload leftSign rightSign carry left right).2 =
      payloadValue leftSign left + payloadValue rightSign right + bitValue carry := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          rw [addPayload]
          simpa only [payloadValue, sub_eq_add_neg, add_assoc] using final_value leftSign rightSign carry
      | cons b right =>
          rw [addPayload]
          dsimp only
          simp only [payloadValue]
          rw [addPayload_value leftSign rightSign (nextCarry leftSign b carry) [] right]
          have bits := bit_sum leftSign b carry
          have extension := sign_extension leftSign
          simp only [payloadValue] at *
          omega
  | cons a left =>
      cases right with
      | nil =>
          rw [addPayload]
          dsimp only
          simp only [payloadValue]
          rw [addPayload_value leftSign rightSign (nextCarry a rightSign carry) left []]
          have bits := bit_sum a rightSign carry
          have extension := sign_extension rightSign
          simp only [payloadValue] at *
          omega
      | cons b right =>
          rw [addPayload]
          dsimp only
          simp only [payloadValue]
          rw [addPayload_value leftSign rightSign (nextCarry a b carry) left right]
          have bits := bit_sum a b carry
          omega
termination_by left.length + right.length

def sumResult (subtract leftSign rightSign carry : Bool) :
    List Bool → List (Option Bool) → Option (Bool × List Bool)
  | [], [] => some (finalSign leftSign rightSign carry, [sumBit leftSign rightSign carry])
  | _, none :: _ => none
  | a :: left, [] =>
      (sumResult subtract leftSign rightSign (nextCarry a rightSign carry) left []).map
        fun tail => (tail.1, sumBit a rightSign carry :: tail.2)
  | [], some b :: input =>
      (sumResult subtract leftSign rightSign (nextCarry leftSign (b ^^ subtract) carry) [] input).map
        fun tail => (tail.1, sumBit leftSign (b ^^ subtract) carry :: tail.2)
  | a :: left, some b :: input =>
      (sumResult subtract leftSign rightSign (nextCarry a (b ^^ subtract) carry) left input).map
        fun tail => (tail.1, sumBit a (b ^^ subtract) carry :: tail.2)
termination_by left input => left.length + input.length

theorem sumResult_map (subtract leftSign rightSign carry : Bool) (left right : List Bool) :
    sumResult subtract leftSign rightSign carry left (right.map some) =
      some (addPayload leftSign rightSign carry left (right.map (fun bit => bit ^^ subtract))) := by
  cases left with
  | nil =>
      cases right with
      | nil => simp only [List.map_nil, sumResult, addPayload]
      | cons b right =>
          simp only [List.map_cons, sumResult, addPayload]
          rw [sumResult_map subtract leftSign rightSign (nextCarry leftSign (b ^^ subtract) carry) [] right]
          rfl
  | cons a left =>
      cases right with
      | nil =>
          simp only [List.map_nil, sumResult, addPayload]
          have ih := sumResult_map subtract leftSign rightSign (nextCarry a rightSign carry) left []
          simp only [List.map_nil] at ih
          rw [ih]
          rfl
      | cons b right =>
          simp only [List.map_cons, sumResult, addPayload]
          rw [sumResult_map subtract leftSign rightSign (nextCarry a (b ^^ subtract) carry) left right]
          rfl
termination_by left.length + right.length

def operandResult (subtract : Bool) (input : List (Option Bool)) (work : List Bool) : Option (Bool × List Bool) :=
  match work with
  | [] => none
  | leftSign :: work =>
      match input with
      | some rightSign :: input => sumResult subtract leftSign (rightSign ^^ subtract) subtract work input
      | _ => none

def scanResult (subtract : Bool) : List (Option Bool) → List Bool → Option (Bool × List Bool)
  | [], _ => none
  | none :: input, work => operandResult subtract input work
  | some bit :: input, work => scanResult subtract input (bit :: work)

def rawArithmetic : List (Option Bool) → List Bool
  | some subtract :: input =>
      ((scanResult subtract input []).map fun pair => pair.1 :: pair.2).getD []
  | _ => []

def inputCode (subtract : Bool) (left right : List Bool) : List (Option Bool) :=
  some subtract :: pairCode left right

theorem inputCode_length (subtract : Bool) (left right : List Bool) :
    (inputCode subtract left right).length = left.length + right.length + 2 := by
  simp only [inputCode, List.length_cons, WordMachine.pairCode_length]

theorem scanResult_prefix (subtract : Bool) (initialWord : List Bool)
    (input : List (Option Bool)) (work : List Bool) :
    scanResult subtract (initialWord.map some ++ input) work =
      scanResult subtract input (initialWord.reverse ++ work) := by
  induction initialWord generalizing work with
  | nil => rfl
  | cons bit initialWord ih => simp [scanResult, ih, List.reverse_cons, List.append_assoc]

theorem rawArithmetic_code (subtract leftSign rightSign : Bool) (left right : List Bool) :
    rawArithmetic (inputCode subtract (leftSign :: left) (rightSign :: right)) =
      let result := addPayload leftSign (rightSign ^^ subtract) subtract left
        (right.map fun bit => bit ^^ subtract)
      result.1 :: result.2 := by
  simp only [rawArithmetic, inputCode, pairCode, List.append_assoc, scanResult_prefix,
    List.reverse_reverse, List.append_nil, List.singleton_append, scanResult, List.map_cons,
    operandResult, sumResult_map, Option.map_some, Option.getD_some]

theorem rawArithmetic_value (subtract leftSign rightSign : Bool) (left right : List Bool) :
    wordValue (rawArithmetic (inputCode subtract (leftSign :: left) (rightSign :: right))) =
      some (if subtract then payloadValue leftSign left - payloadValue rightSign right
        else payloadValue leftSign left + payloadValue rightSign right) := by
  rw [rawArithmetic_code]
  simp only [wordValue, addPayload_value]
  cases subtract with
  | false => simp [bitValue]
  | true =>
      simp only [Bool.xor_true, payload_complement, bitValue, if_true]
      congr 1
      ring

theorem rawArithmetic_decoded (subtract : Bool) (left right : List Bool) (a b : ℤ)
    (leftValue : wordValue left = some a) (rightValue : wordValue right = some b) :
    wordValue (rawArithmetic (inputCode subtract left right)) =
      some (if subtract then a - b else a + b) := by
  cases left with
  | nil => simp [wordValue] at leftValue
  | cons leftSign left =>
      cases right with
      | nil => simp [wordValue] at rightValue
      | cons rightSign right =>
          simp only [wordValue, Option.some.injEq] at leftValue rightValue
          simpa only [leftValue, rightValue] using rawArithmetic_value subtract leftSign rightSign left right

theorem sumResult_source (subtract leftSign rightSign carry : Bool)
    (work : List Bool) (input : List (Option Bool)) (result : Bool × List Bool)
    (produced : sumResult subtract leftSign rightSign carry work input = some result) :
    ∃ right : List Bool, input = right.map some := by
  induction input generalizing work carry result with
  | nil => exact ⟨[], rfl⟩
  | cons entry input ih =>
      cases entry with
      | none => simp only [sumResult] at produced; cases produced
      | some b =>
          cases work with
          | nil =>
              cases tail : sumResult subtract leftSign rightSign (nextCarry leftSign (b ^^ subtract) carry) [] input with
              | none => simp only [sumResult, tail, Option.map_none] at produced; cases produced
              | some pair =>
                  obtain ⟨right, same⟩ := ih _ [] pair tail
                  exact ⟨b :: right, by simp [same]⟩
          | cons a work =>
              cases tail : sumResult subtract leftSign rightSign (nextCarry a (b ^^ subtract) carry) work input with
              | none => simp only [sumResult, tail, Option.map_none] at produced; cases produced
              | some pair =>
                  obtain ⟨right, same⟩ := ih _ work pair tail
                  exact ⟨b :: right, by simp [same]⟩

theorem operandResult_source (subtract : Bool) (input : List (Option Bool))
    (work : List Bool) (result : Bool × List Bool)
    (produced : operandResult subtract input work = some result) :
    ∃ right : List Bool, input = right.map some ∧ work ≠ [] ∧ right ≠ [] := by
  cases work with
  | nil => simp [operandResult] at produced
  | cons leftSign work =>
      cases input with
      | nil => simp [operandResult] at produced
      | cons entry input =>
          cases entry with
          | none => simp [operandResult] at produced
          | some rightSign =>
              obtain ⟨right, same⟩ := sumResult_source subtract leftSign (rightSign ^^ subtract) subtract work input result produced
              exact ⟨rightSign :: right, by simp [same], by simp, by simp⟩

theorem scanResult_source (subtract : Bool) (input : List (Option Bool))
    (work : List Bool) (result : Bool × List Bool)
    (produced : scanResult subtract input work = some result) :
    ∃ initialWord right : List Bool,
      input = initialWord.map some ++ [none] ++ right.map some ∧
        initialWord.reverse ++ work ≠ [] ∧ right ≠ [] := by
  induction input generalizing work with
  | nil => simp [scanResult] at produced
  | cons entry input ih =>
      cases entry with
      | none =>
          obtain ⟨right, same, leftNonempty, rightNonempty⟩ := operandResult_source subtract input work result produced
          exact ⟨[], right, by simp [same], by simpa using leftNonempty, rightNonempty⟩
      | some bit =>
          obtain ⟨initialWord, right, same, leftNonempty, rightNonempty⟩ := ih (bit :: work) produced
          exact ⟨bit :: initialWord, right, by simpa using congrArg (List.cons (some bit)) same,
            by simp [List.reverse_cons, List.append_assoc], rightNonempty⟩

theorem rawArithmetic_invalid (input : List (Option Bool))
    (invalid : ¬ ∃ (subtract : Bool) (left right : List Bool),
      input = inputCode subtract left right ∧ left ≠ [] ∧ right ≠ []) :
    rawArithmetic input = [] := by
  cases input with
  | nil => rfl
  | cons entry input =>
      cases entry with
      | none => rfl
      | some subtract =>
          cases produced : scanResult subtract input [] with
          | none => simp [rawArithmetic, produced]
          | some result =>
              obtain ⟨initialWord, right, same, leftNonempty, rightNonempty⟩ :=
                scanResult_source subtract input [] result produced
              apply False.elim
              apply invalid
              exact ⟨subtract, initialWord.reverse, right,
                by simp [inputCode, pairCode, same], by simpa using leftNonempty, rightNonempty⟩

def accumulated (buffer : List Bool) : Option (Bool × List Bool) → List Bool
  | none => []
  | some pair => pair.1 :: (buffer.reverse ++ pair.2)

theorem accumulated_cons (bit : Bool) (buffer : List Bool) (result : Option (Bool × List Bool)) :
    accumulated buffer (result.map (fun pair => (pair.1, bit :: pair.2))) =
      accumulated (bit :: buffer) result := by
  cases result <;> simp [accumulated, List.reverse_cons, List.append_assoc]

open JoinMachine (Stack Alphabet tapes)

structure State where
  subtract : Bool
  leftSign : Bool
  rightSign : Bool
  carry : Bool
  leftHead : Option Bool
  inputHead : Option (Option Bool)
  deriving DecidableEq

private def stateEquiv : State ≃ (Bool × Bool × Bool × Bool × Option Bool × Option (Option Bool)) where
  toFun state := (state.subtract, state.leftSign, state.rightSign, state.carry, state.leftHead, state.inputHead)
  invFun value := ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1, value.2.2.2.2.2⟩
  left_inv state := by cases state; rfl
  right_inv value := by rcases value with ⟨a, b, c, d, e, f⟩; rfl

instance : Fintype State := Fintype.ofEquiv _ stateEquiv.symm

def baseState (subtract leftSign rightSign carry : Bool) : State :=
  ⟨subtract, leftSign, rightSign, carry, none, none⟩

def initialState : State := baseState false false false false
def inputRecord (state : State) (head : Option (Option Bool)) : State := { state with inputHead := head }
def workRecord (state : State) (head : Option Bool) : State := { state with leftHead := head }
def inputEnd (state : State) : Bool := state.inputHead.isNone
def workEnd (state : State) : Bool := state.leftHead.isNone
def separator (state : State) : Bool := state.inputHead == some none
def rawBit (state : State) : Bool := (state.inputHead.bind id).getD false
def workBit (state : State) : Bool := state.leftHead.getD false
def leftDigit (state : State) : Bool := state.leftHead.getD state.leftSign
def rightDigit (state : State) : Bool :=
  ((state.inputHead.bind id).map (fun bit => bit ^^ state.subtract)).getD state.rightSign
def outputBit (state : State) : Bool := sumBit (leftDigit state) (rightDigit state) state.carry
def afterCarry (state : State) : State :=
  baseState state.subtract state.leftSign state.rightSign
    (nextCarry (leftDigit state) (rightDigit state) state.carry)
def finishState (state : State) : State :=
  baseState state.subtract (finalSign state.leftSign state.rightSign state.carry) false false
def rightState (state : State) : State :=
  baseState state.subtract state.leftSign (rawBit state ^^ state.subtract) state.subtract

inductive Phase
  | readOp | scan | leftSign | rightSign | add | reverse | clearInput | clearWork | clearBuffer
  deriving DecidableEq

instance : Fintype Phase where
  elems := {Phase.readOp, Phase.scan, Phase.leftSign, Phase.rightSign, Phase.add, Phase.reverse,
    Phase.clearInput, Phase.clearWork, Phase.clearBuffer}
  complete := by intro phase; cases phase <;> simp

abbrev Statement := TM2.Stmt Alphabet Phase State
open TM2.Stmt

def jump (phase : Phase) : Statement := goto fun _ => phase
def finish : Statement := load (fun _ => initialState) halt

def program : Phase → Statement
  | .readOp => pop .input inputRecord
      (branch inputEnd (jump .clearInput) (branch separator (jump .clearInput)
        (load (fun state => baseState (rawBit state) false false (rawBit state)) (jump .scan))))
  | .scan => pop .input inputRecord
      (branch inputEnd (jump .clearInput) (branch separator (jump .leftSign)
        (push .work rawBit (jump .scan))))
  | .leftSign => pop .work workRecord
      (branch workEnd (jump .clearInput)
        (load (fun state => { state with leftSign := workBit state }) (jump .rightSign)))
  | .rightSign => pop .input inputRecord
      (branch inputEnd (jump .clearInput) (branch separator (jump .clearInput)
        (load rightState (jump .add))))
  | .add => pop .work workRecord (pop .input inputRecord
      (branch separator (jump .clearInput)
        (branch (fun state => workEnd state && inputEnd state)
          (push .buffer (fun state => sumBit state.leftSign state.rightSign state.carry)
            (load finishState (jump .reverse)))
          (push .buffer outputBit (load afterCarry (jump .add))))))
  | .reverse => pop .buffer workRecord
      (branch workEnd (push .work (fun state => state.leftSign) finish)
        (push .work workBit (jump .reverse)))
  | .clearInput => pop .input inputRecord
      (branch inputEnd (jump .clearWork) (jump .clearInput))
  | .clearWork => pop .work workRecord
      (branch workEnd (jump .clearBuffer) (jump .clearWork))
  | .clearBuffer => pop .buffer workRecord
      (branch workEnd finish (jump .clearBuffer))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .work
  Γ := Alphabet
  Λ := Phase
  main := .readOp
  σ := State
  initialState := initialState
  m := program

def configuration (phase : Option Phase) (state : State)
    (input : List (Option Bool)) (work buffer : List Bool) : machine.Cfg :=
  ⟨phase, state, tapes input work buffer⟩

def terminal (output : List Bool) : machine.Cfg := configuration none initialState [] output []

theorem initial_configuration (input : List (Option Bool)) :
    initList machine input = configuration (some .readOp) initialState input [] [] := by
  unfold initList configuration
  congr 1
  funext stack
  cases stack <;> rfl

theorem terminal_configuration (output : List Bool) : terminal output = haltList machine output := by
  unfold terminal configuration haltList
  congr 1
  funext stack
  cases stack <;> rfl

@[simp] theorem step_clearBuffer_nil (state : State) :
    machine.step (configuration (some .clearBuffer) state [] [] []) = some (terminal []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd,
    finish, terminal]
  rfl

@[simp] theorem step_clearBuffer_cons (state : State) (bit : Bool) (buffer : List Bool) :
    machine.step (configuration (some .clearBuffer) state [] [] (bit :: buffer)) =
      some (configuration (some .clearBuffer) (workRecord state (some bit)) [] [] buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, jump]
  rfl

@[simp] theorem step_clearWork_nil (state : State) (buffer : List Bool) :
    machine.step (configuration (some .clearWork) state [] [] buffer) =
      some (configuration (some .clearBuffer) (workRecord state none) [] [] buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, jump]
  rfl

@[simp] theorem step_clearWork_cons (state : State) (bit : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .clearWork) state [] (bit :: work) buffer) =
      some (configuration (some .clearWork) (workRecord state (some bit)) [] work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, jump]
  rfl

@[simp] theorem step_clearInput_nil (state : State) (work buffer : List Bool) :
    machine.step (configuration (some .clearInput) state [] work buffer) =
      some (configuration (some .clearWork) (inputRecord state none) [] work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, jump]
  rfl

@[simp] theorem step_clearInput_cons (state : State) (entry : Option Bool)
    (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .clearInput) state (entry :: input) work buffer) =
      some (configuration (some .clearInput) (inputRecord state (some entry)) input work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, jump]
  rfl

@[simp] theorem step_reverse_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .reverse) state [] work []) =
      some (terminal (state.leftSign :: work)) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd,
    finish, terminal]
  rfl

@[simp] theorem step_reverse_cons (state : State) (bit : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .reverse) state [] work (bit :: buffer)) =
      some (configuration (some .reverse) (workRecord state (some bit)) [] (bit :: work) buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, workBit, jump]
  rfl

@[simp] theorem step_add_nil (state : State) (buffer : List Bool) :
    machine.step (configuration (some .add) state [] [] buffer) =
      some (configuration (some .reverse) (finishState state) [] []
        (sumBit state.leftSign state.rightSign state.carry :: buffer)) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, inputRecord,
    workEnd, inputEnd, separator, finishState, jump]
  rfl

@[simp] theorem step_add_separator (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .add) state (none :: input) work buffer) =
      some (configuration (some .clearInput)
        (inputRecord (workRecord state work.head?) (some none)) input work.tail buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, separator, jump]
  rfl

@[simp] theorem step_add_left (state : State) (a : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .add) state [] (a :: work) buffer) =
      some (configuration (some .add)
        (baseState state.subtract state.leftSign state.rightSign (nextCarry a state.rightSign state.carry))
        [] work (sumBit a state.rightSign state.carry :: buffer)) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, inputRecord,
    workEnd, inputEnd, separator, afterCarry, outputBit, leftDigit, rightDigit, jump]
  rfl

@[simp] theorem step_add_right (state : State) (b : Bool) (input : List (Option Bool)) (buffer : List Bool) :
    machine.step (configuration (some .add) state (some b :: input) [] buffer) =
      some (configuration (some .add)
        (baseState state.subtract state.leftSign state.rightSign
          (nextCarry state.leftSign (b ^^ state.subtract) state.carry))
        input [] (sumBit state.leftSign (b ^^ state.subtract) state.carry :: buffer)) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, inputRecord,
    workEnd, inputEnd, separator, afterCarry, outputBit, leftDigit, rightDigit, jump]
  rfl

@[simp] theorem step_add_pair (state : State) (a b : Bool) (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .add) state (some b :: input) (a :: work) buffer) =
      some (configuration (some .add)
        (baseState state.subtract state.leftSign state.rightSign
          (nextCarry a (b ^^ state.subtract) state.carry))
        input work (sumBit a (b ^^ state.subtract) state.carry :: buffer)) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, inputRecord,
    workEnd, inputEnd, separator, afterCarry, outputBit, leftDigit, rightDigit, jump]
  rfl

@[simp] theorem step_rightSign_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .rightSign) state [] work []) =
      some (configuration (some .clearInput) (inputRecord state none) [] work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, jump]
  rfl

@[simp] theorem step_rightSign_separator (state : State) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .rightSign) state (none :: input) work []) =
      some (configuration (some .clearInput) (inputRecord state (some none)) input work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator, jump]
  rfl

@[simp] theorem step_rightSign_bit (state : State) (bit : Bool) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .rightSign) state (some bit :: input) work []) =
      some (configuration (some .add) (baseState state.subtract state.leftSign (bit ^^ state.subtract) state.subtract)
        input work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator,
    rightState, rawBit, jump]
  rfl

@[simp] theorem step_leftSign_nil (state : State) (input : List (Option Bool)) :
    machine.step (configuration (some .leftSign) state input [] []) =
      some (configuration (some .clearInput) (workRecord state none) input [] []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, jump]
  rfl

@[simp] theorem step_leftSign_bit (state : State) (bit : Bool) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .leftSign) state input (bit :: work) []) =
      some (configuration (some .rightSign) {workRecord state (some bit) with leftSign := bit} input work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, workRecord, workEnd, workBit, jump]
  rfl

@[simp] theorem step_scan_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .scan) state [] work []) =
      some (configuration (some .clearInput) (inputRecord state none) [] work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, jump]
  rfl

@[simp] theorem step_scan_separator (state : State) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (none :: input) work []) =
      some (configuration (some .leftSign) (inputRecord state (some none)) input work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator, jump]
  rfl

@[simp] theorem step_scan_bit (state : State) (bit : Bool) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (some bit :: input) work []) =
      some (configuration (some .scan) (inputRecord state (some (some bit))) input (bit :: work) []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator, rawBit, jump]
  rfl

@[simp] theorem step_readOp_nil (state : State) :
    machine.step (configuration (some .readOp) state [] [] []) =
      some (configuration (some .clearInput) (inputRecord state none) [] [] []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, jump]
  rfl

@[simp] theorem step_readOp_separator (state : State) (input : List (Option Bool)) :
    machine.step (configuration (some .readOp) state (none :: input) [] []) =
      some (configuration (some .clearInput) (inputRecord state (some none)) input [] []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator, jump]
  rfl

@[simp] theorem step_readOp_bit (state : State) (bit : Bool) (input : List (Option Bool)) :
    machine.step (configuration (some .readOp) state (some bit :: input) [] []) =
      some (configuration (some .scan) (baseState bit false false bit) input [] []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, inputRecord, inputEnd, separator, rawBit, jump]
  rfl

private def oneStep {before after : machine.Cfg} (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := step
  steps_le_m := Nat.le_refl 1

private def afterStep {before middle after : machine.Cfg} {budget : Nat}
    (step : machine.step before = some middle)
    (run : EvalsToInTime machine.step middle (some after) budget) :
    EvalsToInTime machine.step before (some after) (budget + 1) :=
  EvalsToInTime.trans machine.step 1 budget before middle (some after) (oneStep step) run

private def increaseBudget {before after : machine.Cfg} {cost budget : Nat}
    (run : EvalsToInTime machine.step before (some after) cost) (bound : cost ≤ budget) :
    EvalsToInTime machine.step before (some after) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

def clearBuffer_run (state : State) (buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .clearBuffer) state [] [] buffer)
      (some (terminal [])) (buffer.length + 1) := by
  induction buffer generalizing state with
  | nil => exact oneStep (step_clearBuffer_nil state)
  | cons bit buffer ih =>
      simpa only [List.length_cons, Nat.add_assoc] using
        afterStep (step_clearBuffer_cons state bit buffer) (ih (workRecord state (some bit)))

def clearWork_run (state : State) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .clearWork) state [] work buffer)
      (some (terminal [])) (work.length + buffer.length + 2) := by
  induction work generalizing state with
  | nil => simpa using afterStep (step_clearWork_nil state buffer) (clearBuffer_run (workRecord state none) buffer)
  | cons bit work ih =>
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        afterStep (step_clearWork_cons state bit work buffer) (ih (workRecord state (some bit)))

def clearInput_run (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .clearInput) state input work buffer)
      (some (terminal [])) (input.length + work.length + buffer.length + 3) := by
  induction input generalizing state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Nat.add_assoc] using
        afterStep (step_clearInput_nil state work buffer) (clearWork_run (inputRecord state none) work buffer)
  | cons entry input ih =>
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        afterStep (step_clearInput_cons state entry input work buffer) (ih (inputRecord state (some entry)))

def reverse_run (state : State) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .reverse) state [] work buffer)
      (some (terminal (state.leftSign :: (buffer.reverse ++ work)))) (buffer.length + 1) := by
  induction buffer generalizing state work with
  | nil => exact oneStep (step_reverse_nil state work)
  | cons bit buffer ih =>
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, workRecord] using
        afterStep (step_reverse_cons state bit work buffer) (ih (workRecord state (some bit)) (bit :: work))

def sum_run (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .add) state input work buffer)
      (some (terminal (accumulated buffer
        (sumResult state.subtract state.leftSign state.rightSign state.carry work input))))
      (2 * (input.length + work.length) + buffer.length + 5) :=
  match work, input with
  | [], [] => by
      have run := afterStep (step_add_nil state buffer)
        (reverse_run (finishState state) [] (sumBit state.leftSign state.rightSign state.carry :: buffer))
      exact increaseBudget
        (by simpa only [sumResult, accumulated, finishState, baseState,
          List.reverse_cons, List.append_nil] using run)
        (by simp)
  | work, none :: input => by
      have run := afterStep (step_add_separator state input work buffer)
        (clearInput_run (inputRecord (workRecord state work.head?) (some none)) input work.tail buffer)
      exact increaseBudget (by simpa only [sumResult, accumulated] using run)
        (by simp only [List.length_cons, List.length_tail]; omega)
  | a :: work, [] => by
      have run := afterStep (step_add_left state a work buffer)
        (sum_run (baseState state.subtract state.leftSign state.rightSign (nextCarry a state.rightSign state.carry))
          [] work (sumBit a state.rightSign state.carry :: buffer))
      exact increaseBudget (by simpa only [sumResult, accumulated_cons, baseState] using run)
        (by simp only [List.length_cons, List.length_nil]; omega)
  | [], some b :: input => by
      have run := afterStep (step_add_right state b input buffer)
        (sum_run (baseState state.subtract state.leftSign state.rightSign
          (nextCarry state.leftSign (b ^^ state.subtract) state.carry))
          input [] (sumBit state.leftSign (b ^^ state.subtract) state.carry :: buffer))
      exact increaseBudget (by simpa only [sumResult, accumulated_cons, baseState] using run)
        (by simp only [List.length_cons, List.length_nil]; omega)
  | a :: work, some b :: input => by
      have run := afterStep (step_add_pair state a b input work buffer)
        (sum_run (baseState state.subtract state.leftSign state.rightSign
          (nextCarry a (b ^^ state.subtract) state.carry))
          input work (sumBit a (b ^^ state.subtract) state.carry :: buffer))
      exact increaseBudget (by simpa only [sumResult, accumulated_cons, baseState] using run)
        (by simp only [List.length_cons]; omega)
termination_by work.length + input.length

def rightSign_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .rightSign) state input work [])
      (some (terminal (accumulated [] (operandResult state.subtract input (state.leftSign :: work)))))
      (2 * (input.length + work.length) + 8) := by
  cases input with
  | nil =>
      have run := afterStep (step_rightSign_nil state work) (clearInput_run (inputRecord state none) [] work [])
      exact increaseBudget (by simpa only [operandResult, accumulated] using run)
        (by simp; omega)
  | cons entry input =>
      cases entry with
      | none =>
          have run := afterStep (step_rightSign_separator state input work)
            (clearInput_run (inputRecord state (some none)) input work [])
          exact increaseBudget (by simpa only [operandResult, accumulated] using run)
            (by simp only [List.length_cons, List.length_nil]; omega)
      | some bit =>
          have run := afterStep (step_rightSign_bit state bit input work)
            (sum_run (baseState state.subtract state.leftSign (bit ^^ state.subtract) state.subtract) input work [])
          exact increaseBudget (by simpa only [operandResult, baseState] using run)
            (by simp only [List.length_cons, List.length_nil]; omega)

def leftSign_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .leftSign) state input work [])
      (some (terminal (accumulated [] (operandResult state.subtract input work))))
      (2 * (input.length + work.length) + 9) := by
  cases work with
  | nil =>
      have run := afterStep (step_leftSign_nil state input) (clearInput_run (workRecord state none) input [] [])
      exact increaseBudget (by simpa only [operandResult, accumulated] using run)
        (by simp; omega)
  | cons bit work =>
      have run := afterStep (step_leftSign_bit state bit input work)
        (rightSign_run {workRecord state (some bit) with leftSign := bit} input work)
      exact increaseBudget (by simpa only [workRecord] using run)
        (by simp only [List.length_cons]; omega)

def scan_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .scan) state input work [])
      (some (terminal (accumulated [] (scanResult state.subtract input work))))
      (3 * input.length + 2 * work.length + 11) := by
  induction input generalizing state work with
  | nil =>
      have run := afterStep (step_scan_nil state work) (clearInput_run (inputRecord state none) [] work [])
      exact increaseBudget (by simpa only [scanResult, accumulated] using run)
        (by simp; omega)
  | cons entry input ih =>
      cases entry with
      | none =>
          have run := afterStep (step_scan_separator state input work) (leftSign_run (inputRecord state (some none)) input work)
          exact increaseBudget (by simpa only [scanResult, inputRecord] using run)
            (by simp only [List.length_cons]; omega)
      | some bit =>
          have run := afterStep (step_scan_bit state bit input work) (ih (inputRecord state (some (some bit))) (bit :: work))
          exact increaseBudget (by simpa only [scanResult, inputRecord] using run)
            (by simp only [List.length_cons]; omega)

def rawArithmetic_outputs (input : List (Option Bool)) :
    TM2OutputsInTime machine input (some (rawArithmetic input)) (3 * input.length + 12) := by
  change EvalsToInTime machine.step (initList machine input) (some (haltList machine (rawArithmetic input))) _
  rw [initial_configuration, ← terminal_configuration]
  cases input with
  | nil =>
      have run := afterStep (step_readOp_nil initialState) (clearInput_run (inputRecord initialState none) [] [] [])
      exact increaseBudget (by simpa only [rawArithmetic] using run)
        (by simp)
  | cons entry input =>
      cases entry with
      | none =>
          have run := afterStep (step_readOp_separator initialState input)
            (clearInput_run (inputRecord initialState (some none)) input [] [])
          exact increaseBudget (by simpa only [rawArithmetic] using run)
            (by simp only [List.length_cons, List.length_nil]; omega)
      | some subtract =>
          have run := afterStep (step_readOp_bit initialState subtract input)
            (scan_run (baseState subtract false false subtract) input [])
          have same : accumulated [] (scanResult subtract input []) =
              rawArithmetic (some subtract :: input) := by
            cases found : scanResult subtract input [] <;> simp [rawArithmetic, accumulated, found]
          exact increaseBudget (by simpa only [baseState, same] using run)
            (by simp only [List.length_cons, List.length_nil]; omega)

noncomputable def rawArithmetic_polyTime :
    TM2ComputableInPolyTime (id : List (Option Bool) → List (Option Bool))
      (id : List Bool → List Bool) rawArithmetic where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 12
  outputsFun input := by simpa using rawArithmetic_outputs input

end SaturationMonoid.ComplexityProjection.SATSource.IntegerMachine
