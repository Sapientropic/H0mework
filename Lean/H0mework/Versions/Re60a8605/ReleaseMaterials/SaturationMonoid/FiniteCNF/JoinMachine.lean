import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.WordMachine

/-!
One fixed three-stack TM2 computes coordinatewise AND of equal-length words.
The input uses WordMachine.pairCode. Malformed input is drained to the empty
output; successful output is reversed from a buffer into the work/output stack.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JoinMachine

open Turing StateTransition
open WordMachine (pairCode State bitState bitOf separator)

def zipResult : List (Option Bool) → List Bool → Option (List Bool)
  | [], [] => some []
  | some bit :: input, head :: work => (zipResult input work).map ((head && bit) :: ·)
  | _, _ => none

def scanResult : List (Option Bool) → List Bool → Option (List Bool)
  | [], _ => none
  | none :: input, work => zipResult input work
  | some bit :: input, work => scanResult input (bit :: work)

def rawJoin (input : List (Option Bool)) : List Bool := (scanResult input []).getD []

def accumulated (buffer : List Bool) : Option (List Bool) → List Bool
  | none => []
  | some result => buffer.reverse ++ result

theorem accumulated_cons (bit : Bool) (buffer : List Bool) (result : Option (List Bool)) :
    accumulated buffer (result.map (bit :: ·)) = accumulated (bit :: buffer) result := by
  cases result <;> simp [accumulated, List.reverse_cons, List.append_assoc]

theorem zipResult_map (left right : List Bool) :
    zipResult (right.map some) left =
      if left.length = right.length then some (List.zipWith Bool.and left right) else none := by
  induction right generalizing left with
  | nil => cases left <;> simp [zipResult]
  | cons bit right ih =>
      cases left with
      | nil => simp [zipResult]
      | cons head left =>
          by_cases same : left.length = right.length <;> simp [zipResult, ih, same]

theorem scanResult_prefix (initialWord : List Bool) (input : List (Option Bool)) (work : List Bool) :
    scanResult (initialWord.map some ++ input) work =
      scanResult input (initialWord.reverse ++ work) := by
  induction initialWord generalizing work with
  | nil => rfl
  | cons bit initialWord ih => simp [scanResult, ih, List.reverse_cons, List.append_assoc]

theorem rawJoin_pair_cases (left right : List Bool) :
    rawJoin (pairCode left right) =
      if left.length = right.length then List.zipWith Bool.and left right else [] := by
  simp only [rawJoin, pairCode, List.append_assoc, scanResult_prefix,
    List.reverse_reverse, List.append_nil]
  change (zipResult (right.map some) left).getD [] = _
  rw [zipResult_map]
  split <;> rfl

theorem rawJoin_pair (left right : List Bool) (same : left.length = right.length) :
    rawJoin (pairCode left right) = List.zipWith Bool.and left right := by
  rw [rawJoin_pair_cases, if_pos same]

theorem zipResult_source (input : List (Option Bool)) (work result : List Bool)
    (produced : zipResult input work = some result) :
    ∃ right : List Bool, input = right.map some ∧ work.length = right.length := by
  induction input generalizing work result with
  | nil =>
      cases work with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons head work => simp [zipResult] at produced
  | cons entry input ih =>
      cases entry with
      | none => cases work <;> simp [zipResult] at produced
      | some bit =>
          cases work with
          | nil => simp [zipResult] at produced
          | cons head work =>
              cases tail : zipResult input work with
              | none => simp [zipResult, tail] at produced
              | some output =>
                  obtain ⟨right, hin, hlen⟩ := ih work output tail
                  exact ⟨bit :: right, by simp [hin], by simp [hlen]⟩

theorem scanResult_source (input : List (Option Bool)) (work result : List Bool)
    (produced : scanResult input work = some result) :
    ∃ initialWord right : List Bool,
      input = initialWord.map some ++ [none] ++ right.map some ∧
        initialWord.length + work.length = right.length := by
  induction input generalizing work with
  | nil => simp [scanResult] at produced
  | cons entry input ih =>
      cases entry with
      | none =>
          obtain ⟨right, hin, hlen⟩ := zipResult_source input work result produced
          exact ⟨[], right, by simp [hin], by simpa using hlen⟩
      | some bit =>
          obtain ⟨initialWord, right, hin, hlen⟩ := ih (bit :: work) produced
          refine ⟨bit :: initialWord, right, ?_, ?_⟩
          · simpa using congrArg (List.cons (some bit)) hin
          · simp only [List.length_cons] at hlen ⊢
            omega

theorem rawJoin_invalid (input : List (Option Bool))
    (invalid : ¬ ∃ left right : List Bool,
      input = pairCode left right ∧ left.length = right.length) : rawJoin input = [] := by
  cases produced : scanResult input [] with
  | none => simp [rawJoin, produced]
  | some result =>
      obtain ⟨initialWord, right, hin, hlen⟩ := scanResult_source input [] result produced
      apply False.elim
      apply invalid
      exact ⟨initialWord.reverse, right, by simpa [pairCode] using hin, by simpa using hlen⟩

inductive Stack
  | input | work | buffer
  deriving DecidableEq

instance : Fintype Stack where
  elems := {Stack.input, Stack.work, Stack.buffer}
  complete := by intro stack; cases stack <;> simp

inductive Phase
  | scan | zip | reverse | clearInput | clearWork | clearBuffer
  deriving DecidableEq

instance : Fintype Phase where
  elems := {Phase.scan, Phase.zip, Phase.reverse, Phase.clearInput, Phase.clearWork, Phase.clearBuffer}
  complete := by intro phase; cases phase <;> simp

abbrev Alphabet : Stack → Type
  | .input => Option Bool
  | .work => Bool
  | .buffer => Bool

instance alphabetFinite (stack : Stack) : Fintype (Alphabet stack) := by
  cases stack <;> infer_instance

abbrev Statement := TM2.Stmt Alphabet Phase State
open TM2.Stmt

def jump (phase : Phase) : Statement := goto fun _ => phase
def finish : Statement := load (fun _ => none) halt

def program : Phase → Statement
  | .scan =>
      pop .input (fun _ head => head)
        (branch Option.isNone (jump .clearInput)
          (branch separator (jump .zip)
            (push .work bitOf (jump .scan))))
  | .zip =>
      pop .input (fun _ head => head)
        (branch Option.isNone
          (pop .work (fun _ head => some head)
            (branch separator (jump .reverse) (jump .clearInput)))
          (branch separator (jump .clearInput)
            (pop .work (fun state head => some (head.map fun left => left && bitOf state))
              (branch separator (jump .clearInput)
                (push .buffer bitOf (jump .zip))))))
  | .reverse =>
      pop .buffer (fun _ head => some head)
        (branch separator finish (push .work bitOf (jump .reverse)))
  | .clearInput =>
      pop .input (fun _ head => head)
        (branch Option.isNone (jump .clearWork) (jump .clearInput))
  | .clearWork =>
      pop .work (fun _ head => some head)
        (branch separator (jump .clearBuffer) (jump .clearWork))
  | .clearBuffer =>
      pop .buffer (fun _ head => some head)
        (branch separator finish (jump .clearBuffer))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .work
  Γ := Alphabet
  Λ := Phase
  main := .scan
  σ := State
  initialState := none
  m := program

def tapes (input : List (Option Bool)) (work buffer : List Bool) :
    (stack : Stack) → List (Alphabet stack)
  | .input => input
  | .work => work
  | .buffer => buffer

@[simp] theorem tapes_input (input : List (Option Bool)) (work buffer : List Bool) :
    tapes input work buffer .input = input := rfl
@[simp] theorem tapes_work (input : List (Option Bool)) (work buffer : List Bool) :
    tapes input work buffer .work = work := rfl
@[simp] theorem tapes_buffer (input : List (Option Bool)) (work buffer : List Bool) :
    tapes input work buffer .buffer = buffer := rfl

@[simp] theorem update_input (input next : List (Option Bool)) (work buffer : List Bool) :
    Function.update (tapes input work buffer) .input next = tapes next work buffer := by
  funext stack
  cases stack <;> simp [Function.update, tapes]

@[simp] theorem update_work (input : List (Option Bool)) (work next buffer : List Bool) :
    Function.update (tapes input work buffer) .work next = tapes input next buffer := by
  funext stack
  cases stack <;> simp [Function.update, tapes]

@[simp] theorem update_buffer (input : List (Option Bool)) (work buffer next : List Bool) :
    Function.update (tapes input work buffer) .buffer next = tapes input work next := by
  funext stack
  cases stack <;> simp [Function.update, tapes]

def configuration (phase : Option Phase) (state : State)
    (input : List (Option Bool)) (work buffer : List Bool) : machine.Cfg :=
  ⟨phase, state, tapes input work buffer⟩

def terminal (output : List Bool) : machine.Cfg := configuration none none [] output []

theorem initial_configuration (input : List (Option Bool)) :
    initList machine input = configuration (some .scan) none input [] [] := by
  unfold initList configuration
  congr 1
  funext stack
  cases stack <;> rfl

theorem terminal_configuration (output : List Bool) :
    terminal output = haltList machine output := by
  unfold terminal configuration haltList
  congr 1
  funext stack
  cases stack <;> rfl

@[simp] theorem step_scan_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .scan) state [] work []) =
      some (configuration (some .clearInput) none [] work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_scan_separator (state : State) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (none :: input) work []) =
      some (configuration (some .zip) (some none) input work []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_scan_bit (state : State) (bit : Bool)
    (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (some bit :: input) work []) =
      some (configuration (some .scan) (bitState bit) input (bit :: work) []) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
      separator, bitOf, bitState] <;> rfl

@[simp] theorem step_clearInput_nil (state : State) (work buffer : List Bool) :
    machine.step (configuration (some .clearInput) state [] work buffer) =
      some (configuration (some .clearWork) none [] work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_clearInput_cons (state : State) (entry : Option Bool)
    (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .clearInput) state (entry :: input) work buffer) =
      some (configuration (some .clearInput) (some entry) input work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_clearWork_nil (state : State) (buffer : List Bool) :
    machine.step (configuration (some .clearWork) state [] [] buffer) =
      some (configuration (some .clearBuffer) (some none) [] [] buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_clearWork_cons (state : State) (bit : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .clearWork) state [] (bit :: work) buffer) =
      some (configuration (some .clearWork) (bitState bit) [] work buffer) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator, bitState] <;> rfl

@[simp] theorem step_clearBuffer_nil (state : State) :
    machine.step (configuration (some .clearBuffer) state [] [] []) = some (terminal []) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, separator, finish, terminal]
  rfl

@[simp] theorem step_clearBuffer_cons (state : State) (bit : Bool) (buffer : List Bool) :
    machine.step (configuration (some .clearBuffer) state [] [] (bit :: buffer)) =
      some (configuration (some .clearBuffer) (bitState bit) [] [] buffer) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator, bitState] <;> rfl

@[simp] theorem step_reverse_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .reverse) state [] work []) = some (terminal work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, separator, finish, terminal]
  rfl

@[simp] theorem step_reverse_cons (state : State) (bit : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .reverse) state [] work (bit :: buffer)) =
      some (configuration (some .reverse) (bitState bit) [] (bit :: work) buffer) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
      separator, bitOf, bitState] <;> rfl

@[simp] theorem step_zip_empty (state : State) (buffer : List Bool) :
    machine.step (configuration (some .zip) state [] [] buffer) =
      some (configuration (some .reverse) (some none) [] [] buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_zip_extra_work (state : State) (bit : Bool) (work buffer : List Bool) :
    machine.step (configuration (some .zip) state [] (bit :: work) buffer) =
      some (configuration (some .clearInput) (bitState bit) [] work buffer) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator, bitState] <;> rfl

@[simp] theorem step_zip_separator (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .zip) state (none :: input) work buffer) =
      some (configuration (some .clearInput) (some none) input work buffer) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_zip_extra_input (state : State) (bit : Bool)
    (input : List (Option Bool)) (buffer : List Bool) :
    machine.step (configuration (some .zip) state (some bit :: input) [] buffer) =
      some (configuration (some .clearInput) (some none) input [] buffer) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator] <;> rfl

@[simp] theorem step_zip_bits (state : State) (bit head : Bool)
    (input : List (Option Bool)) (work buffer : List Bool) :
    machine.step (configuration (some .zip) state (some bit :: input) (head :: work) buffer) =
      some (configuration (some .zip) (bitState (head && bit)) input work ((head && bit) :: buffer)) := by
  cases bit <;> cases head <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
      separator, bitOf, bitState] <;> rfl

private def oneStep {before after : machine.Cfg}
    (transition : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := transition
  steps_le_m := Nat.le_refl 1

private def afterStep {before middle after : machine.Cfg} {budget : Nat}
    (transition : machine.step before = some middle)
    (continuation : EvalsToInTime machine.step middle (some after) budget) :
    EvalsToInTime machine.step before (some after) (budget + 1) :=
  EvalsToInTime.trans machine.step 1 budget before middle (some after) (oneStep transition) continuation

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
  | cons bit buffer ih => exact afterStep (step_clearBuffer_cons state bit buffer) (ih (bitState bit))

def clearWork_run (state : State) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .clearWork) state [] work buffer)
      (some (terminal [])) (work.length + buffer.length + 2) := by
  induction work generalizing state with
  | nil =>
      exact increaseBudget
        (afterStep (step_clearWork_nil state buffer) (clearBuffer_run (some none) buffer)) (by simp)
  | cons bit work ih =>
      exact increaseBudget
        (afterStep (step_clearWork_cons state bit work buffer) (ih (bitState bit)))
        (by simp only [List.length_cons]; omega)

def clearInput_run (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .clearInput) state input work buffer)
      (some (terminal [])) (input.length + work.length + buffer.length + 3) := by
  induction input generalizing state with
  | nil =>
      exact increaseBudget
        (afterStep (step_clearInput_nil state work buffer) (clearWork_run none work buffer)) (by simp)
  | cons entry input ih =>
      exact increaseBudget
        (afterStep (step_clearInput_cons state entry input work buffer) (ih (some entry)))
        (by simp only [List.length_cons]; omega)

def reverse_run (state : State) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .reverse) state [] work buffer)
      (some (terminal (buffer.reverse ++ work))) (buffer.length + 1) := by
  induction buffer generalizing state work with
  | nil => exact oneStep (step_reverse_nil state work)
  | cons bit buffer ih =>
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        afterStep (step_reverse_cons state bit work buffer) (ih (bitState bit) (bit :: work))

def zip_run (state : State) (input : List (Option Bool)) (work buffer : List Bool) :
    EvalsToInTime machine.step (configuration (some .zip) state input work buffer)
      (some (terminal (accumulated buffer (zipResult input work))))
      (input.length + work.length + buffer.length + 3) := by
  induction input generalizing state work buffer with
  | nil =>
      cases work with
      | nil =>
          simpa only [zipResult, accumulated, List.append_nil, List.length_nil, Nat.zero_add] using
            increaseBudget (afterStep (step_zip_empty state buffer) (reverse_run (some none) [] buffer))
              (by omega : buffer.length + 1 + 1 ≤ buffer.length + 3)
      | cons bit work =>
          exact increaseBudget
            (afterStep (step_zip_extra_work state bit work buffer) (clearInput_run (bitState bit) [] work buffer))
            (by simp only [List.length_nil, List.length_cons]; omega)
  | cons entry input ih =>
      cases entry with
      | none =>
          exact increaseBudget
            (afterStep (step_zip_separator state input work buffer) (clearInput_run (some none) input work buffer))
            (by simp only [List.length_cons]; omega)
      | some bit =>
          cases work with
          | nil =>
              exact increaseBudget
                (afterStep (step_zip_extra_input state bit input buffer) (clearInput_run (some none) input [] buffer))
                (by simp only [List.length_cons, List.length_nil]; omega)
          | cons head work =>
              simp only [zipResult, accumulated_cons]
              exact increaseBudget
                (afterStep (step_zip_bits state bit head input work buffer)
                  (ih (bitState (head && bit)) work ((head && bit) :: buffer)))
                (by simp only [List.length_cons]; omega)

def scan_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .scan) state input work [])
      (some (terminal ((scanResult input work).getD [])))
      (2 * input.length + work.length + 4) := by
  induction input generalizing state work with
  | nil =>
      exact increaseBudget
        (afterStep (step_scan_nil state work) (clearInput_run none [] work []))
        (by simp only [List.length_nil]; omega)
  | cons entry input ih =>
      cases entry with
      | none =>
          have result : accumulated [] (zipResult input work) = (zipResult input work).getD [] := by
            cases zipResult input work <;> rfl
          simp only [scanResult]
          rw [← result]
          exact increaseBudget
            (afterStep (step_scan_separator state input work) (zip_run (some none) input work []))
            (by simp only [List.length_cons, List.length_nil]; omega)
      | some bit =>
          exact increaseBudget
            (afterStep (step_scan_bit state bit input work) (ih (bitState bit) (bit :: work)))
            (by simp only [List.length_cons]; omega)

def rawJoin_outputs (input : List (Option Bool)) :
    TM2OutputsInTime machine input (some (rawJoin input)) (2 * input.length + 4) := by
  change EvalsToInTime machine.step (initList machine input)
    (some (haltList machine (rawJoin input))) _
  rw [initial_configuration]
  simpa only [terminal_configuration, rawJoin, List.length_nil, Nat.add_zero] using scan_run none input []

noncomputable def rawJoin_polyTime :
    TM2ComputableInPolyTime (id : List (Option Bool) → List (Option Bool))
      (id : List Bool → List Bool) rawJoin where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 4
  outputsFun input := by simpa using rawJoin_outputs input

end SaturationMonoid.ComplexityProjection.SATSource.JoinMachine
