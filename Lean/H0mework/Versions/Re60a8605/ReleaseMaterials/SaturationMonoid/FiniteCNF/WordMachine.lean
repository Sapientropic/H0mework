import Mathlib.Computability.TuringMachine.Computable
import Lean.Elab.Tactic.Omega

/-!
A fixed two-stack TM2 compares two Boolean words. The input alphabet is
`Option Bool`: `none` is the unique separator. The left word is reversed in
the input so the scanning phase builds its ordinary order on the work stack.
Every rejected input is drained, and the machine resets its finite state
before leaving one result bit on the output/work stack.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.WordMachine

open Turing StateTransition

def compareWords : List (Option Bool) → List Bool → Bool
  | [], work => work.isEmpty
  | none :: _, _ => false
  | some _ :: _, [] => false
  | some bit :: input, head :: work =>
      if bit = head then compareWords input work else false

def scanWords : List (Option Bool) → List Bool → Bool
  | [], _ => false
  | none :: input, work => compareWords input work
  | some bit :: input, work => scanWords input (bit :: work)

def rawMatch (input : List (Option Bool)) : Bool := scanWords input []

def pairCode (left right : List Bool) : List (Option Bool) :=
  left.reverse.map some ++ [none] ++ right.map some

theorem pairCode_length (left right : List Bool) :
    (pairCode left right).length = left.length + right.length + 1 := by
  simp only [pairCode, List.length_append, List.length_map, List.length_reverse,
    List.length_cons, List.length_nil]
  omega

theorem compareWords_true_iff (input : List (Option Bool)) (work : List Bool) :
    compareWords input work = true ↔ input = work.map some := by
  induction input generalizing work with
  | nil => cases work <;> simp [compareWords]
  | cons entry input ih =>
      cases entry with
      | none => cases work <;> simp [compareWords]
      | some bit =>
          cases work with
          | nil => simp [compareWords]
          | cons head work =>
              by_cases h : bit = head <;> simp [compareWords, h, ih]

theorem scanWords_prefix (initialWord : List Bool) (input : List (Option Bool))
    (work : List Bool) :
    scanWords (initialWord.map some ++ input) work =
      scanWords input (initialWord.reverse ++ work) := by
  induction initialWord generalizing work with
  | nil => rfl
  | cons bit initialWord ih =>
      simp [scanWords, ih, List.reverse_cons, List.append_assoc]

theorem rawMatch_pair (left right : List Bool) :
    rawMatch (pairCode left right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawMatch, pairCode, List.append_assoc, scanWords_prefix,
    List.reverse_reverse, List.append_nil]
  change compareWords (right.map some) left = true ↔ (left == right) = true
  rw [compareWords_true_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have recovered := congrArg (List.map (fun value : Option Bool => value.getD false)) h
    simpa using recovered.symm
  · rintro rfl
    rfl

theorem scanWords_true_iff (input : List (Option Bool)) (work : List Bool) :
    scanWords input work = true ↔
      ∃ initialWord : List Bool,
        input = initialWord.map some ++ [none] ++ (initialWord.reverse ++ work).map some := by
  induction input generalizing work with
  | nil =>
      constructor
      · simp [scanWords]
      · rintro ⟨initialWord, h⟩
        have size := congrArg List.length h
        simp only [List.length_nil, List.length_append, List.length_map,
          List.length_cons, List.length_reverse] at size
        omega
  | cons entry input ih =>
      cases entry with
      | none =>
          rw [scanWords, compareWords_true_iff]
          constructor
          · rintro rfl
            exact ⟨[], rfl⟩
          · rintro ⟨initialWord, h⟩
            cases initialWord with
            | nil => simpa using h
            | cons bit initialWord => simp at h
      | some bit =>
          rw [scanWords, ih]
          constructor
          · rintro ⟨initialWord, h⟩
            refine ⟨bit :: initialWord, ?_⟩
            simp only [List.map_cons, List.cons_append, List.reverse_cons,
              List.append_assoc]
            simpa only [List.append_assoc, List.nil_append, List.singleton_append]
              using congrArg (List.cons (some bit)) h
          · rintro ⟨initialWord, h⟩
            cases initialWord with
            | nil => simp at h
            | cons head initialWord =>
                simp only [List.map_cons, List.cons_append, List.cons.injEq,
                  Option.some.injEq] at h
                rcases h with ⟨rfl, h⟩
                exact ⟨initialWord, by simpa [List.reverse_cons, List.append_assoc] using h⟩

theorem rawMatch_true_iff (input : List (Option Bool)) :
    rawMatch input = true ↔ ∃ word : List Bool, input = pairCode word word := by
  rw [rawMatch, scanWords_true_iff]
  constructor
  · rintro ⟨initialWord, h⟩
    exact ⟨initialWord.reverse, by simpa [pairCode] using h⟩
  · rintro ⟨word, h⟩
    exact ⟨word.reverse, by simpa [pairCode] using h⟩

inductive Phase
  | scan | compare | drainInput | drainWork
  deriving DecidableEq

instance : Fintype Phase where
  elems := {Phase.scan, Phase.compare, Phase.drainInput, Phase.drainWork}
  complete := by intro phase; cases phase <;> simp

abbrev State := Option (Option Bool)

abbrev Alphabet : Bool → Type
  | false => Option Bool
  | true => Bool

def bitState (bit : Bool) : State := some (some bit)
def bitOf (state : State) : Bool := (state.bind id).getD false
def separator (state : State) : Bool := state == some none
def success (state : State) : Bool := state == bitState true

abbrev Statement := TM2.Stmt Alphabet Phase State

open TM2.Stmt

def jump (phase : Phase) : Statement := goto fun _ => phase

def finish (answer : Bool) : Statement :=
  load (fun _ => none) (push true (fun _ => answer) halt)

def program : Phase → Statement
  | .scan =>
      pop false (fun _ head => head)
        (branch Option.isNone (jump .drainInput)
          (branch separator (jump .compare)
            (push true bitOf (jump .scan))))
  | .compare =>
      pop false (fun _ head => head)
        (branch Option.isNone
          (pop true (fun _ head => bitState head.isNone)
            (branch success (finish true) (jump .drainInput)))
          (branch separator (jump .drainInput)
            (pop true (fun state head => bitState (head == some (bitOf state)))
              (branch success (jump .compare) (jump .drainInput)))))
  | .drainInput =>
      pop false (fun _ head => head)
        (branch Option.isNone (jump .drainWork) (jump .drainInput))
  | .drainWork =>
      pop true (fun _ head => some head)
        (branch separator (finish false) (jump .drainWork))

abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet
  Λ := Phase
  main := .scan
  σ := State
  initialState := none
  m := program

def tapes (input : List (Option Bool)) (work : List Bool) :
    (k : Bool) → List (Alphabet k)
  | false => input
  | true => work

@[simp] theorem stacks_input (input : List (Option Bool)) (work : List Bool) :
    tapes input work false = input := rfl

@[simp] theorem stacks_work (input : List (Option Bool)) (work : List Bool) :
    tapes input work true = work := rfl

@[simp] theorem update_input (input next : List (Option Bool)) (work : List Bool) :
    Function.update (tapes input work) false next = tapes next work := by
  funext k
  cases k <;> simp [Function.update, tapes]

@[simp] theorem update_work (input : List (Option Bool)) (work next : List Bool) :
    Function.update (tapes input work) true next = tapes input next := by
  funext k
  cases k <;> simp [Function.update, tapes]

def configuration (phase : Option Phase) (state : State)
    (input : List (Option Bool)) (work : List Bool) : machine.Cfg :=
  ⟨phase, state, tapes input work⟩

def terminal (answer : Bool) : machine.Cfg := configuration none none [] [answer]

theorem initial_configuration (input : List (Option Bool)) :
    initList machine input = configuration (some .scan) none input [] := by
  unfold initList configuration
  congr 1
  funext k
  cases k <;> rfl

theorem terminal_configuration (answer : Bool) :
    terminal answer = haltList machine [answer] := by
  unfold terminal configuration haltList
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem step_scan_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .scan) state [] work) =
      some (configuration (some .drainInput) none [] work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_scan_separator (state : State) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (none :: input) work) =
      some (configuration (some .compare) (some none) input work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_scan_bit (state : State) (bit : Bool)
    (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .scan) state (some bit :: input) work) =
      some (configuration (some .scan) (bitState bit) input (bit :: work)) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator, bitOf, bitState] <;> rfl

@[simp] theorem step_drainInput_nil (state : State) (work : List Bool) :
    machine.step (configuration (some .drainInput) state [] work) =
      some (configuration (some .drainWork) none [] work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_drainInput_cons (state : State) (entry : Option Bool)
    (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .drainInput) state (entry :: input) work) =
      some (configuration (some .drainInput) (some entry) input work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump]
  rfl

@[simp] theorem step_drainWork_nil (state : State) :
    machine.step (configuration (some .drainWork) state [] []) = some (terminal false) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
    separator, finish, terminal]
  rfl

@[simp] theorem step_drainWork_cons (state : State) (bit : Bool) (work : List Bool) :
    machine.step (configuration (some .drainWork) state [] (bit :: work)) =
      some (configuration (some .drainWork) (bitState bit) [] work) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator, bitState] <;> rfl

@[simp] theorem step_compare_empty (state : State) :
    machine.step (configuration (some .compare) state [] []) = some (terminal true) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
    success, bitState, finish, terminal]
  rfl

@[simp] theorem step_compare_extra_work (state : State) (bit : Bool) (work : List Bool) :
    machine.step (configuration (some .compare) state [] (bit :: work)) =
      some (configuration (some .drainInput) (bitState false) [] work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, success, bitState]
  rfl

@[simp] theorem step_compare_separator (state : State) (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .compare) state (none :: input) work) =
      some (configuration (some .drainInput) (some none) input work) := by
  simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump, separator]
  rfl

@[simp] theorem step_compare_extra_input (state : State) (bit : Bool) (input : List (Option Bool)) :
    machine.step (configuration (some .compare) state (some bit :: input) []) =
      some (configuration (some .drainInput) (bitState false) input []) := by
  cases bit <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
      separator, success, bitOf, bitState] <;> rfl

@[simp] theorem step_compare_bits (state : State) (bit head : Bool)
    (input : List (Option Bool)) (work : List Bool) :
    machine.step (configuration (some .compare) state (some bit :: input) (head :: work)) =
      some (if bit = head then configuration (some .compare) (bitState true) input work
        else configuration (some .drainInput) (bitState false) input work) := by
  cases bit <;> cases head <;>
    simp [FinTM2.step, TM2.step, configuration, program, TM2.stepAux, jump,
      separator, success, bitOf, bitState] <;> rfl

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

def drainWork_run (state : State) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .drainWork) state [] work)
      (some (terminal false)) (work.length + 1) := by
  induction work generalizing state with
  | nil => exact oneStep (step_drainWork_nil state)
  | cons bit work ih =>
      exact afterStep (step_drainWork_cons state bit work) (ih (bitState bit))

def drainInput_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .drainInput) state input work)
      (some (terminal false)) (input.length + work.length + 2) := by
  induction input generalizing state with
  | nil =>
      exact increaseBudget
        (afterStep (step_drainInput_nil state work) (drainWork_run none work)) (by simp)
  | cons entry input ih =>
      exact increaseBudget
        (afterStep (step_drainInput_cons state entry input work) (ih (some entry)))
        (by simp only [List.length_cons]; omega)

def compare_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .compare) state input work)
      (some (terminal (compareWords input work))) (input.length + work.length + 2) := by
  induction input generalizing state work with
  | nil =>
      cases work with
      | nil => exact increaseBudget (oneStep (step_compare_empty state)) (by decide)
      | cons bit work =>
          exact increaseBudget
            (afterStep (step_compare_extra_work state bit work) (drainInput_run (bitState false) [] work))
            (by simp only [List.length_nil, List.length_cons]; omega)
  | cons entry input ih =>
      cases entry with
      | none =>
          exact increaseBudget
            (afterStep (step_compare_separator state input work) (drainInput_run (some none) input work))
            (by simp only [List.length_cons]; omega)
      | some bit =>
          cases work with
          | nil =>
              exact increaseBudget
                (afterStep (step_compare_extra_input state bit input) (drainInput_run (bitState false) input []))
                (by simp only [List.length_cons, List.length_nil]; omega)
          | cons head work =>
              by_cases same : bit = head
              · have step := step_compare_bits state bit head input work
                rw [if_pos same] at step
                simp only [compareWords, if_pos same]
                exact increaseBudget (afterStep step (ih (bitState true) work))
                  (by simp only [List.length_cons]; omega)
              · have step := step_compare_bits state bit head input work
                rw [if_neg same] at step
                simp only [compareWords, if_neg same]
                exact increaseBudget (afterStep step (drainInput_run (bitState false) input work))
                  (by simp only [List.length_cons]; omega)

def scan_run (state : State) (input : List (Option Bool)) (work : List Bool) :
    EvalsToInTime machine.step (configuration (some .scan) state input work)
      (some (terminal (scanWords input work))) (2 * input.length + work.length + 3) := by
  induction input generalizing state work with
  | nil =>
      exact increaseBudget
        (afterStep (step_scan_nil state work) (drainInput_run none [] work))
        (by simp only [List.length_nil]; omega)
  | cons entry input ih =>
      cases entry with
      | none =>
          exact increaseBudget
            (afterStep (step_scan_separator state input work) (compare_run (some none) input work))
            (by simp only [List.length_cons]; omega)
      | some bit =>
          exact increaseBudget
            (afterStep (step_scan_bit state bit input work) (ih (bitState bit) (bit :: work)))
            (by simp only [List.length_cons]; omega)

def rawMatch_outputs (input : List (Option Bool)) :
    TM2OutputsInTime machine input (some [rawMatch input]) (2 * input.length + 3) := by
  change EvalsToInTime machine.step (initList machine input)
    (some (haltList machine [rawMatch input])) _
  rw [initial_configuration]
  simpa only [terminal_configuration, rawMatch, List.length_nil, Nat.add_zero] using scan_run none input []

noncomputable def rawMatch_polyTime :
    TM2ComputableInPolyTime (id : List (Option Bool) → List (Option Bool))
      Computability.encodeBool rawMatch where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    simpa [Computability.encodeBool] using rawMatch_outputs input

end SaturationMonoid.ComplexityProjection.SATSource.WordMachine
