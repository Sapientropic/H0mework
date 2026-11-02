import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Counting
open Institutions.Capitalism.Universal.Source.Program
open Distributed

def wordCount (alphabetSize : Nat) : Nat → Nat
  | 0 => 1
  | depth+1 => 1 + alphabetSize * wordCount alphabetSize depth

universe u v

theorem sequences_count {α : Type u} (alphabet : List α) (depth : Nat) :
    wordCount alphabet.length depth = (sequences alphabet depth).length := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [wordCount,sequences,List.length_flatMap,←ih,Nat.add_comm]

theorem pi_length {α : Type u} [DecidableEq α] {β : α → Type v}
    (keys : List α) (choices : ∀ key, List (β key)) :
    (List.pi keys choices).length = (keys.map fun key => (choices key).length).prod := by
  induction keys with
  | nil => simp
  | cons key tail ih =>
      simp [List.pi_cons,List.length_flatMap,ih]

theorem constant_pi_length {α : Type u} [DecidableEq α] {β : Type v}
    (keys : List α) (choices : List β) :
    (List.pi keys (fun _ => choices)).length = choices.length ^ keys.length := by
  induction keys with
  | nil => simp
  | cons key tail ih =>
      simp [List.pi_cons,List.length_flatMap,ih,Nat.pow_succ,Nat.mul_comm]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

theorem words_count (depth : Nat) :
    wordCount code.actions.length depth = (words code.actions depth).length := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [wordCount,words,List.length_flatMap,←ih,Nat.add_comm]

def policiesCount : Nat :=
  wordCount code.actions.length code.actionLimit ^ code.keys.length

theorem policiesCount_exact : policiesCount code = code.policies.length := by
  rw [Code.policies,constant_pi_length,←words_count]
  rfl

def eventTablesCount : Nat :=
  (code.keys.map fun key => (ownMoves code key.1).length).prod

theorem eventTablesCount_exact : eventTablesCount code = (eventTables code).length := by
  rw [eventTables,pi_length]
  simp only [List.length_attach]
  rfl

def rulesCount : Nat := policiesCount code * eventTablesCount code

theorem rulesCount_exact : rulesCount code = (rules code).length := by
  rw [rulesCount,policiesCount_exact,eventTablesCount_exact]
  simp [rules,List.length_flatMap]

def programCount (fuel : Nat) : Nat := wordCount (rulesCount code) fuel

theorem programCount_exact (fuel : Nat) :
    programCount code fuel = (programs code fuel).length := by
  simpa only [programCount,rulesCount_exact,programs,List.length_map,List.length_attach]
    using sequences_count (rules code) fuel

def budgetCount (horizon : Nat) : Nat :=
  ((List.range (horizon+1)).map (programCount code)).sum

theorem budgetCount_exact (horizon : Nat) :
    budgetCount code horizon =
      ((List.range (horizon+1)).map fun room => (programs code room).length).sum := by
  unfold budgetCount
  have equal : programCount code = fun room => (programs code room).length := by
    funext room
    exact programCount_exact code room
  rw [equal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Counting
