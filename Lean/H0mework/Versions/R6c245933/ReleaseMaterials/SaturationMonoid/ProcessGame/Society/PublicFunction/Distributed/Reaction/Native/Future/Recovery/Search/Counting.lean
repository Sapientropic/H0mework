import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Billing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Counting
open Institutions.Capitalism.Universal.Source.Program

@[ext] structure Size where
  rows : Nat
  actions : Nat
  deriving DecidableEq, Repr

def measure {α : Type} (rows : List (List α)) : Size :=
  ⟨rows.length,(rows.map List.length).sum⟩
def add (a b : Size) : Size := ⟨a.rows+b.rows,a.actions+b.actions⟩
def prefixed (length : Nat) (a : Size) : Size := ⟨a.rows,length*a.rows+a.actions⟩

@[simp] theorem measure_nil {α : Type} : measure ([] : List (List α)) = ⟨0,0⟩ := rfl
@[simp] theorem measure_cons {α : Type} (head : List α) (tail : List (List α)) :
    measure (head::tail) = ⟨(measure tail).rows+1,head.length+(measure tail).actions⟩ := by
  simp [measure]
@[simp] theorem measure_append {α : Type} (left right : List (List α)) :
    measure (left++right) = add (measure left) (measure right) := by
  simp [measure,add,List.map_append,List.sum_append]

theorem measure_prefix {α : Type} (word : List α) (rows : List (List α)) :
    measure (rows.map (word++·)) = prefixed word.length (measure rows) := by
  induction rows with
  | nil => simp [prefixed]
  | cons head tail ih =>
      simp only [List.map_cons,measure_cons,ih,prefixed,List.length_append]
      congr 1; ring

theorem measure_suffix {α : Type} (word : List α) (rows : List (List α)) :
    measure (rows.map (·++word)) = prefixed word.length (measure rows) := by
  induction rows with
  | nil => simp [prefixed]
  | cons head tail ih =>
      simp only [List.map_cons,measure_cons,ih,prefixed,List.length_append]
      congr 1; ring

theorem measure_prepend_family {α : Type} (alphabet : List α) (rows : List (List α)) :
    measure (alphabet.flatMap fun head => rows.map (List.cons head)) =
      ⟨alphabet.length*(measure rows).rows,
        alphabet.length*((measure rows).rows+(measure rows).actions)⟩ := by
  induction alphabet with
  | nil => simp
  | cons head tail ih =>
      have front : measure (rows.map (List.cons head)) = prefixed 1 (measure rows) :=
        measure_prefix [head] rows
      simp only [List.flatMap_cons,measure_append,front,ih,List.length_cons,add,prefixed]
      congr 1 <;> ring

/-- The bounded-word recursion counts repeated entries exactly as the source does. -/
def wordsSize (alphabetSize : Nat) : Nat → Size
  | 0 => ⟨1,0⟩
  | depth+1 => let previous := wordsSize alphabetSize depth
      ⟨1+alphabetSize*previous.rows,alphabetSize*(previous.rows+previous.actions)⟩

variable {Party Good Port Technology Instrument : Type}

theorem wordsSize_is_original
    (alphabet : List (Request Party Good Port Technology Instrument)) (depth : Nat) :
    wordsSize alphabet.length depth = measure (words alphabet depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [words,measure_cons,measure_prepend_family,List.length_nil,wordsSize,ih]
      congr 1 <;> omega

/-- Fold the production-prefixed lengths without generating any preparation words. -/
def repairsSize (tails : Size) : Nat → Size
  | 0 => ⟨0,0⟩
  | count+1 => add (repairsSize tails count) (prefixed count tails)

theorem repairsSize_is_original {α : Type} (tails : List (List α)) (work : α) (count : Nat) :
    repairsSize (measure tails) count = measure
      ((List.range count).flatMap fun n => tails.map (List.replicate n work++·)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [repairsSize,List.range_succ,List.flatMap_append,List.flatMap_singleton,
        measure_append,measure_prefix,List.length_replicate,ih]

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (model : Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (before : Current model) (actor : Party) (original : List (Action model))

def plain : Size := repairsSize
  (wordsSize (menu model actor).length model.actionLimit) (limit model before actor original+1)

omit [DecidableEq Instrument] in
theorem plain_is_original : plain model before actor original = measure (repairs model before actor original) := by
  unfold plain repairs
  rw [wordsSize_is_original,repairsSize_is_original]

theorem authorizationWord_length (commands : List (Mandate.Command Party)) :
    (authorizationWord model before actor commands).length = commands.length := by
  induction commands generalizing before with
  | nil => rfl
  | cons head tail ih => simpa only [authorizationWord,List.length_cons] using congrArg Nat.succ (ih _)

theorem authorizations_size : measure (authorizations model before actor) = ⟨3,6⟩ := by
  simp [authorizations,measure,authorizationWord_length]

private theorem authorized_size (rows : List (List (Action model))) :
    measure (rows.flatMap fun preparation =>
      (authorizations model before actor).map (·++preparation) ++
      (authorizations model ((⟨preparation⟩ : Proposal model).staged model before) actor).map
        (preparation++·)) = ⟨6*(measure rows).rows,6*(measure rows).actions+12*(measure rows).rows⟩ := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
      simp only [List.flatMap_cons,measure_append,measure_prefix,measure_suffix,
        authorizations_size,ih,measure_cons,add,prefixed]
      congr 1 <;> ring

def catalogueSize : Size :=
  let base := plain model before actor original
  if needsAuthorization model before original then ⟨7*base.rows,7*base.actions+12*base.rows⟩ else base

theorem catalogueSize_is_original :
    catalogueSize model before actor original = measure (catalogue model before actor original) := by
  unfold catalogueSize catalogue
  split
  next yes =>
    simp only [measure_append,authorizedRepairs,authorized_size,←plain_is_original,add]
    congr 1 <;> ring
  next no => simp only [List.append_nil,plain_is_original]

theorem affine_sum {α : Type} (rows : List (List α)) (a b : Nat) :
    (rows.map fun row => a*row.length+b).sum = a*(measure rows).actions+(measure rows).rows*b := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons,List.sum_cons,ih,measure_cons]
      ring

def comparisonUnits : Nat :=
  let size := catalogueSize model before actor original
  1+size.rows+original.length+3*size.actions+size.rows*original.length

theorem comparisonUnits_is_original : comparisonUnits model before actor original =
    Billing.comparisonUnits original (catalogue model before actor original) := by
  simp only [comparisonUnits,catalogueSize_is_original,Billing.comparisonUnits,affine_sum]
  simp only [measure]
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Counting
