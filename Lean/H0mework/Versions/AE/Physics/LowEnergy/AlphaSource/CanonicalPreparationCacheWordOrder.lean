import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationNumericUnitConsumers
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceCacheRules
open PreparationVacuumArenaCollect PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient
open PreparationVacuumArenaRows PreparationVacuumCentralBudget PreparationVacuumPrincipalBudget
open PreparationVacuumClockSymbol PreparationVacuumPoleCancellation
open scoped BigOperators
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

-- Labels are the original cache's presentation data; they carry no physical value.
structure AtomLabel (k : ℕ) where
  expression : ArenaExpression k
  serial : ℕ
  central : Bool

def originalWordOrder {k : ℕ} (word : List (AtomLabel k)) : List (AtomLabel k) :=
  (word.filter (fun a=>a.central)).mergeSort (fun a b=>a.serial ≤ b.serial)++
    word.filter (fun a=> !a.central)

theorem originalWordOrder_perm {k : ℕ} (word : List (AtomLabel k)) :
    (originalWordOrder word).Perm word := by
  exact ((List.mergeSort_perm _ _).append_right _).trans (List.filter_append_perm _ word)

def wordValue {k : ℕ} (word : List (AtomLabel k)) (x : Phase) : ℂ :=
  (word.map (fun a=>arenaEvaluate a.expression x)).prod

theorem originalWordOrder_value {k : ℕ} (word : List (AtomLabel k)) (x : Phase) :
    wordValue (originalWordOrder word) x=wordValue word x :=
  ((originalWordOrder_perm word).map _).prod_eq

theorem orderedArray_perm (left right : List ArrayBound) (same : left.Perm right) :
    orderedArray left=orderedArray right := by
  induction same with
  | nil=>rfl
  | cons a _ ih=>change productArray a (orderedArray _)=productArray a (orderedArray _);rw [ih]
  | swap a b rest=>
    change productArray b (productArray a (orderedArray rest))=
      productArray a (productArray b (orderedArray rest))
    rw [←productArray_assoc,productArray_comm b a,productArray_assoc]
  | trans _ _ ih₁ ih₂=>exact ih₁.trans ih₂

def wordArray {k : ℕ} (arrays : ArenaExpression k → ArrayBound) (word : List (AtomLabel k)) : ArrayBound :=
  orderedArray (word.map (fun a=>arrays a.expression))

theorem originalWordOrder_array {k : ℕ} (arrays : ArenaExpression k → ArrayBound)
    (word : List (AtomLabel k)) : wordArray arrays (originalWordOrder word)=wordArray arrays word :=
  orderedArray_perm _ _ ((originalWordOrder_perm word).map _)

def orderedRow {k : ℕ} (c : NormalizedCoefficient) (word : List (AtomLabel k)) : Row k :=
  ⟨c,(originalWordOrder word).map AtomLabel.expression⟩

theorem orderedRow_source {k : ℕ} (c : NormalizedCoefficient) (word : List (AtomLabel k)) (x : Phase) :
    rowValue (orderedRow c word) x=(coefficientValue c x : ℂ)*wordValue word x := by
  have read : orderedProduct (((originalWordOrder word).map AtomLabel.expression).map arenaEvaluate) x=
      wordValue (originalWordOrder word) x := by
    simp only [orderedProduct,wordValue,List.foldr_map,List.prod_eq_foldr]
  rw [orderedRow,rowValue,read,originalWordOrder_value]

theorem orderedRow_array {k : ℕ} (input : PrimitiveArrays k) (c : NormalizedCoefficient)
    (word : List (AtomLabel k)) :
    expressionArray input (.row c (orderedRow c word).word)=
      productArray (input.central c) (wordArray (expressionArray input) word) := by
  rw [expressionArray_row]
  have read : orderedArray ((orderedRow c word).word.map (expressionArray input))=
      wordArray (expressionArray input) (originalWordOrder word) := by
    simp only [orderedRow,wordArray,List.map_map,Function.comp_def]
  rw [read,originalWordOrder_array]

end LowEnergy.PreparationVacuumSourceCacheRules
