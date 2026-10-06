import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaCollectRows

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaCollect
open PreparationVacuumPoleCancellation PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic
open PreparationVacuumClockSymbol PreparationVacuumArenaRows
open scoped BigOperators

private theorem orderedProduct_append (fs gs : List PreparationVacuumArenaBudget.ComplexSymbol) (x : Phase) :
    orderedProduct (fs++gs) x=orderedProduct fs x*orderedProduct gs x := by
  induction fs with
  | nil=>simp [orderedProduct]
  | cons f rest ih=>
    change f x*orderedProduct (rest++gs) x=(f x*orderedProduct rest x)*orderedProduct gs x
    rw [ih,mul_assoc]

def multiplyRow {k : ℕ} (left right : Row k) : Row k where
  coefficient:=cancelCoefficient (multiplyCoefficient left.coefficient right.coefficient)
  word:=left.word++right.word

theorem multiplyRow_value {k : ℕ} (left right : Row k) (x : Phase) (hx : x∈poleDomain) :
    rowValue (multiplyRow left right) x=rowValue left x*rowValue right x := by
  simp only [rowValue,multiplyRow,cancelCoefficient_source _ x hx,multiplyCoefficient_source,
    Complex.ofReal_mul,List.map_append]
  rw [orderedProduct_append]
  ring

def multiplyRows {k : ℕ} (left right : List (Row k)) : List (Row k) :=
  left.flatMap (fun l=>right.map (multiplyRow l))

theorem multiplyRows_value {k : ℕ} (left right : List (Row k)) (x : Phase) (hx : x∈poleDomain) :
    rowsValue (multiplyRows left right) x=rowsValue left x*rowsValue right x := by
  have one (l : Row k) : rowsValue (right.map (multiplyRow l)) x=rowValue l x*rowsValue right x := by
    induction right with
    | nil=>simp [rowsValue]
    | cons r rest ih=>
      simp only [List.map_cons,rowsValue,List.sum_cons,multiplyRow_value _ _ x hx] at ih ⊢
      rw [ih]
      ring
  simp only [rowsValue] at one
  induction left with
  | nil=>simp [multiplyRows,rowsValue]
  | cons l rest ih=>
    simp only [multiplyRows,List.flatMap_cons,rowsValue,List.map_append,List.sum_append] at ih ⊢
    rw [one,ih]
    simp only [List.map_cons,List.sum_cons]
    ring

def unitRow (k : ℕ) : Row k := ⟨polynomialCoefficient 1,[]⟩

theorem unitRow_value (k : ℕ) (x : Phase) : rowValue (unitRow k) x=1 := by
  simp [rowValue,unitRow,polynomialCoefficient_source,polynomialSymbol,orderedProduct]

def productRows {k : ℕ} (words : List (List (Row k))) : List (Row k) :=
  words.foldr (fun a b=>collectRows (multiplyRows a b)) [unitRow k]

theorem productRows_value {k : ℕ} (words : List (List (Row k))) (x : Phase) (hx : x∈poleDomain) :
    rowsValue (productRows words) x=(words.map (fun rows=>rowsValue rows x)).prod := by
  induction words with
  | nil=>simp [productRows,rowsValue,unitRow_value]
  | cons word rest ih=>
    change rowsValue (collectRows (multiplyRows word (productRows rest))) x=_
    rw [collectRows_value _ x hx,multiplyRows_value _ _ x hx,ih]
    rfl

end LowEnergy.PreparationVacuumArenaCollect
