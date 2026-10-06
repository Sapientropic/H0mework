import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaOrderedRows

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalBudget PreparationVacuumCentralBudget
open PreparationVacuumClockSymbol
open scoped BigOperators ContDiff Topology

def derivativeExtra {k : ℕ} (e : ArenaExpression k) : ℕ :=
  ArenaExpression.rec (motive_1:=fun _=>ℕ) (motive_2:=fun _=>ℕ)
    (fun _=>0) (fun _ _=>0) (fun _ _=>0)
    (fun r _ _ a b=>r+max a b) (fun _ _ word=>word)
    (fun _ _ a b=>max a b) 0 (fun _ _ a b=>max a b) e

def derivativeDemand {k : ℕ} (e : ArenaExpression k) (m : ℕ) : ℕ :=
  m+derivativeExtra e

@[simp] theorem derivativeExtra_literal {k : ℕ} (c : ℝ) :
    derivativeExtra (.literal c : ArenaExpression k)=0 := rfl
@[simp] theorem derivativeExtra_source {k : ℕ} (d : Fin 3) (j : Fin 14) :
    derivativeExtra (.source d j : ArenaExpression k)=0 := rfl
@[simp] theorem derivativeExtra_clock {k : ℕ} (l : Fin (k+1)) (a : Fin 4) :
    derivativeExtra (.clock l a : ArenaExpression k)=0 := rfl
@[simp] theorem derivativeExtra_moyal {k : ℕ} (r : ℕ) (e f : ArenaExpression k) :
    derivativeExtra (.moyal r e f)=r+max (derivativeExtra e) (derivativeExtra f) := rfl
@[simp] theorem derivativeExtra_add {k : ℕ} (e f : ArenaExpression k) :
    derivativeExtra (.add e f)=max (derivativeExtra e) (derivativeExtra f) := rfl

theorem derivativeExtra_row {k : ℕ} (c : NormalizedCoefficient) (word : List (ArenaExpression k)) :
    derivativeExtra (.row c word)=word.foldr (fun e n=>max (derivativeExtra e) n) 0 := by
  induction word with
  | nil=>rfl
  | cons e word ih=>
    change max (derivativeExtra e) (derivativeExtra (.row c word))=_
    rw [ih]
    rfl

theorem derivativeDemand_moyal {k : ℕ} (r m : ℕ) (e f : ArenaExpression k) :
    derivativeDemand (.moyal r e f) m=
      max (derivativeDemand e (m+r)) (derivativeDemand f (m+r)) := by
  simp only [derivativeDemand,derivativeExtra_moyal,←Nat.add_max_add_left,Nat.add_assoc]

structure PrimitiveArrays (k : ℕ) where
  leaf : Fin 3 → Fin 14 → ArrayBound
  clock : Fin (k+1) → Fin 4 → ArrayBound
  central : NormalizedCoefficient → ArrayBound

def expressionArray {k : ℕ} (input : PrimitiveArrays k) (e : ArenaExpression k) : ArrayBound :=
  ArenaExpression.rec (motive_1:=fun _=>ArrayBound) (motive_2:=fun _=>ArrayBound)
    (fun c=>constantArray |c|) input.leaf input.clock
    (fun r _ _ a b m=>moyalScale r*convolution m r a b)
    (fun c _ word=>productArray (input.central c) word)
    (fun _ _ a b m=>a m+b m) (constantArray 1)
    (fun _ _ head tail=>productArray head tail) e

@[simp] theorem expressionArray_literal {k : ℕ} (input : PrimitiveArrays k) (c : ℝ) :
    expressionArray input (.literal c)=constantArray |c| := rfl
@[simp] theorem expressionArray_source {k : ℕ} (input : PrimitiveArrays k) (d : Fin 3) (j : Fin 14) :
    expressionArray input (.source d j)=input.leaf d j := rfl
@[simp] theorem expressionArray_clock {k : ℕ} (input : PrimitiveArrays k) (l : Fin (k+1)) (a : Fin 4) :
    expressionArray input (.clock l a)=input.clock l a := rfl
@[simp] theorem expressionArray_moyal {k : ℕ} (input : PrimitiveArrays k) (r : ℕ) (e f : ArenaExpression k) :
    expressionArray input (.moyal r e f)=
      (fun m=>moyalScale r*convolution m r (expressionArray input e) (expressionArray input f)) := rfl
@[simp] theorem expressionArray_add {k : ℕ} (input : PrimitiveArrays k) (e f : ArenaExpression k) :
    expressionArray input (.add e f)=(fun m=>expressionArray input e m+expressionArray input f m) := rfl

theorem expressionArray_row {k : ℕ} (input : PrimitiveArrays k) (c : NormalizedCoefficient)
    (word : List (ArenaExpression k)) : expressionArray input (.row c word)=
      productArray (input.central c) (orderedArray (word.map (expressionArray input))) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>ArrayBound) (motive_2:=fun _=>ArrayBound)
      (fun c=>constantArray |c|) input.leaf input.clock
      (fun r _ _ a b m=>moyalScale r*convolution m r a b)
      (fun c _ word=>productArray (input.central c) word)
      (fun _ _ a b m=>a m+b m) (constantArray 1)
      (fun _ _ head tail=>productArray head tail) word=
        orderedArray (word.map (expressionArray input)) by
    exact congrArg (productArray (input.central c)) same
  induction word with
  | nil=>rfl
  | cons e word ih=>change productArray (expressionArray input e) _=_;rw [ih];rfl

structure PrimitiveNonnegative {k : ℕ} (input : PrimitiveArrays k) : Prop where
  leaf : ∀ d j m,0 ≤ input.leaf d j m
  clock : ∀ l a m,0 ≤ input.clock l a m
  central : ∀ c m,0 ≤ input.central c m

theorem expressionArray_nonnegative {k : ℕ} (input : PrimitiveArrays k)
    (positive : PrimitiveNonnegative input) (e : ArenaExpression k) :
    ∀ m,0 ≤ expressionArray input e m := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ m,0 ≤ expressionArray input e m)
    (motive_2:=fun word=>∀ m,0 ≤ orderedArray (word.map (expressionArray input)) m)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c;exact constantArray_nonnegative |c| (abs_nonneg c)
  · intro d j;exact positive.leaf d j
  · intro l a;exact positive.clock l a
  · intro r e f he hf m
    change 0 ≤ moyalScale r*convolution m r (expressionArray input e) (expressionArray input f)
    apply mul_nonneg (by unfold moyalScale;positivity)
    unfold convolution
    exact Finset.sum_nonneg (fun j _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (he _)) (hf _))
  · intro c word ih
    rw [expressionArray_row]
    exact productArray_nonnegative _ _ (positive.central c) ih
  · intro e f he hf m;exact add_nonneg (he m) (hf m)
  · exact constantArray_nonnegative 1 (by norm_num)
  · intro e word he ih;exact productArray_nonnegative _ _ he ih

end LowEnergy.PreparationVacuumArenaRows
