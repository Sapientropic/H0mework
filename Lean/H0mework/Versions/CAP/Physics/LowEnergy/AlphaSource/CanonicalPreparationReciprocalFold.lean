import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalWordBudget
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockGuard

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumReciprocalBudget
open scoped BigOperators

abbrev BudgetAt (n : ℕ) := Fin (n+1) → ℝ

def nextBudget (B : ℕ → ℝ) (u0 : ℝ) {n : ℕ} (previous : BudgetAt n) : BudgetAt (n+1) :=
  fun j => if h : j.val<n+1 then previous ⟨j.val,h⟩ else
    u0*∑ r : Fin (n+1),((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*
      previous ⟨n-r.val,by have := r.isLt; omega⟩

def inverseTable (B : ℕ → ℝ) (u0 : ℝ) (n : ℕ) : BudgetAt n :=
  Nat.rec (motive:=BudgetAt) (fun _ => u0) (fun _ previous => nextBudget B u0 previous) n

def inverseBudget (B : ℕ → ℝ) (u0 : ℝ) (n : ℕ) : ℝ := inverseTable B u0 n (Fin.last n)

theorem inverseTable_zero (B : ℕ → ℝ) (u0 : ℝ) : inverseTable B u0 0 0=u0 := rfl

theorem inverseTable_preserves (B : ℕ → ℝ) (u0 : ℝ) (n : ℕ) (j : Fin (n+1)) :
    inverseTable B u0 (n+1) (Fin.castSucc j)=inverseTable B u0 n j := by
  simp only [inverseTable,nextBudget,Fin.val_castSucc,j.isLt,dif_pos]

theorem inverseTable_previous (B : ℕ → ℝ) (u0 : ℝ) (small big : ℕ) (paid : small ≤ big)
    (j : Fin (small+1)) :
    inverseTable B u0 big (Fin.castLE (by omega) j)=inverseTable B u0 small j := by
  induction big,paid using Nat.le_induction with
  | base => rfl
  | succ big paid ih =>
    have index : (Fin.castLE (by omega) j : Fin (big+2))=
        Fin.castSucc (Fin.castLE (by omega) j : Fin (big+1)) := rfl
    rw [index,inverseTable_preserves,ih]

theorem inverseTable_readback (B : ℕ → ℝ) (u0 : ℝ) (n : ℕ) (j : Fin (n+1)) :
    inverseTable B u0 n j=inverseBudget B u0 j.val := by
  have read := inverseTable_previous B u0 j.val n (by have := j.isLt; omega) (Fin.last j.val)
  have same : (Fin.castLE (by have := j.isLt; omega) (Fin.last j.val) : Fin (n+1))=j := by
    apply Fin.ext
    rfl
  rw [same] at read
  exact read

theorem inverseBudget_zero (B : ℕ → ℝ) (u0 : ℝ) : inverseBudget B u0 0=u0 := rfl

theorem inverseBudget_succ (B : ℕ → ℝ) (u0 : ℝ) (n : ℕ) :
    inverseBudget B u0 (n+1)=u0*∑ r : Fin (n+1),
      ((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*inverseBudget B u0 (n-r.val) := by
  unfold inverseBudget
  simp only [inverseTable,nextBudget,Fin.val_last,lt_self_iff_false,dite_false]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  change ((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*
      inverseTable B u0 n ⟨n-r.val,by have := r.isLt; omega⟩ =
    ((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*inverseBudget B u0 (n-r.val)
  rw [inverseTable_readback]

theorem inverseTable_nonnegative (B : ℕ → ℝ) (u0 : ℝ)
    (zero : 0 ≤ u0) (positive : ∀ n, 0 ≤ B n) (n : ℕ) (j : Fin (n+1)) :
    0 ≤ inverseTable B u0 n j := by
  induction n with
  | zero => exact zero
  | succ n ih =>
    change 0 ≤ nextBudget B u0 (inverseTable B u0 n) j
    unfold nextBudget
    split_ifs
    · exact ih _
    · apply mul_nonneg zero
      apply Finset.sum_nonneg
      intro r _
      exact mul_nonneg (mul_nonneg (by positivity) (positive _)) (ih _)

theorem inverseBudget_nonnegative (B : ℕ → ℝ) (u0 : ℝ)
    (zero : 0 ≤ u0) (positive : ∀ n, 0 ≤ B n) (n : ℕ) :
    0 ≤ inverseBudget B u0 n := inverseTable_nonnegative B u0 zero positive n (Fin.last n)

def sourceTInverseBudget (B : ℕ → ℝ) : ℕ → ℝ := inverseBudget B 15
def sourceDetInverseBudget (B : ℕ → ℝ) : ℕ → ℝ := inverseBudget B 3375

theorem sourceTInverseBudget_succ (B : ℕ → ℝ) (n : ℕ) :
    sourceTInverseBudget B (n+1)=15*∑ r : Fin (n+1),
      ((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*sourceTInverseBudget B (n-r.val) :=
  inverseBudget_succ B 15 n

theorem sourceDetInverseBudget_succ (B : ℕ → ℝ) (n : ℕ) :
    sourceDetInverseBudget B (n+1)=3375*∑ r : Fin (n+1),
      ((n+1).choose (r.val+1) : ℝ)*B (r.val+1)*sourceDetInverseBudget B (n-r.val) :=
  inverseBudget_succ B 3375 n

end LowEnergy.PreparationVacuumReciprocalBudget
