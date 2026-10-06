import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaSourceConsumers
import Mathlib.Data.Nat.Size

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalRadii
open PreparationVacuumCentralBudget PreparationVacuumArenaRows
open scoped BigOperators

abbrev UpperExponent := Option ℕ
abbrev UpperArray := ℕ → UpperExponent

def exponentValue : UpperExponent → ℝ
  | none=>0
  | some e=>(2 : ℝ)^e

def roundExponent (v : ℝ) : UpperExponent :=
  if v=0 then none else some (Nat.size (⌈v⌉₊-1))

theorem exponentValue_nonnegative (e : UpperExponent) : 0 ≤ exponentValue e := by
  cases e <;> simp [exponentValue]

theorem nat_le_rounded_power (n : ℕ) (positive : 0<n) : n≤2^Nat.size (n-1) := by
  have exact:=Nat.lt_size_self (n-1)
  omega

theorem roundExponent_upper (v : ℝ) (nonnegative : 0 ≤ v) : v≤ exponentValue (roundExponent v) := by
  unfold roundExponent
  split_ifs with zero
  · simpa only [zero,exponentValue] using le_refl (0 : ℝ)
  · have positive : 0<⌈v⌉₊:=Nat.ceil_pos.mpr (lt_of_le_of_ne nonnegative (Ne.symm zero))
    have bound : (⌈v⌉₊ : ℝ)≤(2 : ℝ)^Nat.size (⌈v⌉₊-1) := by
      exact_mod_cast nat_le_rounded_power _ positive
    exact (Nat.le_ceil v).trans bound

def maximumExponent (xs : List ℕ) : ℕ := xs.foldr max 0

def upperSum (xs : List UpperExponent) : UpperExponent :=
  let nonzero:=xs.filterMap id
  if nonzero=[] then none else some (maximumExponent nonzero+Nat.size (nonzero.length-1))

theorem maximumExponent_mem (xs : List ℕ) (n : ℕ) (mem : n∈xs) : n≤ maximumExponent xs := by
  induction xs with
  | nil=>simp at mem
  | cons a xs ih=>
    rcases List.mem_cons.mp mem with same|tail
    · subst n;exact le_max_left _ _
    · exact (ih tail).trans (le_max_right _ _)

theorem powers_sum_bound (xs : List ℕ) :
    ((xs.map (fun e=>(2 : ℝ)^e)).sum)≤(xs.length : ℝ)*(2 : ℝ)^maximumExponent xs := by
  calc
    _≤((xs.map (fun _=>(2 : ℝ)^maximumExponent xs)).sum) := by
      apply List.sum_le_sum
      intro e mem
      exact pow_le_pow_right₀ (by norm_num) (maximumExponent_mem xs e mem)
    _=_ := by simp

theorem upperSum_bound (xs : List UpperExponent) :
    (xs.map exponentValue).sum≤ exponentValue (upperSum xs) := by
  have representation : (xs.map exponentValue).sum=
      ((xs.filterMap id).map (fun e=>(2 : ℝ)^e)).sum := by
    induction xs with
    | nil=>rfl
    | cons a xs ih=>cases a <;> simp [exponentValue,ih]
  rw [representation]
  unfold upperSum
  dsimp only
  split_ifs with zero
  · change ((xs.filterMap id).map (fun e=>(2 : ℝ)^e)).sum≤0
    rw [zero]
    simp
  · have positive : 0<(xs.filterMap id).length := by
      have nz : (xs.filterMap id).length≠0 := by
        intro empty
        exact zero (List.length_eq_zero_iff.mp empty)
      omega
    have count : ((xs.filterMap id).length : ℝ)≤(2 : ℝ)^Nat.size ((xs.filterMap id).length-1) := by
      exact_mod_cast nat_le_rounded_power _ positive
    calc
      _≤((xs.filterMap id).length : ℝ)*(2 : ℝ)^maximumExponent (xs.filterMap id) := powers_sum_bound _
      _≤(2 : ℝ)^Nat.size ((xs.filterMap id).length-1)*(2 : ℝ)^maximumExponent (xs.filterMap id) :=
        mul_le_mul_of_nonneg_right count (by positivity)
      _=exponentValue (some (maximumExponent (xs.filterMap id)+Nat.size ((xs.filterMap id).length-1))) := by
        simp only [exponentValue,←pow_add]
        congr 1
        omega

def productExponent (n j : ℕ) (a b : UpperExponent) : UpperExponent :=
  match a,b with
  | some e,some f=>some (e+f+Nat.size (n.choose j-1))
  | _,_=>none

def upperProduct (a b : UpperArray) (n : ℕ) : UpperExponent :=
  upperSum ((List.range (n+1)).map (fun j=>productExponent n j (a j) (b (n-j))))

theorem productExponent_bound (n j : ℕ) (a b : UpperExponent) :
    (n.choose j : ℝ)*exponentValue a*exponentValue b≤ exponentValue (productExponent n j a b) := by
  cases a with
  | none=>simp [exponentValue,productExponent]
  | some e=>cases b with
    | none=>simp [exponentValue,productExponent]
    | some f=>
      have bound : (n.choose j : ℝ)≤(2 : ℝ)^Nat.size (n.choose j-1) := by
        by_cases zero : n.choose j=0
        · simp [zero]
        · exact_mod_cast nat_le_rounded_power _ (Nat.pos_of_ne_zero zero)
      change (n.choose j : ℝ)*(2 : ℝ)^e*(2 : ℝ)^f≤(2 : ℝ)^(e+f+Nat.size (n.choose j-1))
      calc
        _≤(2 : ℝ)^Nat.size (n.choose j-1)*(2 : ℝ)^e*(2 : ℝ)^f := by gcongr
        _=_ := by simp only [←pow_add];congr 1;omega

theorem upperProduct_bound (a b : UpperArray) (n : ℕ) :
    productArray (fun m=>exponentValue (a m)) (fun m=>exponentValue (b m)) n≤
      exponentValue (upperProduct a b n) := by
  have bound : productArray (fun m=>exponentValue (a m)) (fun m=>exponentValue (b m)) n≤
      (((List.range (n+1)).map (fun j=>exponentValue (productExponent n j (a j) (b (n-j))))).sum) := by
    have same (N : ℕ) :
        (∑ j∈Finset.range N,(n.choose j : ℝ)*exponentValue (a j)*exponentValue (b (n-j)))=
        ((List.range N).map (fun j=>(n.choose j : ℝ)*exponentValue (a j)*exponentValue (b (n-j)))).sum := by
      induction N with
      | zero=>simp
      | succ N ih=>simp [Finset.sum_range_succ,List.range_succ,List.map_append,ih]
    rw [productArray,same]
    apply List.sum_le_sum
    intro j _
    exact productExponent_bound n j (a j) (b (n-j))
  exact bound.trans (by simpa only [upperProduct,List.map_map,Function.comp_def] using
    (upperSum_bound ((List.range (n+1)).map (fun j=>productExponent n j (a j) (b (n-j))))))

end LowEnergy.PreparationVacuumOriginalRadii
