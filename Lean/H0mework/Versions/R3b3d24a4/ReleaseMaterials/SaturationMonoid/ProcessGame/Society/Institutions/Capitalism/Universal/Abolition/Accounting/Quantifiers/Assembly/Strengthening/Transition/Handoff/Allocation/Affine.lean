import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open scoped BigOperators
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n : ℕ}

structure Affine (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ

namespace Affine

def eval (form : Affine n) (values : Fin n → ℚ) : ℚ :=
  form.constant + dot form.coeff values

def literal (amount : ℚ) : Affine n := ⟨fun _ => 0, amount⟩

def variableAt (i : Fin n) : Affine n := ⟨fun j => if i = j then 1 else 0, 0⟩

def add (left right : Affine n) : Affine n :=
  ⟨fun i => left.coeff i + right.coeff i, left.constant + right.constant⟩

def sub (left right : Affine n) : Affine n :=
  ⟨fun i => left.coeff i - right.coeff i, left.constant - right.constant⟩

def sum : List (Affine n) → Affine n
  | [] => literal 0
  | first :: rest => add first (sum rest)

def sumOver {Index : Type*} [Fintype Index] (terms : Index → Affine n) : Affine n :=
  ⟨fun i => ∑ k, (terms k).coeff i, ∑ k, (terms k).constant⟩

def le (left right : Affine n) : Inequality n :=
  ⟨(sub left right).coeff, right.constant - left.constant⟩

def lift (form : Affine n) : Affine (n + 1) :=
  ⟨Fin.snoc form.coeff 0, form.constant⟩

@[simp] theorem eval_lift (form : Affine n) (values : Fin (n + 1) → ℚ) :
    form.lift.eval values = form.eval (Fin.init values) := by
  simp [lift, eval, dot, Fin.sum_univ_castSucc, Fin.init]

@[simp] theorem eval_literal (amount : ℚ) (values : Fin n → ℚ) :
    (literal amount).eval values = amount := by simp [literal, eval, dot]

@[simp] theorem eval_variableAt (i : Fin n) (values : Fin n → ℚ) :
    (variableAt i).eval values = values i := by
  simp [eval, variableAt, dot, ite_mul]

@[simp] theorem eval_add (left right : Affine n) (values : Fin n → ℚ) :
    (add left right).eval values = left.eval values + right.eval values := by
  simp only [add, eval, dot, add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem eval_sub (left right : Affine n) (values : Fin n → ℚ) :
    (sub left right).eval values = left.eval values - right.eval values := by
  simp only [sub, eval, dot, sub_mul, Finset.sum_sub_distrib]
  ring

@[simp] theorem eval_sum (terms : List (Affine n)) (values : Fin n → ℚ) :
    (sum terms).eval values = (terms.map (fun term => term.eval values)).sum := by
  induction terms with
  | nil => simp [sum]
  | cons first rest ih => simp [sum, ih]

@[simp] theorem eval_sumOver {Index : Type*} [Fintype Index]
    (terms : Index → Affine n) (values : Fin n → ℚ) :
    (sumOver terms).eval values = ∑ k, (terms k).eval values := by
  simp only [sumOver, eval, dot, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (i : Fin n) (k : Index) => (terms k).coeff i * values i)]

@[simp] theorem holds_le (left right : Affine n) (values : Fin n → ℚ) :
    (le left right).Holds values ↔ left.eval values ≤ right.eval values := by
  simp only [le, sub, eval, Inequality.Holds, dot, sub_mul, Finset.sum_sub_distrib]
  constructor <;> intro bound <;> linarith only [bound]

end Affine

def liftInequality (row : Inequality n) : Inequality (n + 1) :=
  ⟨Fin.snoc row.coeff 0, row.bound⟩

@[simp] theorem liftInequality_exact (row : Inequality n) (values : Fin (n + 1) → ℚ) :
    (liftInequality row).Holds values ↔ row.Holds (Fin.init values) := by
  simp [liftInequality, Inequality.Holds, dot, Fin.sum_univ_castSucc, Fin.init]

theorem feasible_cons (first : Inequality n) (rest : List (Inequality n)) (values : Fin n → ℚ) :
    Feasible (first :: rest) values ↔ first.Holds values ∧ Feasible rest values := by
  simp [Feasible]

@[simp] theorem feasible_nil (values : Fin n → ℚ) : Feasible [] values := by simp [Feasible]

theorem feasible_append (left right : List (Inequality n)) (values : Fin n → ℚ) :
    Feasible (left ++ right) values ↔ Feasible left values ∧ Feasible right values := by
  simp only [Feasible, List.mem_append]
  exact ⟨fun fits => ⟨fun row h => fits row (.inl h), fun row h => fits row (.inr h)⟩,
    fun fits row h => h.elim (fits.1 row) (fits.2 row)⟩

theorem feasible_map {Index : Type*} (rows : List Index) (make : Index → Inequality n) (values : Fin n → ℚ) :
    Feasible (rows.map make) values ↔ ∀ row ∈ rows, (make row).Holds values := by
  constructor
  · exact fun fits row found => fits _ (List.mem_map.mpr ⟨row, found, rfl⟩)
  · intro fits _ found
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp found
    exact fits row present

theorem feasible_flatMap {Index : Type*} (rows : List Index) (make : Index → List (Inequality n))
    (values : Fin n → ℚ) :
    Feasible (rows.flatMap make) values ↔ ∀ row ∈ rows, Feasible (make row) values := by
  constructor
  · exact fun fits row found condition included => fits condition (List.mem_flatMap.mpr ⟨row, found, included⟩)
  · intro fits _ found
    obtain ⟨row, present, included⟩ := List.mem_flatMap.mp found
    exact fits row present _ included

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
