import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Affine
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n m : ℕ}

def serviceValues (values : Fin (n + m) → ℚ) : Fin n → ℚ :=
  fun i => values (i.castAdd m)

def addCoordinates (form : Affine n) (m : ℕ) : Affine (n + m) :=
  ⟨Fin.append form.coeff (fun _ => 0), form.constant⟩

@[simp] theorem eval_addCoordinates (form : Affine n) (values : Fin (n + m) → ℚ) :
    (addCoordinates form m).eval values = form.eval (serviceValues values) := by
  simp [addCoordinates, Affine.eval, dot, Fin.sum_univ_add, serviceValues]

def extendRow (row : Inequality n) (m : ℕ) : Inequality (n + m) :=
  ⟨Fin.append row.coeff (fun _ => 0), row.bound⟩

@[simp] theorem extendRow_exact (row : Inequality n) (values : Fin (n + m) → ℚ) :
    (extendRow row m).Holds values ↔ row.Holds (serviceValues values) := by
  simp [extendRow, Inequality.Holds, dot, Fin.sum_univ_add, serviceValues]

variable {Address : Type*} [DecidableEq Address]

abbrev AddressOf (keys : List Address) := {key // key ∈ keys}

def addressIndex (keys : List Address) (distinct : keys.Nodup) : AddressOf keys ≃ Fin keys.length :=
  (List.Nodup.getEquiv keys distinct).symm

def extraAt (keys : List Address) (distinct : keys.Nodup)
    (values : Fin (n + keys.length) → ℚ) (key : Address) : ℚ :=
  if listed : key ∈ keys then values ((addressIndex keys distinct ⟨key, listed⟩).natAdd n) else 0

def extraForm (keys : List Address) (distinct : keys.Nodup) (n : ℕ)
    (key : Address) : Affine (n + keys.length) :=
  if listed : key ∈ keys then Affine.variableAt ((addressIndex keys distinct ⟨key, listed⟩).natAdd n)
  else Affine.literal 0

@[simp] theorem extraForm_exact (keys : List Address) (distinct : keys.Nodup)
    (values : Fin (n + keys.length) → ℚ) (key : Address) :
    (extraForm keys distinct n key).eval values = extraAt keys distinct values key := by
  unfold extraForm extraAt
  split <;> simp_all

theorem extraAt_unlisted (keys : List Address) (distinct : keys.Nodup)
    (values : Fin (n + keys.length) → ℚ) (key : Address) (outside : key ∉ keys) :
    extraAt keys distinct values key = 0 := by
  simp [extraAt, outside]

def join (keys : List Address) (distinct : keys.Nodup)
    (service : Fin n → ℚ) (extra : Address → ℚ) : Fin (n + keys.length) → ℚ :=
  Fin.append service (fun i => extra ((addressIndex keys distinct).symm i).val)

@[simp] theorem serviceValues_join (keys : List Address) (distinct : keys.Nodup)
    (service : Fin n → ℚ) (extra : Address → ℚ) :
    serviceValues (join keys distinct service extra) = service := by
  funext i
  simp [serviceValues, join]

@[simp] theorem extraAt_join (keys : List Address) (distinct : keys.Nodup)
    (service : Fin n → ℚ) (extra : Address → ℚ)
    (outside : ∀ key ∉ keys, extra key = 0) :
    extraAt keys distinct (join keys distinct service extra) = extra := by
  funext key
  by_cases listed : key ∈ keys
  · simp [extraAt, join, listed]
  · simp [extraAt, listed, outside key listed]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
