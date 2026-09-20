import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
Lean 4.33.0 and mathlib v4.33.0 disagree in the optimized enum `Fintype`
deriver.  This marker routes enum declarations through mathlib's constructive
proxy deriver until the paired upstream release is repaired.
-/

class FintypeViaProxy (α : Type u) : Prop where

open Lean Elab Command

private def deriveFintypeViaProxy (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  Mathlib.Deriving.Fintype.mkFintype declNames[0]!

initialize
  registerDerivingHandler ``FintypeViaProxy deriveFintypeViaProxy
