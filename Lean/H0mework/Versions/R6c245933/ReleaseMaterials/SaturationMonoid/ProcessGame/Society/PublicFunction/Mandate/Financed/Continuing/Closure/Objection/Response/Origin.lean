import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) (word : List Action)

theorem common_items (ordinal : Nat) (inside : ordinal < cut.depth + 2) :
    Registered.traceItems (I fuel (branchInputs cut word)) (ProgrammeHistory.visitAt (I fuel (branchInputs cut word)) ordinal).current =
      Registered.traceItems (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) ordinal).current := by
  cases ordinal with
  | zero => rfl
  | succ birth => exact common_prefix_keeps_each_financial_instruction cut word ⟨birth, by omega⟩

def position (original : Position fuel inputs) (inside : original.ordinal < cut.depth + 2) : Position fuel (branchInputs cut word) :=
  ⟨original.ordinal, ⟨original.index.val, by rw [common_items cut word original.ordinal inside]; exact original.index.isLt⟩⟩

theorem position_same_item (original : Position fuel inputs) (inside : original.ordinal < cut.depth + 2) :
    (position cut word original inside).item fuel (branchInputs cut word) = original.item fuel inputs := by
  have same := congrArg (fun items => items[original.index.val]?) (common_items cut word original.ordinal inside)
  have bound : original.index.val < (Registered.traceItems (I fuel (branchInputs cut word))
      (ProgrammeHistory.visitAt (I fuel (branchInputs cut word)) original.ordinal).current).length :=
    (position cut word original inside).index.isLt
  rw [List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem original.index.isLt] at same
  exact Option.some.inj same

def replacement (original : Claim fuel inputs) (inside : original.position.ordinal < cut.depth + 2) :
    Claim fuel (branchInputs cut word) :=
  let target := position cut word original.position inside
  have found : (read fuel (branchInputs cut word) target).isSome = true := by
    unfold read
    have signed : isSubmission (target.item fuel (branchInputs cut word)).request = true := by
      rw [position_same_item cut word original.position inside, original.signed]
      exact (isSubmission_iff _).mpr rfl
    have active : (target.item fuel (branchInputs cut word)).before.technology.holder.isSome = true ∨
        (target.item fuel (branchInputs cut word)).before.technology.offered.isSome = true := by
      rw [position_same_item cut word original.position inside]
      exact original.active
    rw [dif_pos signed, dif_pos active]
    rfl
  (read fuel (branchInputs cut word) target).get found

theorem replacement_is_actually_read (original : Claim fuel inputs) (inside : original.position.ordinal < cut.depth + 2) :
    read fuel (branchInputs cut word) (position cut word original.position inside) = some (replacement cut word original inside) := by
  exact (Option.some_get _).symm

theorem read_position (position : Position fuel inputs) (claim : Claim fuel inputs)
    (decoded : read fuel inputs position = some claim) : claim.position = position := by
  unfold read at decoded
  split at decoded
  · split at decoded
    · cases Option.some.inj decoded; rfl
    · cases decoded
  · cases decoded

theorem replacement_position (original : Claim fuel inputs) (inside : original.position.ordinal < cut.depth + 2) :
    (replacement cut word original inside).position = position cut word original.position inside :=
  read_position _ _ (replacement_is_actually_read cut word original inside)

theorem replacement_preserves_original_item_and_snapshot (original : Claim fuel inputs)
    (inside : original.position.ordinal < cut.depth + 2) :
    ((replacement cut word original inside).position.item fuel (branchInputs cut word)) = original.position.item fuel inputs ∧
    (replacement cut word original inside).snapshot fuel (branchInputs cut word) = original.snapshot fuel inputs ∧
    (replacement cut word original inside).position.ordinal = original.position.ordinal ∧
    (replacement cut word original inside).position.index.val = original.position.index.val := by
  unfold Claim.snapshot
  rw [replacement_position]
  exact ⟨position_same_item cut word original.position inside,
    congrArg (fun item => item.before.technology) (position_same_item cut word original.position inside), rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response
