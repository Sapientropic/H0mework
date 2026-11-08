import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Slack
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Consumers

open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

private def service : Network Unit Unit where
  need := fun _ => 2
  capacity := fun _ => 1
  allows := fun _ _ => true
  need_nonnegative := by intro; decide
  capacity_nonnegative := by intro; decide

private def coordinate : Unit × Unit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by
    intro position
    apply Fin.ext
    have within := position.isLt
    omega

def debitSlack : Option (ℕ × ℚ × ℚ) :=
  match diagnose (serviceTagged service (fun _ => true) coordinate [()] [()]) with
  | .feasible _ _ => none
  | .blocked failure =>
      match failure.label with
      | .originalDebit () =>
          let amount := failure.minimumSlack
          some (failure.position.val, amount.amount, amount.allocation 0)
      | _ => none

/-- The earlier original demand remains two. The original debit ceiling
is one, and a unit increase is necessary and sufficient for this prefix. -/
theorem the_original_debit_ceiling_needs_one_more_unit :
    debitSlack = some (3, 1, 2) := by
  decide +kernel

private def openPrefix : List (Tagged String 1) :=
  [⟨"prior floor", ⟨fun _ => -1, -1⟩⟩, ⟨"prior ceiling", ⟨fun _ => 1, 2⟩⟩,
    ⟨"new floor", ⟨fun _ => -1, -3⟩⟩]

def compareWithEarlierWitness : Option (ℚ × ℚ × ℚ) :=
  match diagnose openPrefix with
  | .feasible _ _ => none
  | .blocked failure =>
      let minimum := failure.minimumSlack
      some (failure.violation failure.witness, minimum.amount, minimum.allocation 0)

theorem optimizing_the_original_prefix_can_reduce_the_witness_gap :
    compareWithEarlierWitness = some (2, 1, 2) := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Consumers
