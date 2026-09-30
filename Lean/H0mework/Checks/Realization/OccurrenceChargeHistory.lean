import H0mework.Realization.OccurrenceCharge.Model

/-! A closed observation Model need not identify the original history; actual charges still distinguish growth. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceAccountedAction.Regression

open SourceOwnedObservationHistory SourceGeneratedActionObservationHistory

noncomputable section

def first : RootedAccountedUnfolding Nat := .zero 0
def later : RootedAccountedUnfolding Nat := occurrenceUpdate id first

theorem same_zero_charge_read :
    retained (fun _ : Nat => (0 : ℤ)) first = retained (fun _ : Nat => (0 : ℤ)) later := by
  simp [retained, frontierWord, first, later, occurrenceUpdate, RootedAccountedUnfolding.zero,
    RootedAccountedUnfolding.advance, AccountedBranches.singleton, RootedAccountedUnfolding.frontier,
    RootedAccountedUnfolding.SourceCharge.tally, RootedAccountedUnfolding.fold,
    RootedAccountedUnfolding.foldBranches, RootedAccountedUnfolding.SourceCharge.atSource]

theorem different_original_histories : first ≠ later := by
  intro same
  have trace := congrArg (fun tree => tree.trace.length) same
  change 1 = 2 at trace
  omega

theorem same_generated_model :
    projection (sourceAction (occurrenceUpdate (id : Nat → Nat)))
      (observation (retained (fun _ : Nat => (0 : ℤ)))) (sourcePoint first) =
    projection (sourceAction (occurrenceUpdate (id : Nat → Nat)))
      (observation (retained (fun _ : Nat => (0 : ℤ)))) (sourcePoint later) :=
  (model_point_fibre id _ first later).mpr same_zero_charge_read

theorem nonzero_charge_separates :
    projection (sourceAction (occurrenceUpdate (id : Nat → Nat)))
      (observation (retained (fun _ : Nat => (1 : ℤ)))) (sourcePoint first) ≠
    projection (sourceAction (occurrenceUpdate (id : Nat → Nat)))
      (observation (retained (fun _ : Nat => (1 : ℤ)))) (sourcePoint later) := by
  rw [ne_eq, model_point_fibre]
  intro same
  have account := congrArg Prod.snd same
  change (0 : ℤ) = 1 + 0 at account
  omega

end
end SourceAccountedAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
