import H0mework.Probability.MassCompletion.Action

/-! The complete original integer source word enters the joint carrier with both coordinates intact. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory SourceSuccessorBoundary

noncomputable section

def nativeRead : Carrier Nat →ₗ[ℤ] Joint :=
  Finsupp.linearCombination ℤ fun state => jointRead (Finsupp.single state (1 : ℂ))

theorem nativeRead_point (state : Nat) : nativeRead (sourcePoint state) = jointRead (Finsupp.single state 1) := by
  simp only [nativeRead, sourcePoint, Finsupp.linearCombination_single, one_smul]

theorem firstRead_native (word : Carrier Nat) : firstRead (nativeRead word) = SourceShift.wordRead word := by
  change (firstRead.toLinearMap.restrictScalars ℤ)
    (Finsupp.linearCombination ℤ (fun state => jointRead (Finsupp.single state (1 : ℂ))) word) = _
  rw [Finsupp.apply_linearCombination]
  change Finsupp.linearCombination ℤ (fun state => firstRead (jointRead (Finsupp.single state 1))) word = _
  simp only [firstRead_source, readWord_single, one_smul]
  rfl

theorem massRead_native (word : Carrier Nat) : massRead (nativeRead word) = (mass ℤ word : ℂ) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add state scalar word notMem nonzero inductionHypothesis =>
      simp only [map_add, Int.cast_add, inductionHypothesis]
      congr 1
      simp [nativeRead, massRead_source, mass_single]

theorem nativeRead_injective : Function.Injective nativeRead := by
  intro left right equality
  apply SourceShift.wordRead_injective
  exact (firstRead_native left).symm.trans ((congrArg firstRead equality).trans (firstRead_native right))

theorem action_native (word : Carrier Nat) :
    nativeRead (sourceAction Nat.succ word) = action (nativeRead word) := by
  change Finsupp.linearCombination ℤ (fun state => jointRead (Finsupp.single state (1 : ℂ)))
      (Finsupp.mapDomain Nat.succ word) =
    (action.toLinearMap.restrictScalars ℤ)
      (Finsupp.linearCombination ℤ (fun state => jointRead (Finsupp.single state (1 : ℂ))) word)
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  congr 1
  apply congrArg (Finsupp.linearCombination ℤ)
  funext state
  change jointRead (Finsupp.single (state + 1) (1 : ℂ)) = action (jointRead (Finsupp.single state 1))
  rw [action_source]
  simp [push]

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
