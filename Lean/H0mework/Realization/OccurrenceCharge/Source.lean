import H0mework.Realization.OccurrenceCharge.Action
import H0mework.Realization.OccurrenceCharge.Fold

/-! The closed action is derived from the old occurrence's full frontier and actual source charges. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceAccountedAction

open SourceOwnedObservationHistory

noncomputable section
universe u
variable {State Account : Type u} [AddCommGroup Account]

def frontierWord (material : RootedAccountedUnfolding State) : Carrier State :=
  (material.frontier.map sourcePoint).sum

def retained (charge : State → Account) (material : RootedAccountedUnfolding State) : Carrier State × Account :=
  (frontierWord material, RootedAccountedUnfolding.SourceCharge.tally charge material)

theorem frontier_action (step : State → State) (material : RootedAccountedUnfolding State) :
    sourceAction step (frontierWord material) =
      frontierWord (material.advance (fun state => .zero (step state))) := by
  simp only [frontierWord, RootedAccountedUnfolding.frontier_advance]
  have mapped : ∀ roots : List State,
      sourceAction step (roots.map sourcePoint).sum =
        ((roots.flatMap (fun state => (RootedAccountedUnfolding.zero (step state)).frontier)).map sourcePoint).sum := by
    intro roots
    induction roots with
    | nil => simp
    | cons head tail induction =>
        change sourceAction step (sourcePoint head + _) = sourcePoint (step head) + _
        rw [map_add, sourceAction_point]
        exact congrArg (sourcePoint (step head) + ·) induction
  exact mapped material.frontier

theorem frontier_charge (charge : State → Account) (material : RootedAccountedUnfolding State) :
    observation charge (frontierWord material) = (material.frontier.map charge).sum := by
  have mapped : ∀ roots : List State,
      observation charge (roots.map sourcePoint).sum = (roots.map charge).sum := by
    intro roots
    induction roots with
    | nil => simp
    | cons head tail induction =>
        simp only [List.map_cons, List.sum_cons, map_add, observation_point, induction]
  exact mapped material.frontier

theorem retained_advance (step : State → State) (charge : State → Account)
    (material : RootedAccountedUnfolding State) :
    update step charge (retained charge material) =
      retained charge (material.advance (fun state => .zero (step state))) := by
  apply Prod.ext
  · exact frontier_action step material
  · change RootedAccountedUnfolding.SourceCharge.tally charge material +
      observation charge (frontierWord material) =
        RootedAccountedUnfolding.SourceCharge.tally charge
          (material.advance (fun state => .zero (step state)))
    rw [frontier_charge, RootedAccountedUnfolding.SourceCharge.advance]

end
end SourceAccountedAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
