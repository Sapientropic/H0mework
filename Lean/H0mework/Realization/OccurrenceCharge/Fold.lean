import H0mework.Foundation.Source.AccountedUnfolding
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Additive charges are read from the original occurrence and its newly advanced frontier. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootedAccountedUnfolding.SourceCharge

universe u v
variable {Root : Type u} {Value : Type v} [AddCommMonoid Value]

def atSource (charge : Root → Value) (root : Root) : List Value → Value
  | [] => 0
  | head :: tail => charge root + (head :: tail).sum

def tally (charge : Root → Value) (occurrence : RootedAccountedUnfolding Root) : Value :=
  occurrence.fold (atSource charge)

theorem advance (charge : Root → Value) (step : Root → Root) (occurrence : RootedAccountedUnfolding Root) :
    tally charge (occurrence.advance (fun root => .zero (step root))) =
      tally charge occurrence + (occurrence.frontier.map charge).sum :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun tree => tally charge (tree.advance (fun root => .zero (step root))) =
      tally charge tree + (tree.frontier.map charge).sum)
    (motive_2 := fun branches =>
      (foldBranches (atSource charge) (advanceBranches (fun root => .zero (step root)) branches)).sum =
        (foldBranches (atSource charge) branches).sum + ((frontierBranches branches).map charge).sum)
    (fun origin branches branchResult => by
      cases branches with
      | nil => simp [tally, RootedAccountedUnfolding.advance, zero, AccountedBranches.singleton,
          fold, foldBranches, atSource, frontier]
      | cons head tail =>
          exact (congrArg (fun value => charge origin + value) branchResult).trans
            (add_assoc _ _ _).symm)
    (by simp [advanceBranches, foldBranches, frontierBranches])
    (fun head tail headResult tailResult => by
      change tally charge (head.advance _) +
          (foldBranches (atSource charge) (advanceBranches _ tail)).sum =
        (tally charge head + (foldBranches (atSource charge) tail).sum) +
          ((head.frontier ++ frontierBranches tail).map charge).sum
      rw [headResult, tailResult, List.map_append, List.sum_append]
      ac_rfl)
    occurrence

end RootedAccountedUnfolding.SourceCharge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
