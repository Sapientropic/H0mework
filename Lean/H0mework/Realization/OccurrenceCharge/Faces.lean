import H0mework.Realization.OccurrenceCharge.Fold
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Every additive face restricts the same source-charge fold. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootedAccountedUnfolding.SourceCharge

noncomputable section
universe u v w
variable {Root : Type u} {Value : Type v} {Face : Type w} [AddCommMonoid Value] [AddCommMonoid Face]

theorem face_tally (face : Value →+ Face) (charge : Root → Value) (material : RootedAccountedUnfolding Root) :
    face (tally charge material) = tally (face ∘ charge) material :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun tree => face (tally charge tree) = tally (face ∘ charge) tree)
    (motive_2 := fun branches =>
      face (foldBranches (atSource charge) branches).sum = (foldBranches (atSource (face ∘ charge)) branches).sum)
    (fun root branches branchResult => by
      cases branches with
      | nil => exact _root_.map_zero face
      | cons head tail =>
          exact (map_add face (charge root) _).trans (congrArg (face (charge root) + ·) branchResult))
    (_root_.map_zero face)
    (fun head tail headResult tailResult => by
      exact (map_add face _ _).trans (congrArg₂ (· + ·) headResult tailResult))
    material

end
end RootedAccountedUnfolding.SourceCharge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
