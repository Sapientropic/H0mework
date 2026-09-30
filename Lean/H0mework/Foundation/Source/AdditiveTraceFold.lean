import Mathlib.Algebra.Group.Basic
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Additive readout of one rooted occurrence

An additive observation is not a second evaluator.  The semantic trace sum
is proved to be the unique fold of the sole occurrence constructor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootedAccountedUnfolding

universe u v

section

variable {Root : Type u} {Carrier : Type v} [AddMonoid Carrier]

def additiveFoldAlgebra (weight : Root → Carrier) :
    Root → List Carrier → Carrier :=
  fun root children => weight root + children.sum

noncomputable def traceSum (weight : Root → Carrier)
    (occurrence : RootedAccountedUnfolding Root) : Carrier :=
  (occurrence.trace.map weight).sum

private theorem traceBranches_sum_eq_candidateValues_sum
    (weight : Root → Carrier) :
    ∀ branches : AccountedBranches Root,
      ((traceBranches branches).map weight).sum =
        (candidateValues (traceSum weight) branches).sum
  | .nil => rfl
  | .cons head tail => by
      change
        (((head.trace ++ traceBranches tail).map weight).sum) =
          traceSum weight head +
            (candidateValues (traceSum weight) tail).sum
      rw [List.map_append, List.sum_append,
        traceBranches_sum_eq_candidateValues_sum weight tail]
      rfl

theorem traceSum_commutes (weight : Root → Carrier)
    (origin : Root) (branches : AccountedBranches Root) :
    traceSum weight (RootedAccountedUnfolding.occur origin branches) =
      additiveFoldAlgebra weight origin
        (candidateValues (traceSum weight) branches) := by
  change weight origin + ((traceBranches branches).map weight).sum =
    weight origin + (candidateValues (traceSum weight) branches).sum
  rw [traceBranches_sum_eq_candidateValues_sum]

/-- The trace sum is exactly the canonical fold, by `fold_unique`. -/
theorem traceSum_eq_fold (weight : Root → Carrier)
    (occurrence : RootedAccountedUnfolding Root) :
    traceSum weight occurrence =
      occurrence.fold (additiveFoldAlgebra weight) :=
  fold_unique (additiveFoldAlgebra weight) (traceSum weight)
    (traceSum_commutes weight) occurrence

end

end RootedAccountedUnfolding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
