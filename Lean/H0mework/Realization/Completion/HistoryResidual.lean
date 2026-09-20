import H0mework.Realization.Completion.HistorySettlement

/-!
# Explicit coordinates for a persistent presented residual

The cofinal-history settlement classifier has a total negative branch, but a
bare predicate `∀ stage, ¬ CompactAt stage` is not yet a usable residual
coordinate.  This kernel turns that generated obstruction into a concrete
finite observation: a nonzero quotient class and a representative in the
complete presented carrier which is outside the stage presentation range.

The coordinate is extracted from the same history obstruction.  No stage,
pair, representative, finite envelope or branch is accepted from a caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryResidualCoordinate

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt

noncomputable section

universe u w

/-- One explicit finite coordinate of a presented residual. -/
structure GeneratedPresentedResidualCoordinateAt
    {Root : Type w} {Generator : Type u}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) : Type (max u w) where
  private mk ::
  stage : Nat
  coordinate : history.PresentedResidual stage
  coordinate_ne : coordinate ≠ 0
  representative : history.CompletionCarrier
  representative_class :
    (Submodule.Quotient.mk representative : history.PresentedResidual stage) =
      coordinate
  representative_not_mem_range :
    representative ∉
      LinearMap.range (history.stagePresentedToCompletion stage)

namespace GeneratedPresentedResidualCoordinateAt

variable {Root : Type w} {Generator : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history : RootGeneratedCofinalHistoryAt rootOccurrence
  seedOccurrence continuationOccurrence}

theorem coordinate_ne_zero
    (coordinate : GeneratedPresentedResidualCoordinateAt history) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne

theorem representative_outside_source_range
    (coordinate : GeneratedPresentedResidualCoordinateAt history) :
    coordinate.representative ∉
      LinearMap.range
        (history.stagePresentedToCompletion coordinate.stage) :=
  coordinate.representative_not_mem_range

end GeneratedPresentedResidualCoordinateAt

/-- A persistent obstruction yields a nonzero finite coordinate at stage zero.
The first stage is sufficient because persistence says its presented residual
is already non-subsingleton. -/
noncomputable def persistentCoordinate
    {Root : Type w} {Generator : Type u}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    {history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence}
    (obstruction : PersistentPresentedResidualObstructionAt history) :
    GeneratedPresentedResidualCoordinateAt history := by
  classical
  have notSubsingleton : ¬ Subsingleton (history.PresentedResidual 0) :=
    obstruction.residualPersists 0
  letI : Nontrivial (history.PresentedResidual 0) :=
    not_subsingleton_iff_nontrivial.mp notSubsingleton
  let pairWitness := exists_pair_ne (history.PresentedResidual 0)
  let left := Classical.choose pairWitness
  let right := Classical.choose (Classical.choose_spec pairWitness)
  have distinct : left ≠ right :=
    Classical.choose_spec (Classical.choose_spec pairWitness)
  let coordinate : history.PresentedResidual 0 := left - right
  have coordinate_ne : coordinate ≠ 0 := sub_ne_zero.mpr distinct
  let rangeSubmodule : Submodule ℤ history.CompletionCarrier :=
    LinearMap.range (history.stagePresentedToCompletion 0)
  let representative : history.CompletionCarrier :=
    Classical.choose (Submodule.Quotient.mk_surjective
      rangeSubmodule coordinate)
  have representative_class :
      (Submodule.Quotient.mk representative : history.PresentedResidual 0) =
        coordinate :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective
      rangeSubmodule coordinate)
  have representative_not_mem_range : representative ∉ rangeSubmodule := by
    intro rangeMembership
    have representative_zero :
        (Submodule.Quotient.mk representative : history.PresentedResidual 0) =
          0 :=
      (Submodule.Quotient.mk_eq_zero _).2 rangeMembership
    exact coordinate_ne (representative_class.symm.trans representative_zero)
  exact ⟨0, coordinate, coordinate_ne, representative,
    representative_class, representative_not_mem_range⟩

theorem persistent_coordinate_is_nonzero
    {Root : Type w} {Generator : Type u}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    {history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence}
    (obstruction : PersistentPresentedResidualObstructionAt history) :
    ((persistentCoordinate obstruction).coordinate ≠ 0) ∧
      (persistentCoordinate obstruction).representative ∉
        LinearMap.range
          (history.stagePresentedToCompletion
            (persistentCoordinate obstruction).stage) :=
  ⟨(persistentCoordinate obstruction).coordinate_ne,
    (persistentCoordinate obstruction).representative_not_mem_range⟩

end
end CofinalHistoryResidualCoordinate
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
