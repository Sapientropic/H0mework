import Mathlib.Order.WellFounded
import H0mework.Foundation.Finite.BranchingReachability

/-!
# Minimal closed strongly connected subsector

This kernel does not rerun finite reachability.  It consumes an existing exact
`ClosedReachabilityResidualAt`, selects a minimum-cardinality nonempty subset
closed under every actual channel, and proves it is strongly connected using
the already generated dependent paths.

For any member `x`, the exact states reachable from `x` form another nonempty
closed subsector.  They are contained in the selected minimum sector, while
cardinality minimality forces equality.  Hence every pair of sector states is
connected by an actual `GeneratedPathAt`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFiniteClosedReachableMinimalSCC

open SourceGeneratedFiniteEffectiveBranchingReachability

universe u

variable {State : Type u} [Fintype State] {law : Law State}
  {start : State}

structure ClosedSubsectorAt
    (residual : ClosedReachabilityResidualAt law start) : Type u where
  states : Finset State
  nonempty : states.Nonempty
  subsetResidual : states ⊆ residual.states
  stepClosed : ∀ state, state ∈ states → (step : law.StepAt state) →
    law.target step ∈ states

def wholeClosedSubsector
    (residual : ClosedReachabilityResidualAt law start) :
    ClosedSubsectorAt residual where
  states := residual.states
  nonempty := ⟨start, residual.startMem⟩
  subsetResidual := fun _state stateMem => stateMem
  stepClosed := residual.stepClosed

instance closedSubsectorNonempty
    (residual : ClosedReachabilityResidualAt law start) :
    Nonempty (ClosedSubsectorAt residual) :=
  ⟨wholeClosedSubsector residual⟩

noncomputable def generateMinimalClosedSubsector
    (residual : ClosedReachabilityResidualAt law start) :
    ClosedSubsectorAt residual :=
  Function.argmin fun sector : ClosedSubsectorAt residual =>
    sector.states.card

theorem minimalClosedSubsector_card_le
    (residual : ClosedReachabilityResidualAt law start)
    (sector : ClosedSubsectorAt residual) :
    (generateMinimalClosedSubsector residual).states.card ≤
      sector.states.card :=
  by
    unfold generateMinimalClosedSubsector
    exact Function.argmin_le
      (fun candidate : ClosedSubsectorAt residual => candidate.states.card)
      sector

theorem GeneratedPathAt.end_mem_of_closedSubsector
    {residual : ClosedReachabilityResidualAt law start}
    (sector : ClosedSubsectorAt residual)
    {source target : State} (sourceMem : source ∈ sector.states)
    (path : GeneratedPathAt law source target) :
    target ∈ sector.states := by
  induction path with
  | nil => exact sourceMem
  | snoc prior step inductionHypothesis =>
      exact sector.stepClosed _ inductionHypothesis step

noncomputable def reachableClosedSubsectorFrom
    (residual : ClosedReachabilityResidualAt law start)
    (sector : ClosedSubsectorAt residual)
    (source : State) (sourceMem : source ∈ sector.states) :
    ClosedSubsectorAt residual where
  states := reachableSet law source
  nonempty := ⟨source, start_mem_reachableSet law source⟩
  subsetResidual := by
    intro state stateMem
    have pathNonempty := (mem_reachableSet_iff law source state).mp stateMem
    exact sector.subsetResidual
      (GeneratedPathAt.end_mem_of_closedSubsector sector sourceMem
        (Classical.choice pathNonempty))
  stepClosed := by
    intro state stateMem step
    exact target_mem_reachableSet law source state stateMem step

structure MinimalClosedSCCAt
    (residual : ClosedReachabilityResidualAt law start) : Type u where
  private mk ::
  sector : ClosedSubsectorAt residual
  sector_eq : sector = generateMinimalClosedSubsector residual
  pathBetween : ∀ source, source ∈ sector.states →
    ∀ target, target ∈ sector.states →
      GeneratedPathAt law source target

noncomputable def generateMinimalClosedSCC
    (residual : ClosedReachabilityResidualAt law start) :
    MinimalClosedSCCAt residual := by
  let sector := generateMinimalClosedSubsector residual
  have pathBetween : ∀ source, source ∈ sector.states →
      ∀ target, target ∈ sector.states →
        GeneratedPathAt law source target := by
    intro source sourceMem target targetMem
    let reachable := reachableClosedSubsectorFrom
      residual sector source sourceMem
    have reachableSubset : reachable.states ⊆ sector.states := by
      intro state stateMem
      have pathNonempty := (mem_reachableSet_iff law source state).mp stateMem
      exact GeneratedPathAt.end_mem_of_closedSubsector sector sourceMem
        (Classical.choice pathNonempty)
    have sectorCardLe : sector.states.card ≤ reachable.states.card :=
      minimalClosedSubsector_card_le residual reachable
    have reachableEq : reachable.states = sector.states :=
      Finset.eq_of_subset_of_card_le reachableSubset sectorCardLe
    have targetReachable : target ∈ reachableSet law source := by
      change target ∈ reachable.states
      rw [reachableEq]
      exact targetMem
    exact Classical.choice
      ((mem_reachableSet_iff law source target).mp targetReachable)
  exact ⟨sector, rfl, pathBetween⟩

end SourceGeneratedFiniteClosedReachableMinimalSCC
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
