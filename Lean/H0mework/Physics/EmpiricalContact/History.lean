import H0mework.Physics.EmpiricalContact.Inventory

/-! Original macro prefix followed by the uniquely generated contact epoch.
The epoch distinction is read from its genuine authority inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot

noncomputable section

inductive RuntimeState
  | prior (index : Fin 20)
  | continuation (index : Nat)

def priorState (index : Fin 20) : SpinPair.RuntimeState :=
  if historical : index.val < 7 then .history ⟨index.val, historical⟩ else .native (index.val - 7)

def runtimePresentation : RuntimeState → RootInquiryStatePresentation
  | .prior index => if index.val = 19 then inquiryPresentation else SpinPair.runtimePresentation (priorState index)
  | .continuation index => readPresentation (index + 1)

theorem prefix_erase (index : Fin 20) :
    (runtimePresentation (.prior index)).erase = (SpinPair.runtimePresentation (priorState index)).erase := by
  fin_cases index <;> rfl

private def oldRank : SpinPair.RuntimeState → Nat
  | .history index => index.val
  | .native index => index + 7

private theorem priorState_rank (index : Fin 20) : oldRank (priorState index) = index.val := by
  unfold priorState
  split
  · rfl
  · dsimp [oldRank]
    omega

private theorem priorState_injective : Function.Injective priorState := by
  intro left right equality
  have ranks := congrArg oldRank equality
  rw [priorState_rank, priorState_rank] at ranks
  exact Fin.ext ranks

private def inventoryCard (current : AnyAuthoritativeRootCurrent) : Nat :=
  Nat.card current.current.root.source.projectionLaw.Projection

private theorem old_inventory_distinct (state : SpinPair.RuntimeState) :
    inventoryCard (SpinPair.runtimePresentation state).erase ≠ 20 := by
  cases state with
  | history index =>
      fin_cases index
      all_goals first
        | change Nat.card RootProjectionCoordinate ≠ 20
          rw [original_inventory_card]
          decide
        | change Nat.card MaterialProjection ≠ 20
          rw [material_inventory_card]
          decide
  | native index =>
      rcases index with _ | _ | _ | index
      all_goals
        change Nat.card SpinPair.Projection ≠ 20
        rw [spinPair_inventory_card]
        decide

private theorem new_inventory (index : Nat) :
    inventoryCard (readPresentation (index + 1)).erase = 20 := empirical_inventory_card

private theorem visit_depth (index : Nat) : temporalDepth (visit index).history = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      dsimp only [visit]
      exact (temporalDepth_next (visit index).history _).trans (congrArg (· + 1) ih)

private theorem read_depth (index : Nat) :
    erasedDepth (readPresentation (index + 1)).erase = index + 1 := visit_depth (index + 1)

theorem runtimePresentation_erase_injective :
    Function.Injective (fun state => (runtimePresentation state).erase) := by
  intro left right equality
  change (runtimePresentation left).erase = (runtimePresentation right).erase at equality
  cases left with
  | prior i =>
      cases right with
      | prior j =>
          rw [prefix_erase, prefix_erase] at equality
          exact congrArg RuntimeState.prior
            (priorState_injective (SpinPair.runtimePresentation_erase_injective equality))
      | continuation j =>
          rw [prefix_erase] at equality
          exact False.elim (old_inventory_distinct (priorState i)
            ((congrArg inventoryCard equality).trans (new_inventory j)))
  | continuation i =>
      cases right with
      | prior j =>
          rw [prefix_erase] at equality
          exact False.elim (old_inventory_distinct (priorState j)
            ((congrArg inventoryCard equality.symm).trans (new_inventory i)))
      | continuation j =>
          have depths := congrArg erasedDepth equality
          change erasedDepth (readPresentation (i + 1)).erase =
            erasedDepth (readPresentation (j + 1)).erase at depths
          rw [read_depth, read_depth] at depths
          exact congrArg RuntimeState.continuation (Nat.add_right_cancel depths)

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
