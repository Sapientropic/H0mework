import H0mework.Fock.HistoryCopy.ObservationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceConditionalInventory SourceUniformFibreVariance SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped Classical
noncomputable section

local instance snapshotParentMeasurable : MeasurableSpace ParentCarrier := ⊤
local instance snapshotFieldMeasurable : MeasurableSpace IntegralOneParticle := ⊤

private theorem state_injective : Function.Injective secondQuantizedState := by
  intro left right same
  have projected := congrArg thetaProjection same
  simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion] at projected
  change left + 0 = right + 0 at projected
  exact add_right_cancel projected

theorem before_cost (depth bound : Nat) :
    cost bound (before depth bound) = SourceGeneratedConditionalInventory.snapshotCost bound := by
  have same : outputs bound (before depth bound) =
      (outputs bound (fun actor => rawField actor.val)).image secondQuantizedState := by
    unfold outputs
    rw [Finset.image_image]
    exact congrArg (fun query : Fin (bound + 1) → ParentCarrier => Finset.image query Finset.univ)
      (funext (before_source depth bound))
  rw [cost_eq, SourceGeneratedConditionalInventory.snapshotCost, cost_eq, same,
    Finset.card_image_of_injective _ state_injective]

theorem before_cost_three (depth : Nat) : cost 3 (before depth 3) = 1 := by
  have base : SourceGeneratedConditionalInventory.snapshotCost 0 = 0 :=
    exact_inventory 0 _ (fun left right _ => (Fin.eq_zero left).trans (Fin.eq_zero right).symm)
  rw [before_cost, SourceGeneratedConditionalInventory.actual_cost_step 2,
    SourceGeneratedConditionalInventory.actual_cost_step 1, SourceGeneratedConditionalInventory.actual_cost_step 0, base]
  norm_num [show Nat.Prime 5 by decide, show Nat.Prime 7 by decide, show ¬ Nat.Prime 9 by decide]

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
