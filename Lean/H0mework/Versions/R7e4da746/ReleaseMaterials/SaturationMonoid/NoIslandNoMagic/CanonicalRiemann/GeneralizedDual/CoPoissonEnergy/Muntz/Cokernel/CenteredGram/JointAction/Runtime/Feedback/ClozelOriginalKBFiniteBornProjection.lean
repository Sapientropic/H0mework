import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornInventory
import H0mework.Realization.Completion.HistoryTransition

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKBFiniteCalculation.BornProjection
open SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance projectionGroups (grade : Nat) : ∀ target,
    AddCommGroup (BornInventory.L.Value (PairValue Value) grade target) :=
  BornInventory.L.groups (PairValue Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "source" => BornInventory.sourceBornHistory observation nontrivial half depth ordinal
local notation "target" => BornInventory.actualBornHistory observation nontrivial half depth ordinal

/-- The actual source birth supplies both inputs to the existing completion consumer. -/
def transition : CofinalHistoryTransition.GeneratedTransition source target :=
  CofinalHistoryTransition.GeneratedTransition.create source target
    (BornInventory.actual_source_generators_in_born observation nontrivial half depth ordinal)
    (by
      intro word present
      change (target).completionProjection
        ⟨word.val, BornInventory.actual_source_generators_in_born
          observation nontrivial half depth ordinal word.property⟩ = 0
      exact (Submodule.Quotient.mk_eq_zero _).2
        (BornInventory.actual_source_relations_in_born observation nontrivial half depth ordinal present))

/-- This square is generated from the full transported source inventory. -/
theorem completion_projection_square : type_of%
    (CofinalHistoryTransition.GeneratedTransition.completionMap_comp_projection source target
      (transition observation nontrivial half depth ordinal)) :=
  CofinalHistoryTransition.GeneratedTransition.completionMap_comp_projection source target
    (transition observation nontrivial half depth ordinal)

/-- Every paid source relation reaches the same actual born quotient kernel. -/
theorem complete_source_relations_target_kernel (word : (source).relationClosure) :
    (target).completionProjection
      ((Submodule.inclusion (target).relationClosure_le_generatorClosure)
        ⟨word.val, BornInventory.actual_source_relations_in_born
          observation nontrivial half depth ordinal word.property⟩) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2
    (BornInventory.actual_source_relations_in_born observation nontrivial half depth ordinal word.property)

end OriginalKBFiniteCalculation.BornProjection
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
