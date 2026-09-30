import H0mework.Versions.X.Fock.CopyGraph.GrowthBirth
import H0mework.Versions.X.Fock.CopyGraph.RefinementTransfer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def newResidual (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceConditionalGraphDecoder.residual (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read)

def forgettingLoss (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceGraphRefinement.gain (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) Prod.fst

theorem forgetting_residual (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    newResidual depth index read value = taggedResidual depth index read value + forgettingLoss depth index read value := by
  have source := SourceGraphRefinement.residual_update (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value
  simpa only [newResidual, taggedResidual, forgettingLoss, tagged_forget] using source

theorem forgetting_energy (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    ‖newResidual depth index read value‖ ^ 2 = ‖taggedResidual depth index read value‖ ^ 2 + ‖forgettingLoss depth index read value‖ ^ 2 := by
  have source := SourceGraphRefinement.residual_energy (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value
  simpa only [newResidual, taggedResidual, forgettingLoss, tagged_forget] using source

theorem growth_residual (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    newResidual depth index read value + birthGain depth index read value =
      oldResidual depth index read value + forgettingLoss depth index read value := by
  rw [forgetting_residual, birth_residual]
  abel

theorem growth_energy (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    ‖newResidual depth index read value‖ ^ 2 + ‖birthGain depth index read value‖ ^ 2 =
      ‖oldResidual depth index read value‖ ^ 2 + ‖forgettingLoss depth index read value‖ ^ 2 := by
  rw [forgetting_energy, birth_energy]
  ring

theorem no_free_monotonicity (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    ‖newResidual depth index read value‖ ^ 2 ≤ ‖oldResidual depth index read value‖ ^ 2 ↔
      ‖forgettingLoss depth index read value‖ ^ 2 ≤ ‖birthGain depth index read value‖ ^ 2 := by
  have paid := growth_energy depth index read value
  constructor <;> intro comparison <;> linarith only [paid, comparison]

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
