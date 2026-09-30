import H0mework.Versions.X.Fock.CopyGraph.RecurrenceHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section
local instance effectRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

def residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  value - SourceCopyGraph.action (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
    (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) (recovery runtime index steps value))

def birthMap (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  let h := innovationFromPrevious (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
    (sourceRead (inventoryBound runtime) index) (recovery runtime index steps)
  ((((‖h‖ ^ 2 : ℝ) : ℂ)⁻¹) • innerSL ℂ h).smulRight h

def lossMap (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  if supported : sourceRead (inventoryBound runtime) index (inventoryBound runtime + steps + 1) ∈
      (observed (historyPMF (inventoryBound runtime + steps))
        (oldRead (inventoryBound runtime + steps) (sourceRead (inventoryBound runtime) index))).support then
    let w := normal (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (sourceRead (inventoryBound runtime) index) (recovery runtime index steps) supported
    (((‖w‖ ^ 2 : ℝ) : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ w w
  else 0

theorem residual_canonical (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    residual runtime index steps value = SourceConditionalGraphDecoder.residual
      (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (oldRead (inventoryBound runtime + steps) (sourceRead (inventoryBound runtime) index)) value := by
  rw [residual, recovery_canonical]
  have original := SourceConditionalGraphDecoder.original_reconstruction
    (inventoryBound runtime + steps) (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
    (oldRead (inventoryBound runtime + steps) (sourceRead (inventoryBound runtime) index)) value
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

theorem residual_successor (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) value = SourceGraphGrowth.newResidual
      (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (sourceRead (inventoryBound runtime) index) value := by
  rw [residual_canonical]
  rfl

theorem birth_map_canonical (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) :
    birthMap runtime index steps = SourceGraphBirth.update (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (sourceRead (inventoryBound runtime) index) := by
  rw [birthMap, recovery_canonical, innovation_canonical]
  rfl

theorem loss_map_canonical (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) :
    lossMap runtime index steps = SourceGraphFibreUpdate.sourceUpdate (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (sourceRead (inventoryBound runtime) index) := by
  simp only [lossMap, recovery_canonical, normal_canonical]
  rfl

theorem residual_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) value + birthMap runtime index steps value =
      residual runtime index steps value + lossMap runtime index steps value := by
  rw [residual_canonical, residual_canonical, birth_map_canonical, loss_map_canonical,
    SourceGraphBirth.update_is_birth, SourceGraphFibreUpdate.source_update_is_loss]
  exact SourceGraphGrowth.growth_residual (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (sourceRead (inventoryBound runtime) index) value

theorem energy_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖residual runtime index (steps + 1) value‖ ^ 2 + ‖birthMap runtime index steps value‖ ^ 2 =
      ‖residual runtime index steps value‖ ^ 2 + ‖lossMap runtime index steps value‖ ^ 2 := by
  have older : residual runtime index steps value = SourceGraphGrowth.oldResidual
      (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (sourceRead (inventoryBound runtime) index) value := residual_canonical runtime index steps value
  rw [residual_successor, older, birth_map_canonical, loss_map_canonical,
    SourceGraphBirth.update_is_birth, SourceGraphFibreUpdate.source_update_is_loss]
  exact SourceGraphGrowth.growth_energy (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (sourceRead (inventoryBound runtime) index) value

theorem history_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    residual runtime index steps value + ∑ stage ∈ Finset.range steps, birthMap runtime index stage value =
      residual runtime index 0 value + ∑ stage ∈ Finset.range steps, lossMap runtime index stage value := by
  induction steps with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ steps previous =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have source := residual_step runtime index steps value
    calc
      _ = (residual runtime index (steps + 1) value + birthMap runtime index steps value) +
          ∑ stage ∈ Finset.range steps, birthMap runtime index stage value := by abel
      _ = (residual runtime index steps value + lossMap runtime index steps value) +
          ∑ stage ∈ Finset.range steps, birthMap runtime index stage value := by rw [source]
      _ = (residual runtime index steps value + ∑ stage ∈ Finset.range steps, birthMap runtime index stage value) +
          lossMap runtime index steps value := by abel
      _ = _ := by rw [previous]; abel

theorem history_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖residual runtime index steps value‖ ^ 2 + ∑ stage ∈ Finset.range steps, ‖birthMap runtime index stage value‖ ^ 2 =
      ‖residual runtime index 0 value‖ ^ 2 + ∑ stage ∈ Finset.range steps, ‖lossMap runtime index stage value‖ ^ 2 := by
  induction steps with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ steps previous =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have source := energy_step runtime index steps value
    linarith only [previous, source]

theorem recovery_improves_iff (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖residual runtime index steps value‖ ^ 2 ≤ ‖residual runtime index 0 value‖ ^ 2 ↔
      (∑ stage ∈ Finset.range steps, ‖lossMap runtime index stage value‖ ^ 2) ≤
        ∑ stage ∈ Finset.range steps, ‖birthMap runtime index stage value‖ ^ 2 := by
  have paid := history_energy runtime index steps value
  constructor <;> intro comparison <;> linarith only [paid, comparison]

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
