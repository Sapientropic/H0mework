import H0mework.Fock.HistoryConditional.InformationDynamic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInformationReadback

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (dynamicRead dynamicInformation)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem dynamic_variance_capacity (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (((inventoryBound runtime + 1 : ℝ) / 2) ^ 2 - 1) / 12 ≤ SourceConditionalVector.dynamicVariance runtime depth := by
  have information := dynamic_exponential_lower runtime depth
  have recovery := model_information_cost runtime depth
  linarith

theorem dynamic_decoder_capacity (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (((inventoryBound runtime + 1 : ℝ) / 2) ^ 2 - 1) / 12 ≤ SourceConditionalVector.dynamicError runtime depth decoder := by
  exact (dynamic_variance_capacity runtime depth).trans (SourceConditionalVector.dynamic_optimal runtime depth decoder)

theorem dynamic_budget_inventory (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier)
    (budget : ℝ) (bounded : SourceConditionalVector.dynamicError runtime depth decoder ≤ budget) :
    (inventoryBound runtime + 1 : ℝ) ^ 2 ≤ 48 * budget + 4 := by
  have recovery := (dynamic_decoder_capacity runtime depth decoder).trans bounded
  have inventory : 0 ≤ SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have paid := div_nonneg inventory (by positivity : (0 : ℝ) ≤ inventoryBound runtime + 1)
  nlinarith

theorem no_uniform_dynamic_budget (budget : ℝ) :
    ∃ stages : Nat, ∀ depth : Nat, ∀ decoder : Field parity → SourceJointClockGraph.Carrier,
      budget < SourceConditionalVector.dynamicError (runtimeAt stages) depth decoder := by
  obtain ⟨stages, large⟩ := exists_nat_gt (48 * budget + 4)
  refine ⟨stages, fun depth decoder => ?_⟩
  by_contra bounded
  have forced := dynamic_budget_inventory (runtimeAt stages) depth decoder budget (le_of_not_gt bounded)
  rw [SourceConditionalInventory.runtime_bound] at forced
  have nonnegative : (0 : ℝ) ≤ stages := Nat.cast_nonneg _
  nlinarith

end
end SourceInformationReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
