import H0mework.Versions.X.Arithmetic.FockDynamics.RootUpdate
import H0mework.Realization.Operations.IntegralRelations

/-!
# Fock source action through the existing operation coimage

The fixed Fock expression generates one formal source word. Its complete old/effect
inventory enters the generic residual coimage; the generated target map and range
readout deliver the original Fock state update without an endpoint equality input.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock.OperationRelations

open SourceOperationRelations
open SourceGeneratedScalarDifferentialResidual

noncomputable section

def operationWord : Formal OperationValue OperationVar .parent :=
  Finsupp.single fockOperation 1

def inventory (old increment : IntegralOneParticle) :=
  updateInventory (s := OperationSort.parent)
    (fieldEnvironment old) (fieldEnvironment increment)

abbrev InventoryCarrier (old increment : IntegralOneParticle) :=
  ResidualCarrier (inventory old increment)

def generatedInventory (old increment : IntegralOneParticle) : InventoryCarrier old increment :=
  canonicalResidual (inventory old increment) operationWord

def generatedTarget (old increment : IntegralOneParticle) :=
  inducedResidualMap (updateMorphism (s := OperationSort.parent)
    (fieldEnvironment old) (fieldEnvironment increment)) (generatedInventory old increment)

def targetRead (old increment : IntegralOneParticle) : ParentCarrier :=
  (residualEquivRange
    (evaluation (fieldEnvironment old + fieldEnvironment increment))
    (generatedTarget old increment)).val

theorem inventory_readback (old increment : IntegralOneParticle) :
    (residualEquivRange (inventory old increment) (generatedInventory old increment)).val =
      (secondQuantizedState old, secondQuantizedEffect old increment) := by
  change (evaluation (s := OperationSort.parent) (fieldEnvironment old) operationWord,
    effectEvaluator (s := OperationSort.parent)
      (fieldEnvironment old) (fieldEnvironment increment) operationWord) = _
  simp only [evaluation, effectEvaluator, operationWord, Finsupp.linearCombination_single, one_smul,
    fockOperation_eval, fockOperation_effect]

theorem targetRead_eq_sourceOperation (old increment : IntegralOneParticle) :
    targetRead old increment = secondQuantizedState (old + increment) := by
  change evaluation (s := OperationSort.parent)
    (fieldEnvironment old + fieldEnvironment increment) operationWord = _
  rw [fieldEnvironment_add]
  simp only [evaluation, operationWord, Finsupp.linearCombination_single, one_smul,
    fockOperation_eval]

/-- The original state consumer reads the existing coimage of the complete old/effect pair. -/
theorem targetRead_eq_source_add_trace (old increment : IntegralOneParticle) :
    targetRead old increment = secondQuantizedState old +
      (evaluateOperationTrace old increment).sum := by
  have generated := updated_residual_readout
    (fieldEnvironment old) (fieldEnvironment increment) operationWord
  change targetRead old increment = _ at generated
  simpa only [evaluation, effectEvaluator, operationWord,
    Finsupp.linearCombination_single, one_smul, fockOperation_eval, fockOperation_effect,
    evaluateOperationTrace_sum] using generated

theorem source_update (old target : IntegralOneParticle) :
    secondQuantizedState target = secondQuantizedState old +
      (evaluateOperationTrace old (target - old)).sum := by
  have sourceWrite : old + (target - old) = target := by abel
  calc
    secondQuantizedState target = targetRead old (target - old) := by
      rw [targetRead_eq_sourceOperation, sourceWrite]
    _ = _ := targetRead_eq_source_add_trace old (target - old)

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock.OperationRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

