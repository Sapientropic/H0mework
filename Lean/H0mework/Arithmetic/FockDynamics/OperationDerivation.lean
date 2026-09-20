import H0mework.Realization.Operations.DerivationReduction
import H0mework.Realization.Operations.DerivationInventory
import H0mework.Arithmetic.FockDynamics.OperationRelation

/-! The original Fock operation generates a proof receipt consumed before its state update. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock.OperationDerivations

open SourceOperationDerivations SourceOperationInventoryLift

noncomputable section

def inventoryRead (old increment : IntegralOneParticle) : ParentCarrier × ParentCarrier :=
  (liftExpr fockOperation).eval (pairEnvironment (fieldEnvironment old) (fieldEnvironment increment))

abbrev OperationProof (old increment : IntegralOneParticle) :=
  Derivation (pairEnvironment (fieldEnvironment old) (fieldEnvironment increment))
    (liftExpr fockOperation) (.const (secondQuantizedState old, secondQuantizedEffect old increment))

def generatedProof (old increment : IntegralOneParticle) : OperationProof old increment := by
  have generated := Derivation.normalize
    (pairEnvironment (fieldEnvironment old) (fieldEnvironment increment)) (liftExpr fockOperation)
  rw [eval_liftExpr, fockOperation_eval, fockOperation_effect] at generated
  exact generated

theorem receipt_read (old increment : IntegralOneParticle) (receipt : OperationProof old increment) :
    inventoryRead old increment = (secondQuantizedState old, secondQuantizedEffect old increment) :=
  receipt.sound

theorem targetRead_eq_inventory (old increment : IntegralOneParticle) :
    OperationRelations.targetRead old increment =
      (inventoryRead old increment).1 + (inventoryRead old increment).2 := by
  rw [OperationRelations.targetRead_eq_source_add_trace, evaluateOperationTrace_sum]
  simp only [inventoryRead, eval_liftExpr, fockOperation_eval, fockOperation_effect]

/-- The actual operation receipt is eliminated before the existing coimage reaches the state. -/
theorem source_update (old target : IntegralOneParticle)
    (receipt : OperationProof old (target - old)) :
    secondQuantizedState target = secondQuantizedState old +
      (evaluateOperationTrace old (target - old)).sum := by
  have generated := targetRead_eq_inventory old (target - old)
  rw [receipt_read old (target - old) receipt] at generated
  have sourceWrite : old + (target - old) = target := by abel
  rw [OperationRelations.targetRead_eq_sourceOperation, sourceWrite] at generated
  exact generated.trans (congrArg (secondQuantizedState old + ·)
    (evaluateOperationTrace_sum old (target - old)).symm)

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock.OperationDerivations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
