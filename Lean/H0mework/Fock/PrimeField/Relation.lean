import H0mework.Fock.PrimeField.Action

/-! Reindex the original stored old/effect relation and feed it to the existing coimage update. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceOperationRelations SourceGeneratedScalarDifferentialResidual

noncomputable section

variable {current : CanonicalUnitArithmeticRoot.Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}
variable (payload : RootGeneratedParticleWaveCurrentAt current occurrence active)

def relation : OperationRelations.InventoryCarrier (sourceFieldAt current) (birth current) :=
  Eq.recOn (motive := fun increment _ => OperationRelations.InventoryCarrier (sourceFieldAt current) increment)
    (installed_increment payload) payload.operationRelation

theorem relation_is_original : HEq (relation payload) payload.operationRelation :=
  eqRec_heq (installed_increment payload) payload.operationRelation

private theorem transported_generated (old left right : IntegralOneParticle) (same : left = right) :
    Eq.recOn (motive := fun increment _ => OperationRelations.InventoryCarrier old increment) same
        (OperationRelations.generatedInventory old left) = OperationRelations.generatedInventory old right := by
  cases same
  rfl

theorem relation_generated : relation payload = OperationRelations.generatedInventory (sourceFieldAt current) (birth current) := by
  exact (congrArg (fun value : OperationRelations.InventoryCarrier (sourceFieldAt current)
      (sourceFieldAt payload.nativeWrite.target - sourceFieldAt current) =>
      Eq.recOn (motive := fun increment _ => OperationRelations.InventoryCarrier (sourceFieldAt current) increment)
        (installed_increment payload) value) payload.operationRelation_eq).trans
    (transported_generated _ _ _ (installed_increment payload))

def relationRead : ParentCarrier :=
  (residualEquivRange
    (evaluation (s := OperationSort.parent) (fieldEnvironment (sourceFieldAt current) + fieldEnvironment (birth current)))
    (inducedResidualMap (updateMorphism (s := OperationSort.parent)
      (fieldEnvironment (sourceFieldAt current)) (fieldEnvironment (birth current))) (relation payload))).val

theorem relation_read_is_generated :
    relationRead payload = OperationRelations.targetRead (sourceFieldAt current) (birth current) := by
  unfold relationRead
  rw [relation_generated]
  rfl

end
end SourceFactorizationAction.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
