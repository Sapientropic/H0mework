import H0mework.Versions.R2.Fock.PrimeField.Relation

/-! The actual source increment reindexes the original replayable receipt, which then generates the Fock equation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

variable {current : CanonicalUnitArithmeticRoot.Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}
variable (payload : RootGeneratedParticleWaveCurrentAt current occurrence active)

def receipt : OperationDerivations.OperationProof (sourceFieldAt current) (birth current) :=
  Eq.recOn (motive := fun increment _ => OperationDerivations.OperationProof (sourceFieldAt current) increment)
    (installed_increment payload) payload.operationDerivation

theorem receipt_is_original : HEq (receipt payload) payload.operationDerivation :=
  eqRec_heq (installed_increment payload) payload.operationDerivation

include payload in
theorem receipt_reads_birth :
    OperationDerivations.inventoryRead (sourceFieldAt current) (birth current) =
      (secondQuantizedState (sourceFieldAt current), secondQuantizedEffect (sourceFieldAt current) (birth current)) :=
  OperationDerivations.receipt_read (sourceFieldAt current) (birth current) (receipt payload)

theorem operation_values :
    payload.operationValues = evaluateOperationTrace (sourceFieldAt current) (birth current) := by
  rw [payload.operationValues_eq, payload.operationTrace_eq, installed_increment payload]
  rfl

theorem forced_from_source :
    payload.forcedTrace = secondQuantizedEffect (sourceFieldAt current) (birth current) := by
  rw [payload.forcedTrace_sum, operation_values]
  exact evaluateOperationTrace_sum (sourceFieldAt current) (birth current)

theorem state_from_source :
    payload.targetState = payload.sourceState + secondQuantizedEffect (sourceFieldAt current) (birth current) := by
  have generated := (relation_read_is_generated payload).trans
    (OperationDerivations.targetRead_eq_inventory (sourceFieldAt current) (birth current))
  rw [receipt_reads_birth payload] at generated
  have actual := (relation_read_is_generated payload).trans
    (OperationRelations.targetRead_eq_sourceOperation (sourceFieldAt current) (birth current))
  rw [← target_field current] at actual
  rw [payload.targetState_eq, payload.sourceState_eq]
  exact actual.symm.trans generated

end
end SourceFactorizationAction.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
