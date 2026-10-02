import H0mework.Versions.R2.Realization.Operations.Context.Execution
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Context.Relations.Consumer

/-! The original physical expression executes before its actual next
binding is replayed. Its source pair, typed boundary and new trace are read
from the same physical runtime; the old proof remains an independent value. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalForwardTransport
open SourceOperationEffects SourceOperationExecution SourceOperationNative SourceOperationScalarPresentation SourceOperationInventoryLift
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation

variable (runtime : LivingRuntimeState process)

def actualTrace : Trace (SourcePhysicalContextRelationConsumer.readPaired runtime.state)
    (liftExpr fockOperation) (.const ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace)) := by
  have generated := execution (SourcePhysicalContextRelationConsumer.readPaired runtime.state) (liftExpr fockOperation)
  have source := (SourcePhysicalContextRelationConsumer.sourceTree runtime).sound
  change (liftExpr fockOperation).eval (SourcePhysicalContextRelationConsumer.readPaired runtime.state) =
    ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) at source
  rw [source] at generated
  exact generated

def actualNextTrace : Trace (Context.environment (point runtime))
    ((Context.embed SourcePhysicalContextRelationConsumer.readPaired (liftExpr fockOperation)).subst Context.binding)
    (.const ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace)) :=
  Context.nextForwardTrace SourcePhysicalContextRelationConsumer.readPaired runtime
    (actualTrace runtime.tick.next)

theorem actual_source_charge : (actualNextTrace runtime).length =
    remaining ((Context.embed SourcePhysicalContextRelationConsumer.readPaired (liftExpr fockOperation)).subst Context.binding) :=
  (actualNextTrace runtime).length_to_const

theorem actual_source_boundary : relationMap (R := ℤ) (Context.environment (point runtime))
    (actualNextTrace runtime).relationWords =
    Finsupp.single ((Context.embed SourcePhysicalContextRelationConsumer.readPaired (liftExpr fockOperation)).subst Context.binding) 1 -
      Finsupp.single (.const ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace)) 1 :=
  (actualNextTrace runtime).relation_boundary

def retains_existing_type :
    SourceOperationDerivations.Derivation (Context.environment (point runtime))
      ((Context.embed SourcePhysicalContextRelationConsumer.readPaired (liftExpr fockOperation)).subst Context.binding)
      (.const ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace)) :=
  (actualNextTrace runtime).toDerivation

end SourcePhysicalForwardTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
