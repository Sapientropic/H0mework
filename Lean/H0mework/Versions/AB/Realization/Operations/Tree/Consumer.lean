import H0mework.Versions.AB.Realization.Operations.Tree.Source
import H0mework.Versions.R2.Arithmetic.FockDynamics.RootRuntime

/-! The compiled tree is read from the original source occurrence. The
physical whole and next retain their existing receipts; query charging is an installer responsibility. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree
open ArithmeticGeneration CanonicalUnitArithmeticRoot
open SourceOperationEffects SourceOperationExecution

theorem actual_write_programme (current : Current) :
    (program (emitted current).2.actionTrace).eval environment =
      Finsupp.single (emitted current).2.write.target 1 :=
  (program_source _).trans (congrArg (fun value => Finsupp.single value (1 : ℤ))
    (emitted current).2.action_operation_agree.1.symm)

theorem physical_whole_next (depth : Nat) :
    let runtime := NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeAt depth
    let payload := NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimePayload depth
    payload.nativeWrite.target = nativeActionTarget runtime.emittedOccurrence.2.actionTrace ∧
      payload.targetState = payload.sourceState + payload.forcedTrace ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent =
        NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeFacade.process.stateAt
          (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeFacade.process.successor runtime.state) :=
  NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeSourceAction_fockLedgerNext depth

theorem runtime_program_source (depth : Nat) :
    let runtime := NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeAt depth
    let payload := NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimePayload depth
    (program runtime.emittedOccurrence.2.actionTrace).eval environment =
        Finsupp.single payload.nativeWrite.target 1 ∧
      payload.targetState = payload.sourceState + payload.forcedTrace ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent =
        NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeFacade.process.stateAt
          (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeFacade.process.successor runtime.state) := by
  have original := physical_whole_next depth
  exact ⟨(program_source _).trans
    (congrArg (fun value => Finsupp.single value (1 : ℤ)) original.1.symm), original.2⟩

end SourceOperationNative.Tree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
