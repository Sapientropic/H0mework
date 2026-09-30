import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Source

/-! The complete process output consumes the original compiler and sealed
runtime mouths. Activation laws are transported existing values, never
created by the material coverage theorem. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {original : SourceNativeInquiryEngineProcess.{0}} (origin : Origin original)

/-- Every query at every generated registry index retains its entire
original compilation, including indices outside the activated trajectory. -/
theorem Origin.compile_recovers (index : origin.process.State)
    (query : (origin.process.stateAt index).Query) :
    HEq (MotherRegistryRecovery.compile (origin.process.stateAt index) query)
      (MotherRegistryRecovery.compile (original.stateAt (origin.presentation.state index))
        (origin.presentation.query index query)) :=
  origin.presentation.compile_heq index query

theorem Origin.ask_recovers (engine : Engine original)
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    let actual := (MotherMacroRuntime.transportEngine origin.restrict_eq.symm engine).ask
      (MotherMacroRuntime.transportActivation origin.restrict_eq.symm activation)
    let prior := engine.ask activation
    HEq actual prior ∧
    HEq actual.resolution prior.resolution ∧
    HEq actual.answer prior.answer ∧
    HEq actual.receipt prior.receipt ∧
    actual.next = MotherMacroRuntime.transportEngine origin.restrict_eq.symm prior.next :=
  MotherMacroRuntime.ask_readouts origin.restrict_eq.symm engine activation

def Origin.runtime (runtime : SourceNativeInquiryRuntime original) : SourceNativeInquiryRuntime origin.restrict :=
  MotherMacroRuntime.transportRuntime origin.restrict_eq.symm runtime

theorem Origin.runtime_tick (runtime : SourceNativeInquiryRuntime original) (state : runtime.State) :
    let actual := (MotherMacroRuntime.transportState origin.restrict_eq.symm state).tick
    let prior := state.tick
    HEq actual prior ∧
    HEq actual.rawReadout prior.rawReadout ∧
    HEq actual.resolution prior.resolution ∧
    HEq actual.answer prior.answer ∧
    HEq actual.receipt prior.receipt ∧
    actual.resolutionKind = prior.resolutionKind ∧
    actual.next = MotherMacroRuntime.transportEngine origin.restrict_eq.symm prior.next ∧
    actual.nextState = MotherMacroRuntime.transportState origin.restrict_eq.symm prior.nextState :=
  MotherMacroRuntime.tick_readouts origin.restrict_eq.symm state

theorem Origin.runtime_history (runtime : SourceNativeInquiryRuntime original) (depth : Nat) :
    (origin.runtime runtime).stateAt depth =
      MotherMacroRuntime.transportState origin.restrict_eq.symm (runtime.stateAt depth) ∧
    HEq ((origin.runtime runtime).tickAt depth) (runtime.tickAt depth) ∧
    ((origin.runtime runtime).tickAt depth).nextState =
      MotherMacroRuntime.transportState origin.restrict_eq.symm (runtime.tickAt depth).nextState :=
  MotherMacroRuntime.history_commutes origin.restrict_eq.symm runtime depth

/-- No formed-node, address, activation or representability premise enters
the complete-process coverage mouth. The factory/get binding is carried by
Origin.process, and its inverse restriction restores the entire record. -/
theorem every_original_process (original : SourceNativeInquiryEngineProcess.{0}) :
    ∃ origin : Origin original,
      origin.restrict = original ∧
      HEq origin.restrict.successorAt original.successorAt ∧
      ∀ index : origin.process.State, ∀ query : (origin.process.stateAt index).Query,
        HEq (MotherRegistryRecovery.compile (origin.process.stateAt index) query)
          (MotherRegistryRecovery.compile (original.stateAt (origin.presentation.state index))
            (origin.presentation.query index query)) := by
  obtain ⟨origin⟩ := every_source original
  exact ⟨origin, origin.restrict_eq, origin.successorAt_recovers, origin.compile_recovers⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroSource
