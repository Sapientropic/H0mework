import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Runtime.Engine
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! The existing canonical runtime is transported only after complete
process equality. Reachable states and activated occurrences remain sealed. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroRuntime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

variable {source target : SourceNativeInquiryEngineProcess.{u}} (same : source = target)

def transportRuntime (runtime : SourceNativeInquiryRuntime source) :
    SourceNativeInquiryRuntime target := same ▸ runtime

def transportState {runtime : SourceNativeInquiryRuntime source} (state : runtime.State) :
    (transportRuntime same runtime).State := by
  cases same
  exact state

def transportActivated {runtime : SourceNativeInquiryRuntime source} {state : runtime.State}
    (activated : SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt state) :
    SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt (transportState same state) := by
  cases same
  exact activated

theorem runtime_law_commutes (runtime : SourceNativeInquiryRuntime source) :
    (transportRuntime same runtime).activationLaw = transportLaw same runtime.activationLaw := by
  cases same
  rfl

theorem state_fields_commute {runtime : SourceNativeInquiryRuntime source} (state : runtime.State) :
    (transportState same state).engine = transportEngine same state.engine ∧
    HEq (transportState same state).activation (transportActivation same state.activation) := by
  cases same
  exact ⟨rfl, HEq.rfl⟩

theorem tick_commutes {runtime : SourceNativeInquiryRuntime source} (state : runtime.State) :
    (transportState same state).tick = transportActivated same state.tick := by
  cases same
  rfl

/-- The complete activated occurrence, raw compilation readout and exact
macro successor share the same literal process transport. -/
theorem tick_readouts {runtime : SourceNativeInquiryRuntime source} (state : runtime.State) :
    let actual := (transportState same state).tick
    let original := state.tick
    HEq actual original ∧
    HEq actual.rawReadout original.rawReadout ∧
    HEq actual.resolution original.resolution ∧
    HEq actual.answer original.answer ∧
    HEq actual.receipt original.receipt ∧
    actual.resolutionKind = original.resolutionKind ∧
    actual.next = transportEngine same original.next ∧
    actual.nextState = transportState same original.nextState := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl⟩

theorem initialState_commutes (runtime : SourceNativeInquiryRuntime source) :
    (transportRuntime same runtime).initialState = transportState same runtime.initialState := by
  cases same
  rfl

/-- All finite canonical activations commute, using the existing recursive
law at every step rather than an independently supplied activation table. -/
theorem history_commutes (runtime : SourceNativeInquiryRuntime source) (depth : Nat) :
    (transportRuntime same runtime).stateAt depth = transportState same (runtime.stateAt depth) ∧
    HEq ((transportRuntime same runtime).tickAt depth) (runtime.tickAt depth) ∧
    ((transportRuntime same runtime).tickAt depth).nextState =
      transportState same (runtime.tickAt depth).nextState := by
  cases same
  exact ⟨rfl, HEq.rfl, rfl⟩

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroRuntime
