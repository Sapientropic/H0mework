import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerRuntime
import H0mework.Versions.R9c73a630.Foundation.Runtime.GeneratedContinuity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def pointerPaidBalance (state : pointerRuntimeProcess.State) : Prop :=
  Live.entropyProduction (pointerCurrentState state.current) + Live.freeEnergy (pointerCurrentState state.current) =
    Live.entropyProduction Live.initial + Live.freeEnergy Live.initial + pointerAccumulatedWork state.current

def pointerAccountLaw : SourceNativeGeneratedInvariantLaw pointerRuntimeProcess :=
  .create (fun state => PLift (pointerPaidBalance state))
    ⟨(add_zero _).symm⟩
    (fun state previous => ⟨by
      change Live.entropyProduction (pointerCurrentState (pointerNext state.current)) +
        Live.freeEnergy (pointerCurrentState (pointerNext state.current)) =
        Live.entropyProduction Live.initial + Live.freeEnergy Live.initial +
          pointerAccumulatedWork (pointerNext state.current)
      have paid := previous.down
      change Live.entropyProduction (pointerCurrentState state.current) +
        Live.freeEnergy (pointerCurrentState state.current) =
        Live.entropyProduction Live.initial + Live.freeEnergy Live.initial + pointerAccumulatedWork state.current at paid
      linarith [pointerNext_netAccount state.current, pointerAccumulatedWork_next state.current]⟩)

theorem pointerRuntime_entropyPaid (runtime : LivingRuntimeState pointerRuntimeProcess) :
    pointerPaidBalance runtime.state := by
  have paid (state : pointerRuntimeProcess.State) (reachable : SourceNativeRuntimeReachableAt pointerRuntimeProcess state) :
      pointerPaidBalance state := by
    induction reachable with
    | initial => exact pointerAccountLaw.initialAt.down
    | @step state _ previous => exact (pointerAccountLaw.advanceAt state ⟨previous⟩).down
  exact paid runtime.state runtime.reachable

theorem pointerRuntime_allFinitePaid (depth : Nat) :
    pointerPaidBalance (pointerRuntimeProcess.stateAfter depth) := (pointerAccountLaw.generatedAt depth).down

theorem pointerRuntime_completeAccount (runtime : LivingRuntimeState pointerRuntimeProcess) :
    (∀ projection, type_of% (pointerRuntimeFace_factorizes runtime projection)) ∧
    (∀ projection, type_of% (pointerRuntime_face_is_installed runtime projection)) ∧
    type_of% (pointerRuntime_wholeLedger_is_installed runtime) ∧
    type_of% (pointerRuntime_netAccount_is_installed runtime) ∧
    type_of% (pointerRuntimeNext_joint runtime) ∧ type_of% (pointerRuntime_next_is_load runtime) ∧
    type_of% (pointerRuntime_entropyPaid runtime) ∧
    0 ≤ Live.entropyProduction (pointerCurrentState runtime.state.current) :=
  ⟨pointerRuntimeFace_factorizes runtime, pointerRuntime_face_is_installed runtime,
    pointerRuntime_wholeLedger_is_installed runtime, pointerRuntime_netAccount_is_installed runtime,
    pointerRuntimeNext_joint runtime, pointerRuntime_next_is_load runtime, pointerRuntime_entropyPaid runtime,
    Live.entropyProduction_nonnegative _⟩

theorem pointerRuntime_sourceGeneratedPointerInstrument :
    type_of% (pointerRuntime_completeAccount pointerRuntimeSeed) ∧
    type_of% pointerRuntime_firstMeasurement_is_installed ∧ type_of% pointerRuntime_instrumentCertificate ∧
    type_of% pointerRuntime_memory ∧ type_of% pointerRuntimeFirst_generated ∧ type_of% generatedPointerAction_next ∧
    type_of% pointer_received_is_parent ∧ type_of% pointerParent_clock ∧ type_of% pointerParent_prepared_joint ∧
    type_of% pointerRuntime_firstClock ∧
    type_of% (pointerRuntime_nextMeasurement_is_inactive pointerRuntimeSeed) ∧
    (∀ depth, type_of% (pointerRuntime_allFinitePaid depth)) :=
  ⟨pointerRuntime_completeAccount pointerRuntimeSeed, pointerRuntime_firstMeasurement_is_installed,
    pointerRuntime_instrumentCertificate, pointerRuntime_memory, pointerRuntimeFirst_generated,
    generatedPointerAction_next, pointer_received_is_parent, pointerParent_clock, pointerParent_prepared_joint,
    pointerRuntime_firstClock, pointerRuntime_nextMeasurement_is_inactive pointerRuntimeSeed, pointerRuntime_allFinitePaid⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
