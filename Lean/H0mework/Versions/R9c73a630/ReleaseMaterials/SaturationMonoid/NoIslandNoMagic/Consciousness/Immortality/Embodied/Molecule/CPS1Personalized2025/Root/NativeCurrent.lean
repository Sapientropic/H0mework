import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Types
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootFromInput

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Native

open Source.NativeRegistration
open CPS1MaterialIncidence.NativeRootDataProbe

attribute [local irreducible] generated_input source_programme InputBodyAt source_input_body input_body_next

noncomputable section

/-- The source-generated body is stored in the current; the old analysis phase
is its restriction, not a clock that selects a future body. -/
structure Current : Type where
  phase : Root.Current
  input : RegisteredNativeInput
  body : InputBodyAt input

def erase (current : Current) : Root.Current := current.phase

/-- This data factory is subordinate to the root source's input registration. -/
def initial (input : RegisteredNativeInput) : Current :=
  ⟨.registeredSource,input,source_input_body input⟩

def next (current : Current) : Current :=
  ⟨Root.nextCurrent current.phase,current.input,input_body_next current.input current.body⟩

def OperationAt (current : Current) : Prop := Root.OperationAt (erase current)

theorem sourceOperation (current : Current) : OperationAt current :=
  Root.sourceOperation (erase current)

/-- The event carries its computed body and the equation tying it to this
current. Its producer accepts no caller-selected after-state. -/
structure Write (current : Current) : Type where
  body : InputBodyAt current.input
  actual : body = input_body_next current.input current.body
  operation : OperationAt current

def nativeWrite (current : Current) : Write current :=
  ⟨input_body_next current.input current.body,rfl,sourceOperation current⟩

abbrev EventAt (current : Current) : Type := Write current

abbrev sourceEvent (current : Current) : EventAt current := nativeWrite current

def nativeTarget {current : Current} (event : Write current) : Current :=
  ⟨Root.nextCurrent current.phase,current.input,event.body⟩

theorem initial_phase (input : RegisteredNativeInput) :
    erase (initial input) = .registeredSource := rfl

theorem initial_input (input : RegisteredNativeInput) :
    (initial input).input = input := rfl

theorem initial_body (input : RegisteredNativeInput) :
    (initial input).body = source_input_body input := rfl

theorem erase_next (current : Current) :
    erase (next current) = Root.nextCurrent (erase current) := rfl

theorem next_input (current : Current) : (next current).input = current.input := rfl

theorem next_body (current : Current) :
    (next current).body = input_body_next current.input current.body := rfl

theorem nativeTarget_actual {current : Current} (event : Write current) :
    nativeTarget event = next current := by
  unfold nativeTarget next
  rw [event.actual]

theorem native_write_kernel {current : Current} (event : Write current) :
    (nativeTarget event).body = input_body_next current.input current.body := event.actual

theorem sourceEvent_target (current : Current) :
    nativeTarget (sourceEvent current) = next current := rfl

theorem sourceEvent_body (current : Current) :
    (sourceEvent current).body = input_body_next current.input current.body := rfl

theorem sourceEvent_operation (current : Current) :
    (sourceEvent current).operation = sourceOperation current := rfl

theorem sourceEvent_erases (current : Current) :
    erase (nativeTarget (sourceEvent current)) = Root.nextCurrent (erase current) := rfl

theorem next_next_input (current : Current) :
    (next (next current)).input = current.input := rfl

theorem next_next_body (current : Current) :
    (next (next current)).body =
      input_body_next current.input (input_body_next current.input current.body) := rfl

theorem second_event_consumes_previous_body (current : Current) :
    (sourceEvent (nativeTarget (sourceEvent current))).body =
      input_body_next current.input (sourceEvent current).body := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Native
