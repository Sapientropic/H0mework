import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

/-! A registered-input front for the existing inquiry engine. The process
and its branch compiler are unchanged. Each tick requires a current installed
input; its successor waits without manufacturing the next activation. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.InputRuntime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

variable (process : SourceNativeInquiryEngineProcess.{u})

/-- Only the original initial engine and its registered ask-successors are
reachable. This is an executed finite history, not a future input schedule. -/
inductive History : Engine process → Type (u + 13)
  | initial : History (Engine.initial process)
  | received {engine : Engine process} (prior : History engine)
      (input : Engine.SourceNativeInquiryRegisteredInputAt engine) :
      History (engine.ask (engine.registeredInquiryActivation input)).next

structure State : Type (u + 13) where
  private mk ::
  engine : Engine process
  private history : History process engine

def initial : State process := ⟨Engine.initial process, .initial⟩

variable {process}

abbrev InputAt (state : State process) := Engine.SourceNativeInquiryRegisteredInputAt state.engine

/-- The token retains the installed input occurrence, including two distinct
input faces whose query readouts happen to agree. -/
structure Occurrence (state : State process) : Type u where
  private mk ::
  input : InputAt state

def State.tick (state : State process) (input : InputAt state) : Occurrence state := ⟨input⟩

def Occurrence.rawReadout {state : State process} (event : Occurrence state) :=
  state.engine.ask (state.engine.registeredInquiryActivation event.input)

def Occurrence.answer {state : State process} (event : Occurrence state) := event.rawReadout.answer

def Occurrence.receipt {state : State process} (event : Occurrence state) := event.rawReadout.receipt

def Occurrence.next {state : State process} (event : Occurrence state) : State process :=
  ⟨event.rawReadout.next, .received state.history event.input⟩

theorem registered_tick_retains_the_exact_input (state : State process) (input : InputAt state) :
    (state.tick input).input = input ∧
    (state.engine.registeredInquiryActivation (state.tick input).input).registeredInput? = some input :=
  ⟨rfl, Engine.registeredInquiryActivation_input state.engine input⟩

theorem next_engine_is_the_original_ask_successor {state : State process} (event : Occurrence state) :
    event.next.engine = event.rawReadout.next := rfl

theorem next_erases_to_the_original_generated_current {state : State process} (event : Occurrence state) :
    type_of% event.rawReadout.next_erases_to_generated :=
  event.rawReadout.next_erases_to_generated

theorem next_preserves_the_original_generated_living_law {state : State process} (event : Occurrence state) :
    state.engine.node.PreservesGeneratedLivingLawAt
      (state.engine.registeredInquiryActivation event.input).query event.next.engine.node :=
  event.rawReadout.next_preservesGeneratedLivingLaw

def History.length {engine : Engine process} : History process engine → Nat
  | .initial => 0
  | .received prior _ => prior.length + 1

def State.length (state : State process) : Nat := state.history.length

/-- This counts actual registered asks only. It is neither physical time
nor a fee payment nor a bound on material continuation. -/
theorem next_has_one_more_registered_attempt {state : State process} (event : Occurrence state) :
    event.next.length = state.length + 1 := rfl

theorem no_installed_input_means_no_registered_tick (state : State process)
    (missing : IsEmpty (InputAt state)) : IsEmpty (Occurrence state) :=
  ⟨fun event => missing.false event.input⟩

theorem tick_is_injective_in_the_input (state : State process) : Function.Injective state.tick := by
  intro left right same
  exact congrArg Occurrence.input same

#print axioms registered_tick_retains_the_exact_input
#print axioms next_erases_to_the_original_generated_current
#print axioms next_preserves_the_original_generated_living_law
#print axioms no_installed_input_means_no_registered_tick

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.InputRuntime
