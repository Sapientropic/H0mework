import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Registry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SourceNativeInquiryRuntime
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev State := InputRuntime.State (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)

def initial : State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader :=
  InputRuntime.initial (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)

/-- Each input is a read of the current installed source face. A completed
batch reads its actual raw germ; no later input or activation is stored. -/
def installedInput (engine : Engine (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)) :
    Engine.SourceNativeInquiryRegisteredInputAt engine := by
  rcases engine with ⟨stage⟩
  cases stage with
  | input => exact Ingress.registeredInput (review := review) input depth sourceStart datum prefixLimit renewalLimit
  | account tick =>
      change SourceNativeRootInquiryInputAt
        (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.state.base.root
        (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.state.base.visit
        (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.Query
      cases current : actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick with
      | original frame =>
          exact Raw.registeredInput frame.package.source frame.package.sourceData frame.package.reader
            frame.package.basis (.finite frame.visit) frame.ready frame.sourceFold
      | enacted origin admission frame =>
          exact Public.Inquiry.registeredInput frame.source frame.reader (.finite frame.visit) frame.actual

def event (state : State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) : InputRuntime.Occurrence state :=
  state.tick (installedInput (review := review) input depth sourceStart datum prefixLimit renewalLimit reader state.engine)

def advance (state : State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) :
    State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader :=
  (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader state).next

/-- A finite observation of this one source-controlled registered runtime. -/
def run : Nat → State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  | 0 => initial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  | ticks + 1 => advance (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (run ticks)

def firstEvent : InputRuntime.Occurrence (initial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) :=
  event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader _

theorem first_ask_returns_the_literal_complete_frame :
    (firstEvent (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).next.engine.node =
      .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader 0).presentation := rfl

theorem first_ask_consumes_the_source_action :
    RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      (firstEvent (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).rawReadout.resolution
      (Ingress.generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) := HEq.rfl

variable (tick : Nat) (state : State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
  (same : state.engine.node = .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation)

omit same in
private theorem next_account_node
    (engine : Engine (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader))
    (sameNode : engine.node = .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation)
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node =
      .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + 1)).presentation := by
  rcases engine with ⟨stage⟩
  have exactStage : stage = Stage.account tick :=
    (process (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase sameNode)
  subst stage
  rfl

include same in
theorem actual_next (occurrence : InputRuntime.Occurrence state) :
    occurrence.next.engine.node =
      .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + 1)).presentation :=
  next_account_node (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick state.engine same
    (state.engine.registeredInquiryActivation occurrence.input)

theorem run_is_the_original_registered_history (ticks : Nat) :
    (run (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (ticks + 1)).engine.node =
      .active (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader ticks).presentation := by
  induction ticks with
  | zero => exact first_ask_returns_the_literal_complete_frame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  | succ ticks prior =>
      exact actual_next (review := review) input depth sourceStart datum prefixLimit renewalLimit reader ticks _ prior
        (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader _)

theorem each_actual_attempt_has_the_original_complete_next
    (state : State (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) :
    state.engine.node.PreservesGeneratedLivingLawAt
      (state.engine.registeredInquiryActivation
        (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader state).input).query
      (advance (review := review) input depth sourceStart datum prefixLimit renewalLimit reader state).engine.node :=
  (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader state).rawReadout.next_preservesGeneratedLivingLaw

#print axioms installedInput
#print axioms run_is_the_original_registered_history
#print axioms each_actual_attempt_has_the_original_complete_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
