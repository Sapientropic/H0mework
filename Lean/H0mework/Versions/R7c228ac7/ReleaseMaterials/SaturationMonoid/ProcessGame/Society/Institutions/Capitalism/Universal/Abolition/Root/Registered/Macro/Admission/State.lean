import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

inductive EventAt : frame.V.Current → Type
  | pending : EventAt origin
  | registered {current : frame.V.Current}
      (native : Nonempty ((Epoch.Finance.process input depth count).Run registered.admitted.current
        (frame.account current).current)) : EventAt current

def state {current : frame.V.Current} : EventAt frame registered current → registered.law.DebtState
  | .pending => .pending
  | .registered native => .registered (frame.account current) native

def nextEvent {current : frame.V.Current} (event : EventAt frame registered current) :
    EventAt frame registered (frame.next current) := by
  cases event with
  | pending =>
      apply EventAt.registered
      rw [registered.actual_next_account]
      exact ⟨.nil⟩
  | registered prior =>
      exact .registered (prior.map fun run => run.concatRuns (Epoch.Finance.process input depth count) (frame.native current))

private theorem registered_eq {left right : (Epoch.Finance.process input depth count).GeneratedState}
    (leftRun : Nonempty ((Epoch.Finance.process input depth count).Run registered.admitted.current left.current))
    (rightRun : Nonempty ((Epoch.Finance.process input depth count).Run registered.admitted.current right.current))
    (same : left = right) :
    (Epoch.Finance.Activation.State.registered (before := frame.account origin) (claim := .inr registered.issued.claim) left leftRun) =
      .registered right rightRun := by
  cases same
  rfl

def actionTarget {current : frame.V.Current} : EventAt frame registered current → registered.law.DebtState
  | .pending => registered.firstStep.target
  | .registered prior =>
      match frame.item? current with
      | some item => .registered ((Epoch.Finance.consume input depth count item (frame.account current)).next input depth count)
          (prior.map fun run => run.concatRuns (Epoch.Finance.process input depth count)
            ((Epoch.Finance.consume input depth count item (frame.account current)).transition input depth count))
      | none => .registered (frame.account current) prior

def actionReceipt {current : frame.V.Current} (event : EventAt frame registered current) :
    registered.law.StepAt (state frame registered event) (actionTarget frame registered event) ⊕
      registered.law.TransportAt (state frame registered event) (actionTarget frame registered event) := by
  cases event with
  | pending => exact .inl registered.firstStep.step
  | @registered current prior =>
      dsimp only [actionTarget, state]
      cases selected : frame.item? current with
      | some item => exact .inr (.actualInstruction (frame.account current) prior item)
      | none => exact .inr (.unchanged _)

theorem next_state {current : frame.V.Current} (event : EventAt frame registered current) :
    state frame registered (nextEvent frame registered event) = actionTarget frame registered event := by
  cases event with
  | pending => exact registered_eq frame registered _ _ registered.actual_next_account
  | @registered current prior =>
      dsimp only [actionTarget, state, nextEvent]
      cases found : frame.item? current with
      | some item =>
          apply registered_eq frame registered
          exact frame.account_next_of_item current item found
      | none =>
          apply registered_eq frame registered
          exact frame.account_next_of_empty current found

abbrev Current := Sigma (EventAt frame registered)
def initial : Current frame registered := ⟨origin, .pending⟩
def next (current : Current frame registered) : Current frame registered :=
  ⟨frame.next current.1, nextEvent frame registered current.2⟩
abbrev N := ExtendedNetwork frame.N registered.law

def supportAt (current : Current frame registered) : (N frame registered).Support :=
  ⟨frame.sourceSupport current.1, some (state frame registered current.2)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
