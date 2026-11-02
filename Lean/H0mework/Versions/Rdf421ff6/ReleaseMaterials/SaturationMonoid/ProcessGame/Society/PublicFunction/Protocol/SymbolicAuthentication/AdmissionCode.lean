import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageCommunicationRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionCode

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port (Mandate.State Party Technology) Instrument)

/-- This protocol profile uses the source's genesis revision admission to grant repeat issuance.
Later material revisions remain real; they do not silently replace the installed profile. -/
def mayRewrite (site : Fin base.sites) : Bool :=
  base.law.allowed base.initial.technology (base.law.revisionPort base.initial.technology) (base.siteParty site)

def affected : Finset (Fin base.sites) := Finset.univ.filter (fun site => mayRewrite base site)
abbrev budget := (affected base).card

def pack (ready : Bool) (signal : Fin base.signals) : Fin (base.signals * 2) :=
  ⟨signal.val * 2 + if ready then 0 else 1, by cases ready <;> dsimp <;> omega⟩
def content (signal : Fin (base.signals * 2)) : Fin base.signals := ⟨signal.val / 2, by omega⟩
def ready (signal : Fin (base.signals * 2)) : Bool := signal.val % 2 == 0

omit [DecidableEq Port] [DecidableEq Technology] in
theorem ready_pack (available : Bool) (signal : Fin base.signals) : ready base (pack base available signal) = available := by
  cases available <;> simp [ready, pack, Nat.add_mod]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem content_pack (available : Bool) (signal : Fin base.signals) : content base (pack base available signal) = signal := by
  apply Fin.ext
  cases available <;> dsimp [content, pack] <;> omega

/-- The extra bit is an admission latch, not peer-controlled message data. -/
abbrev lift : Code Party Good Port (Mandate.State Party Technology) Instrument :=
  {base with
    signals := base.signals * 2
    actionLimit := 1
    initialSignal := pack base true base.initialSignal
    readLocal := fun site snapshot => pack base true (base.readLocal site snapshot)
    memoryReady := fun old => ready base old && base.memoryReady (content base old)
    afterSend := fun sender recipient old reading => pack base (ready base old)
      (base.afterSend sender recipient (content base old) (content base reading))
    afterDelivery := fun recipient sender old reading => pack base (ready base old)
      (base.afterDelivery recipient sender (content base old) (content base reading))
    afterAction := fun site old word => pack base (ready base old && mayRewrite base site)
      (base.afterAction site (content base old) word)}

omit [DecidableEq Port] [DecidableEq Technology] in
theorem original_material_law_and_accounts_are_preserved :
    (lift base).law = base.law ∧ (lift base).initial = base.initial ∧
      (lift base).bootstrap = base.bootstrap ∧ (lift base).task = base.task ∧
      (lift base).sendCost = base.sendCost ∧ (lift base).deliveryCost = base.deliveryCost :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem an_event_cannot_reopen_a_sealed_key
    (policy : (lift base).Policy) (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (frame : (lift base).Frame) (event : Event Party Good Port (Mandate.State Party Technology) Instrument base.sites)
    (key : Fin base.sites) (sealed : ready base (frame.inbox key) = false) :
    ready base (((lift base).step policy current frame event).inbox key) = false := by
  cases event with
  | adversary request => exact sealed
  | send sender recipient =>
    simp only [Code.step]
    split
    · dsimp only
      split
      · rename_i same
        subst key
        simp only [ready_pack, sealed]
      · exact sealed
    · exact sealed
  | deliver serial =>
    simp only [Code.step]
    split
    · exact sealed
    · split
      · dsimp only
        split
        · simp only [ready_pack, sealed]
        · exact sealed
      · exact sealed
  | activate site =>
    simp only [Code.step]
    split
    · rename_i same
      subst key
      rw [ready_pack, sealed]
      rfl
    · exact sealed

omit [DecidableEq Port] [DecidableEq Technology] in
theorem feedback_cannot_reopen_a_sealed_key
    (policy : Option (lift base).Policy) (input : Input (lift base)) (state : State (lift base))
    (key : Fin base.sites) (sealed : ready base (state.frame.inbox key) = false) :
    ready base ((Reaction.Feedback.advance (lift base) policy input state).frame.inbox key) = false := by
  cases policy with
  | none => exact sealed
  | some policy =>
    cases chosen : decision (lift base) input state with
    | none => simpa only [Reaction.Feedback.advance, chosen] using sealed
    | some event =>
      simpa only [Reaction.Feedback.advance, chosen, stepLocal] using
        an_event_cannot_reopen_a_sealed_key base policy state.current {state.frame with word := []} event.val key sealed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionCode
