import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiry
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseControls

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquirySource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information Agency.Protocol Continuation

abbrev scope := Distributed.Recall.Information.Regression.scope
abbrev law := Distributed.Recall.Information.Regression.law
abbrev initial (bank : Nat) : Mandate.Source.Current := {Distributed.Recall.Information.Regression.initial with stock := fun _ _ => (bank : ℚ)}
def proposal (bank : Nat) := Mandate.request scope (initial bank) false (.propose false)
def acceptance (bank : Nat) := Mandate.request scope (law.step (initial bank) (proposal bank)) false .accept
def signature : Mandate.Source.Action := ⟨false, [], .challenge, [.challenge], .present⟩
def bootstrap (bank : Nat) := [proposal bank, acceptance bank, signature]
abbrev boot (bank : Nat) := law.next (initial bank) (bootstrap bank)
def review (bank : Nat) := Mandate.request scope (boot bank) false .review
def revoke (bank : Nat) (reviewed : Bool) := Mandate.request scope
  (if reviewed then law.step (boot bank) (review bank) else boot bank) false .revoke

-- The sensor uses an existing local material coordinate. No technology field,
-- sender-supplied version, or out-of-band receipt is added to Code.snapshot.
abbrev code (bank : Nat) : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {Distributed.Recall.Information.Regression.code with
    initial := initial bank
    bootstrap := bootstrap bank
    actions := [signature, revoke bank false, revoke bank true]
    actionLimit := 2
    signals := 3
    initialSignal := 0
    memoryReady := fun _ => true
    readLocal := fun _ snapshot => if snapshot.stock () = (boot bank).stock false () then 1 else 2
    afterSend := fun _ _ old _ => old
    afterDelivery := fun _ _ _ reading => reading
    afterAction := fun _ _ _ => 0
    sendCost := fun _ _ => [AdmissionControls.yes]
    deliveryCost := fun _ => [AdmissionControls.yes]
    eventAlphabet := [.activate 0, .send 0 0, .deliver 0, .adversary (review bank)]}

abbrev source (bank : Nat) : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code bank
  reference := fun _ _ => []
  reference_generated := by
    apply (code bank).every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code bank).publicPrefix
  original := (code bank).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev model (bank : Nat) : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) := ⟨Distributed.Recall.Information.Regression.base, scope, source bank, rfl, rfl⟩
abbrev origin (bank : Nat) : Origin (model bank) where
  history := ⟨(source bank).history, (source bank).original⟩
  response := ⟨Reaction.restrict (code bank) (source bank).opponent, Reaction.restriction_is_generated _ _⟩
  side := .original
abbrev start (bank : Nat) := EventHistory.ofOrigin (model bank) 6 (origin bank)

def quiet (bank : Nat) : Rule (code bank) where
  work := ⟨fun _ _ => [], by
    apply (code bank).every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun _ _ => ⟨none, List.mem_cons_self⟩

abbrev setup (bank : Nat) := [quiet bank, quiet bank]
abbrev inquire (bank : Nat) := WithdrawalInquiry.protocol (model bank) (start bank) (setup bank) 0
abbrev installed (bank : Nat) := setup bank ++ [inquire bank, quiet bank]
abbrev resolve (bank : Nat) := WithdrawalInquiry.protocol (model bank) (start bank) (installed bank) 0

inductive Mode where
  | delivered | reviewed | withheld | lateReview
  deriving DecidableEq

def environment (bank : Nat) (mode : Mode) : Opponent (code bank) := fun history _ _ =>
  match history.length - ((source bank).history.length + 1) with
  | 1 => if mode = .reviewed then some ⟨.adversary (review bank), by simp [code]⟩ else none
  | 3 => if mode = .lateReview then some ⟨.adversary (review bank), by simp [code]⟩ else
      if mode = .withheld then none else some ⟨.deliver 0, by simp [code]⟩
  | _ => none

abbrev past (bank : Nat) (mode : Mode) := (installed bank).map fun rule => (rule, environment bank mode)
abbrev before (bank : Nat) (mode : Mode) := EventHistory.execute (start bank) (past bank mode)
abbrev full (bank : Nat) (mode : Mode) := past bank mode ++ [(resolve bank, environment bank mode)]
abbrev final (bank : Nat) (mode : Mode) := EventHistory.execute (start bank) (full bank mode)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquirySource
