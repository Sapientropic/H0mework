import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationControls

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadbackSource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information Agency.Protocol Continuation

inductive Mode where
  | normal | erased | rewritten | unreadable | wrongWire | unpaidSend | unpaidDelivery
  deriving DecidableEq

abbrev yes := AttestationControls.yes
abbrev no := AttestationControls.no
def receiveFee : Mandate.Source.Action := ⟨true, [], .resource, [], .use true [((), 1)] .external⟩
def hugeReceive : Mandate.Source.Action := ⟨true, [], .resource, [], .use true [((), 100)] .external⟩

abbrev code (mode : Mode) : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {AttestationControls.origin.code with
    initial := {AttestationControls.origin.code.initial with stock := fun _ _ => 10}
    actions := [yes, no]
    actionLimit := 1
    sites := 2
    siteParty := fun site => decide (site = 1)
    signals := 3
    initialSignal := 0
    memoryReady := fun reading => !(mode == .unreadable && reading == 1)
    readLocal := fun _ _ => if mode = .wrongWire then 2 else 1
    afterAction := fun _ old _ => old
    afterSend := fun _ _ old _ => old
    afterDelivery := fun _ _ _ reading => if mode = .erased then 0 else if mode = .rewritten then 2 else reading
    sendCost := fun _ _ => if mode = .unpaidSend then [AttestationControls.huge] else [yes]
    deliveryCost := fun _ => if mode = .unpaidDelivery then [hugeReceive] else [receiveFee]
    eventAlphabet := [.activate 0, .activate 1, .send 0 1, .deliver 0]
    eventLimit := 0
    eligible := fun _ => true}

abbrev source (mode : Mode) : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code mode
  reference := fun _ _ => []
  reference_generated := by
    apply (code mode).every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code mode).publicPrefix
  original := (code mode).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original

abbrev model (mode : Mode) : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨Distributed.Recall.Information.Regression.base, Distributed.Recall.Information.Regression.scope, source mode, rfl, rfl⟩
abbrev origin (mode : Mode) : Origin (model mode) where
  history := ⟨(source mode).history, (source mode).original⟩
  response := ⟨Reaction.restrict (code mode) (source mode).opponent, Reaction.restriction_is_generated _ _⟩
  side := .original
abbrev start (mode : Mode) := EventHistory.ofOrigin (model mode) 8 (origin mode)
abbrev environment (mode : Mode) : Opponent (code mode) := fun _ _ _ => none

def vote (mode : Mode) : Rule (code mode) where
  work := ⟨fun key _ => if key.1 = 0 then [yes] else [], by
    apply (code mode).every_local_policy_is_enumerated
    intro key inside
    apply (mem_words_iff _ _ _).mpr
    split <;> simp⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.activate 0, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

def send (mode : Mode) : Rule (code mode) where
  work := ⟨fun _ _ => [], by
    apply (code mode).every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.send 0 1, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

abbrev quiet (mode : Mode) : Rule (code mode) := SilentWindow.quiet
abbrev deliver (mode : Mode) : Opponent (code mode) := fun _ _ _ => some ⟨.deliver 0, by simp [code]⟩
abbrev beforeDelivery (mode : Mode) : List (EventHistory.Stage (code := code mode)) :=
  [(vote mode, environment mode), (quiet mode, environment mode), (quiet mode, environment mode),
    (quiet mode, environment mode), (send mode, environment mode)]
abbrev stages (mode : Mode) := beforeDelivery mode ++ [(quiet mode, deliver mode)]
abbrev duplicateStages := stages .normal ++ [(quiet .normal, environment .normal), (quiet .normal, deliver .normal)]

abbrev vocabulary := AttestationControls.vocabulary
abbrev slot : Scope := ⟨0, 0, 0⟩
abbrev ballot (mode : Mode) : StageBudget.Ballot (code := code mode) := ⟨0, 0, 0, false, slot, true, 1⟩
abbrev encoding (mode : Mode) : StageTransport.Encoding (code := code mode) :=
  fun reading => if reading = (if mode = .wrongWire then 2 else 1) then some (ballot mode) else none
abbrev law (mode : Mode) : StageReception.Law (code mode) := ⟨fun _ _ => slot, 1⟩
abbrev statement (mode : Mode) : RequestAttestation.Statement (code := code mode) := ⟨ballot mode, yes⟩
abbrev wire (mode : Mode) : StageTransport.Wire (code := code mode) := ⟨4, 0, 1, (if mode = .wrongWire then 2 else 1), 1, ballot mode⟩
abbrev confirmation (mode : Mode) : StageReception.Receipt (code := code mode) := ⟨wire mode, 5, 5⟩
abbrev receipt (mode : Mode) : RequestReadback.Receipt (code := code mode) := ⟨confirmation mode, statement mode, 1⟩
abbrev observed (mode : Mode) := RequestReadback.produce vocabulary (encoding mode) (law mode) (start mode) (stages mode) 1 6

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadbackSource
