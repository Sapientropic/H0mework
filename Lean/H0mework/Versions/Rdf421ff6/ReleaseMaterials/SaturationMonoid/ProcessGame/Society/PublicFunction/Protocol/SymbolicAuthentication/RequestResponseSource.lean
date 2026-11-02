import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadbackSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseSource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information Agency.Protocol Continuation

inductive Mode where
  | normal | erased | rewritten | unreadable | wrongWire | unpaidSend | unpaidDelivery | noReply | poor
  deriving DecidableEq

def transportMode : Mode → RequestReadbackSource.Mode
  | .erased => .erased
  | .rewritten => .rewritten
  | .unreadable => .unreadable
  | .wrongWire => .wrongWire
  | .unpaidSend => .unpaidSend
  | .unpaidDelivery => .unpaidDelivery
  | _ => .normal

abbrev yes := RequestReadbackSource.yes
abbrev no := RequestReadbackSource.no
abbrev positive := RequestReadbackSource.receiveFee
def negative : Mandate.Source.Action := ⟨true, [], .challenge, [], .use true [((), 1)] .external⟩

abbrev code (mode : Mode) : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {RequestReadbackSource.code (transportMode mode) with
    initial := { (RequestReadbackSource.code (transportMode mode)).initial with
      stock := fun party _ => if party && mode == .poor then 1 else 10 }
    actions := [yes, no] ++ if mode = .noReply then [] else [positive, negative]
    signals := 4
    initialSignal := 0
    memoryReady := fun reading => decide (reading ≠ 3) && !(mode == .unreadable && reading == 1)
    readLocal := fun _ _ => if mode = .wrongWire then 2 else 1
    afterSend := fun _ _ old _ => old
    afterAction := fun _ _ _ => 3
    afterDelivery := fun _ _ old reading => if old = 3 then 3 else
      if mode = .erased then 0 else if mode = .rewritten then 2 else reading}

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
    split
    · simp
    · simp⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.activate 0, by simp [code, RequestReadbackSource.code]⟩,
      by simp [ownMoves, code, RequestReadbackSource.code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

def send (mode : Mode) : Rule (code mode) where
  work := ⟨fun _ _ => [], by
    apply (code mode).every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.send 0 1, by simp [code, RequestReadbackSource.code]⟩,
      by simp [ownMoves, code, RequestReadbackSource.code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

abbrev quiet (mode : Mode) : Rule (code mode) := SilentWindow.quiet
abbrev deliver (mode : Mode) : Opponent (code mode) := fun _ _ _ => some ⟨.deliver 0, by simp [code, RequestReadbackSource.code]⟩
abbrev stages (mode : Mode) : List (EventHistory.Stage (code := code mode)) :=
  [(vote mode, environment mode), (quiet mode, environment mode), (quiet mode, environment mode),
    (quiet mode, environment mode), (send mode, environment mode), (quiet mode, deliver mode)]
abbrev beforeResponse (mode : Mode) := EventHistory.execute (start mode) (stages mode)
abbrev full (mode : Mode) := RequestResponse.produce (start mode) (stages mode) (environment mode)
abbrev final (mode : Mode) := EventHistory.execute (start mode) (full mode)
abbrev row (mode : Mode) := StageTrace.material (beforeResponse mode) RequestResponse.protocol (environment mode)
abbrev vocabulary := RequestReadbackSource.vocabulary
abbrev slot := RequestReadbackSource.slot
abbrev ballot (mode : Mode) : StageBudget.Ballot (code := code mode) := ⟨0, 0, 0, false, slot, true, 1⟩
abbrev responseBallot (mode : Mode) : StageBudget.Ballot (code := code mode) := ⟨6, 0, 1, true, slot, true, 1⟩
abbrev encoding (mode : Mode) : StageTransport.Encoding (code := code mode) :=
  fun reading => if reading = (if mode = .wrongWire then 2 else 1) then some (ballot mode) else none
abbrev law (mode : Mode) : StageReception.Law (code mode) := ⟨fun _ _ => slot, 1⟩
abbrev statement (mode : Mode) : RequestAttestation.Statement (code := code mode) := ⟨ballot mode, yes⟩
abbrev responseStatement (mode : Mode) : RequestAttestation.Statement (code := code mode) := ⟨responseBallot mode, positive⟩
abbrev recovery (mode : Mode) := RequestReadback.produce vocabulary (encoding mode) (law mode) (start mode) (full mode) 1 (full mode).length

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseSource
