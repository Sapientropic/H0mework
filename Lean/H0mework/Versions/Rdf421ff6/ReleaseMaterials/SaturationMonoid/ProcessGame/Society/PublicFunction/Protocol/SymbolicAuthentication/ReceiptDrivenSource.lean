import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRun
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EagerDelivery

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information Agency.Protocol Continuation
open RequestResponseSource (Mode)

abbrev Port := Mandate.Source.Port × Bool
abbrev Action := Request Bool Unit Port (Mandate.State Bool Unit) Unit
abbrev slot : Scope := ⟨0, 0, 0⟩
abbrev secondScope : Scope := ⟨0, 0, 1⟩

def yes : Action := ⟨false, [], (.resource, false), [], .use false [((), 1)] .external⟩
def phase : Action := ⟨false, [], (.resource, true), [], .use false [((), 1)] .external⟩
def positive : Action := ⟨true, [], (.resource, false), [], .use true [((), 1)] .external⟩
def phaseReply : Action := ⟨true, [], (.resource, true), [], .use true [((), 1)] .external⟩

-- Two registered external resource channels preserve the native service and
-- challenge ports. A protocol phase never supplies a native delegation.
def base : RawLaw Bool Unit Port Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun technology port => Distributed.Recall.Information.Regression.base.controller technology port.1
  allowed := fun _ port _ => decide (port.1 = .resource)
  stockPort := fun _ _ _ => (.resource, false)
  revisionPort := fun _ => (.challenge, false)
  revisionCost := Distributed.Recall.Information.Regression.base.revisionCost
  settlementUnit := Distributed.Recall.Information.Regression.base.settlementUnit
  settlementRate := Distributed.Recall.Information.Regression.base.settlementRate
  issuerPort := fun _ => (.resource, false)
  necessities := Distributed.Recall.Information.Regression.base.necessities
  mandatoryMaintenance := Distributed.Recall.Information.Regression.base.mandatoryMaintenance
  duration := Distributed.Recall.Information.Regression.base.duration

abbrev scope : Mandate.Scope (Party := Bool) (Good := Unit) (Port := Port) :=
  ⟨Distributed.Recall.Information.Regression.task, (.service, false), (.challenge, false), by decide, [((), 1)]⟩

def liftRequest (request : Mandate.Source.Action) : Action :=
  ⟨request.signer, request.consents, (request.purpose, false), request.gates.map (fun port => (port, false)), request.operation⟩

abbrev vocabulary : OwnedAttestation.Vocabulary (Party := Bool) (Good := Unit) (Port := Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨(fun port => if port.1 = .resource then some ((if port.2 then secondScope else slot), true) else none), fun _ => 0, ()⟩

-- Both serializations read the sender's own stock after the original paid
-- bootstrap. The source statements are generated before either send.
abbrev code (mode : Mode) : Code Bool Unit Port (Mandate.State Bool Unit) Unit where
  law := Mandate.law base scope
  initial := (RequestResponseSource.code mode).initial
  bootstrap := (RequestResponseSource.code mode).bootstrap.map liftRequest
  task := scope.task
  actions := [yes, phase, positive, phaseReply]
  actionLimit := 2
  sites := 2
  signals := 5
  initialSignal := 0
  siteParty := fun site => decide (site = 1)
  memoryReady := fun reading => decide (reading.val < 3) && !(mode == Mode.unreadable && reading == 1)
  readLocal := fun _ snapshot => if mode = Mode.wrongWire then 2 else if 5 ≤ snapshot.stock () then 1 else 2
  afterAction := fun site old _ => if site = 1 ∧ old = 2 then 4 else 3
  afterSend := fun _ _ _ _ => 0
  afterDelivery := fun _ _ old reading =>
    if old = 4 ∨ (old = 3 ∧ reading = 1) then old
    else if mode = Mode.erased then 0 else if mode = Mode.rewritten then 2 else reading
  sendCost := fun _ _ => [yes]
  deliveryCost := fun _ => [positive]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0, .activate 1, .send 0 1, .deliver 0, .deliver 1]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro party; cases party <;> simp
  goods_cover := by intro good; cases good; simp
  instruments_cover := by intro instrument; cases instrument; simp

abbrev source (mode : Mode) : Machine Bool Unit Port (Mandate.State Bool Unit) Unit where
  code := code mode
  reference := fun _ _ => []
  reference_generated := by
    apply (code mode).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code mode).publicPrefix
  original := (code mode).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original

abbrev model (mode : Mode) : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨base, scope, source mode, rfl, rfl⟩

def start (mode : Mode) (budget : Nat) : Cursor (code mode) :=
  ⟨(source mode).reference, (source mode).reference_generated, (source mode).history, (source mode).original,
    (source mode).opponent, (source mode).side, ⟨fun _ _ _ => none, budget⟩, [], 0, (source mode).history.length + 1⟩

def vote (mode : Mode) : Rule (code mode) where
  work := ⟨fun key _ => if key.1 = 0 then [yes, phase] else [], by
    apply (code mode).every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    split <;> simp⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.activate 0, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

def send (mode : Mode) : Rule (code mode) where
  work := ⟨fun _ _ => [], by
    apply (code mode).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.send 0 1, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove (code mode) 0)
    else ⟨none, List.mem_cons_self⟩

abbrev quiet (mode : Mode) : Rule (code mode) := SilentWindow.quiet
def programme (mode : Mode) : List (Rule (code mode)) :=
  [vote mode, quiet mode, quiet mode, quiet mode, send mode, quiet mode,
    quiet mode, quiet mode, send mode, quiet mode, quiet mode, quiet mode]

abbrev law (mode : Mode) : StageReception.Law (code mode) :=
  ⟨fun _ current => if 4 ≤ current.stock false () then slot else secondScope, 3⟩
abbrev firstBallot (mode : Mode) : StageBudget.Ballot (code := code mode) := ⟨0, 0, 0, false, slot, true, 1⟩
abbrev secondBallot (mode : Mode) : StageBudget.Ballot (code := code mode) := ⟨0, 1, 0, false, secondScope, true, 1⟩
abbrev encoding (mode : Mode) : StageTransport.Encoding (code := code mode) :=
  fun signal => if signal = 1 then some (firstBallot mode) else if signal = 2 then some (secondBallot mode) else none

@[irreducible] def actual (mode : Mode) := ReceiptDrivenRun.produce (model mode) (start mode 16) vocabulary
  (encoding mode) (law mode) 1 (programme mode) (EagerDelivery.callback (start mode 16))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenSource
