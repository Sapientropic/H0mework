import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplySource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open Repayment.Recovery (Good)

def code : Code Party Good Port (Mandate.State Party Bool) Unit where
  law := WholeCursorLaw.law
  initial := WholeCursorLaw.initial
  bootstrap := [issue]
  task := WholeCursorLaw.task
  actions := [ballot]
  actionLimit := 1
  sites := 1
  signals := 2
  initialSignal := 0
  siteParty := fun _ => producer
  readLocal := fun _ _ => 1
  sendCost := fun _ _ => [charge]
  deliveryCost := fun _ => [charge]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0,.send 0 0,.deliver 0]
  eventLimit := 0
  eligible := fun _ => true
  parties := [.inl 0,.inl 1,.inl 2,supplier]
  goods := [.feedstock,.service,.waste,.energy,.labor]
  instruments := [()]
  parties_cover := by intro actor;cases actor with
                     | inl actor => fin_cases actor <;> simp
                     | inr actor => cases actor;simp [supplier]
  goods_cover := by intro good;cases good <;> simp
  instruments_cover := by intro instrument;cases instrument;simp

def idle : code.Policy := fun _ _ => []
def paid : code.Policy := fun _ _ => [ballot]
theorem idle_generated : idle ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [idle])
theorem paid_generated : paid ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [paid,code])

def activation (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.activate site,by fin_cases site;decide +kernel⟩,by fin_cases site;decide +kernel⟩
def sending (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.send site site,by fin_cases site;decide +kernel⟩,by fin_cases site;decide +kernel⟩
def vote : Rule code := ⟨⟨paid,paid_generated⟩,fun key _ => activation key.1⟩
def send : Rule code := ⟨⟨idle,idle_generated⟩,fun key _ => sending key.1⟩
abbrev quiet : Rule code := SilentWindow.quiet
abbrev silent : Opponent code := EventStep.fixed none

def emitter : Machine Party Good Port (Mandate.State Party Bool) Unit where
  code := code
  reference := idle
  reference_generated := idle_generated
  history := code.publicPrefix
  original := code.public_prefix_is_an_actual_generated_history
  opponent := silent
  side := .original

def originalBound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Bool) (Instrument := Unit) := ⟨base,scope,emitter,rfl,rfl⟩
def initialCursor : Cursor code :=
  ⟨emitter.reference,emitter.reference_generated,emitter.history,emitter.original,emitter.opponent,
    .original,⟨fun _ _ _ => none,6⟩,[],0,emitter.history.length+1⟩
def past : List (EventHistory.Stage (code := code)) := [(vote,silent),(quiet,silent),(send,silent),(quiet,silent)]
abbrev pending := EventHistory.execute initialCursor past

def slot : Scope := ⟨0,0,0⟩
def vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Bool) (Instrument := Unit) :=
  ⟨fun purpose => if purpose = ballotPort then some (slot,true) else none,
    fun current => current.technology.version,.service⟩
def ballotBody : StageBudget.Ballot (code := code) := ⟨0,0,⟨0,by decide⟩,producer,slot,true,1⟩
def encoding : StageTransport.Encoding (code := code) := fun signal => if signal.val = 1 then some ballotBody else none
def priorReception : StageReception.Law code := ⟨fun _ _ => slot,3⟩
abbrev origin := CatalogueHandoffConsumer.remember initialCursor past vocabulary encoding ⟨0,by decide⟩ priorReception

abbrev position : Repayment.Position Party Unit := ⟨(),producer,creditor⟩
variable (saved : Cursor code)
abbrev current := (EventStep.seed saved).current
-- Every already-sent packet keeps its original fee word in this reserve.
def feeWord : List Action := ((EventStep.seed saved).frame.sent.map fun packet => code.deliveryCost packet.recipient).flatten
def reserve : ℚ := max 0 (((feeWord saved).map fun request => flowAt (code.law.debit (current saved) request) producer .service).sum)
def cycles : Nat := ⌈max 0 ((Repayment.balance position (current saved) + reserve saved -
  (current saved).stock producer .service) / 3)⌉₊
def front : List Action := (List.replicate (cycles saved) cycle).flatten
abbrev intermediate := (code.law.execute (current saved) 0 (front saved)).final
def batch : List Action := front saved ++ Repayment.candidate code.law position (intermediate saved)
abbrev active := AtomicWorkSource.code code (batch saved)
abbrev start := AtomicWorkSource.cursor code (batch saved) saved
abbrev work (submit : Bool) := AtomicWorkSource.protocol code (batch saved) submit
abbrev row (submit : Bool) (rival : Opponent (active saved)) := AtomicWorkSource.row code (batch saved) saved submit rival
abbrev after (submit : Bool) (rival : Opponent (active saved)) := AtomicWorkSource.next code (batch saved) saved submit rival
abbrev assess (submit : Bool) (rival : Opponent (active saved)) := AtomicWorkSource.assess code (batch saved) saved submit rival

def bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Bool) (Instrument := Unit) := ⟨base,scope,(start saved).source,rfl,rfl⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplySource
