import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceDynamicCache

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (bound base laws contract)
open ProductiveSigningSource (current total)
noncomputable section

def originalCode := bound.source.code
abbrev State := JointReceptionSource.State originalCode
def start : State := ConcreteProductiveSource.endpoint
def recycling := {contract with acceptance := RecycledQuorumMaterial.recycle}
def feeding := {contract with acceptance := RecycledQuorumMaterial.feed}

structure Control where
 recycle : Bool
 payFeed : Bool
 deliverFeed : Bool
 payInvocation : Bool
 acceptInvocation : Bool
 deriving DecidableEq

def needsFuel (state : State) : Bool := decide ((current state).stock 1 .feedstock<2)

-- Refusing credit retains an external action that actually consumed its inputs.
def donated (state : State) (control : Control) : State :=
 if needsFuel state then JointReceptionSource.advance recycling state (.renew false control.recycle) else state

def supplied (state : State) (control : Control) : State :=
 if needsFuel state then JointReceptionSource.advance feeding (donated state control)
  (.renew control.payFeed control.deliverFeed) else state

def ready (state : State) (control : Control) : State :=
 JointReceptionSource.advance contract (supplied state control) (.execute [.command 2,.idle])

def request (control : Control) := {ConcreteProductiveSource.request with
 enabled := control.payInvocation,accept := control.acceptInvocation}

def step (state : State) (control : Control) : State :=
 FreshSigningSource.cycle contract base laws (ready state control) (request control)

abbrev candidate (state : State) (control : Control) :=
 (SourceRepairSearch.cases contract 0 (ready state control)).head (by simp [SourceRepairSearch.cases])

inductive Status where
 | productive | blocked
 deriving DecidableEq

def status (state : State) (control : Control) : Status :=
 if ProductiveSigningSource.accepts contract base laws (request control) .service 3 1 state
  (candidate state control) then .productive else .blocked

def run (state : State) (control : Nat → State → Control) : Nat → State :=
 Nat.rec state fun ordinal current => step current (control ordinal current)

def net (state : State) (control : Control) : ℚ := total (step state control) .service-total state .service

def accumulated (state : State) (control : Nat → State → Control) : Nat → ℚ :=
 Nat.rec 0 fun ordinal previous => previous+net (run state control ordinal) (control ordinal (run state control ordinal))

abbrev cooperative : Control := ⟨true,true,true,true,true⟩
abbrev withheld : Control := {cooperative with recycle := false}
abbrev undelivered : Control := {cooperative with deliverFeed := false}

abbrev prior := FreshSigningSource.prepared contract ConcreteProductiveSource.ready ConcreteProductiveSource.request
def snapshot := SourceDynamicCache.Fresh.generated base laws prior ConcreteProductiveSource.request
def material := snapshot.before.current
abbrev refuelingWord := [RecycledQuorumMaterial.recycle,RecycledQuorumMaterial.waste,RecycledQuorumMaterial.feed]

def refuelingOffer (control : Control) : Option (List RecycledQuorumMaterial.Action) :=
 if control.recycle && control.payFeed && control.deliverFeed &&
  decide (∀ item∈bound.source.code.law.rawItems material refuelingWord,
   bound.source.code.law.Valid item.before item.request) then some refuelingWord else none

theorem the_generated_current_offers_the_original_refueling_word :
 refuelingOffer cooperative=some refuelingWord := by decide +kernel

theorem the_refueling_word_replenishes_the_worker_from_real_provider_inputs :
 (bound.source.code.law.next material refuelingWord).stock 1 .feedstock=2 ∧
 (bound.source.code.law.next material refuelingWord).stock 2 .energy=3 ∧
 (bound.source.code.law.next material refuelingWord).stock 2 .labor=3 := by
 and_intros <;> decide +kernel

theorem withholding_the_actual_supplier_removes_the_offer : refuelingOffer withheld=none := rfl
theorem withholding_the_actual_feed_removes_the_offer : refuelingOffer undelivered=none := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveSource
