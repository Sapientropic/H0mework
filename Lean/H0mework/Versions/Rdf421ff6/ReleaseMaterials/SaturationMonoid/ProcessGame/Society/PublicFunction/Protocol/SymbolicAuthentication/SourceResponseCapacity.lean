import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseCapacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceResponseCapacity

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

def actionCheck : Bool := code.keys.all fun key =>
  (words code.actions code.actionLimit).all fun word => decide
    (code.memoryReady (code.afterAction key.1 key.2 word) = false)

def sendCheck : Bool := code.keys.all fun key =>
  (List.finRange code.sites).all fun recipient => (List.finRange code.signals).all fun reading => decide
    (code.memoryReady key.2 = false → code.memoryReady (code.afterSend key.1 recipient key.2 reading) = false)

def deliveryCheck : Bool := code.keys.all fun key =>
  (List.finRange code.sites).all fun sender => (List.finRange code.signals).all fun reading => decide
    (code.memoryReady key.2 = false → code.memoryReady (code.afterDelivery key.1 sender key.2 reading) = false)

def inspect : Bool := actionCheck code && sendCheck code && deliveryCheck code

omit [DecidableEq Port] [DecidableEq Technology] in
theorem checked_source_generates_its_absorption_law (accepted : inspect code = true) : ResponseCapacity.Absorbing code := by
  have checks : actionCheck code = true ∧ sendCheck code = true ∧ deliveryCheck code = true := by
    simpa [inspect, and_assoc] using accepted
  refine ⟨?_, ?_, ?_⟩
  · intro site old word supported
    exact of_decide_eq_true ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.1) (site, old) (code.key_mem _))) word supported)
  · intro sender recipient old reading spent
    exact (of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.2.1) (sender, old) (code.key_mem _))) recipient (List.mem_finRange _)))
        reading (List.mem_finRange _))) spent
  · intro recipient sender old reading spent
    exact (of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.2.2) (recipient, old) (code.key_mem _))) sender (List.mem_finRange _)))
        reading (List.mem_finRange _))) spent

def generate (cursor : Cursor code) : Option Nat :=
  if inspect code then some (ResponseCapacity.rank cursor) else none

theorem generated_capacity_pays_for_every_actual_extension
    (cursor : Cursor code) (capacity : Nat) (made : generate code cursor = some capacity)
    (stages : List (EventHistory.Stage (code := code))) :
    ResponseCapacity.count cursor stages + ResponseCapacity.rank (EventHistory.execute cursor stages) ≤ capacity ∧
      capacity ≤ code.sites := by
  unfold generate at made
  split at made
  · rename_i accepted
    cases Option.some.inj made
    have source := checked_source_generates_its_absorption_law code accepted
    exact ⟨ResponseCapacity.the_actual_source_pays_for_every_productive_response source cursor stages,
      (ResponseCapacity.response_count_is_bounded_by_the_actual_initial_memory source cursor stages).2⟩
  · contradiction

variable {code}

theorem exhausted_capacity_closes_the_local_response_gate
    (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
    (empty : ResponseCapacity.rank (EventHistory.execute start past) = 0)
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (observedAt : Nat) (site : Fin code.sites) :
    ReceivedStatementAuthentication.work vocabulary encoding law start (past.map Prod.fst) observedAt
      (ReceivedStatementAuthentication.remembered start past observedAt site) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = [] := by
  have vacant := Finset.card_eq_zero.mp empty
  have unready : code.memoryReady ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = false := by
    by_contra missing
    have ready : code.memoryReady ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = true := by
      cases value : code.memoryReady ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) <;> simp_all
    have inside : site ∈ ResponseCapacity.available (EventStep.seed (EventHistory.execute start past)).frame := by
      simp [ResponseCapacity.available, ready]
    rw [vacant] at inside
    exact Finset.notMem_empty _ inside
  have noRead : RequestReadback.localRead (code := code)
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = none := by
    simp only [RequestReadback.localRead, unready, Bool.false_eq_true, if_false]
  have noWork := RequestResponse.missing_local_content_produces_no_work site _ noRead
  simp only [ReceivedStatementAuthentication.work, noWork, if_true]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceResponseCapacity
