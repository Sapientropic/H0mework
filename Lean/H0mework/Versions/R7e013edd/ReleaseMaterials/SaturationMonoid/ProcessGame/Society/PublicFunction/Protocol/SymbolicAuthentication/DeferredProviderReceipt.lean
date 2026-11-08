import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderReceipt
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open DeferredProviderSource
noncomputable section

def payment := SourceWindowCache.payment SourceCreditSource.creditModel.source.code SourceCreditSource.exchange
 SourceCreditSource.issued.cursor SourceCreditSource.issued.before true
def bill := PaidInvocationSource.quote SourceCreditSource.creditModel.source.code SourceCreditSource.exchange
 SourceCreditSource.issued.cursor true

def externalAcceptance (row : StageTrace.Record (code := model.source.code)) : Bool :=
 match row.call with
 | .external (some event) => decide (event.val=.adversary SourceCreditSource.exchange.acceptance)
 | _ => false

def eligible (row : StageTrace.Record (code := model.source.code)) : Bool := decide (
 payment.submitted=[SourceCreditSource.exchange.payment] ∧
 SourceCreditSource.exchange.payment.signer=SourceCreditSource.exchange.payer ∧
 SourceCreditSource.exchange.acceptance.signer=SourceCreditSource.exchange.provider ∧
 (∀ item∈StageTrace.items payment,model.source.code.law.Valid item.before item.request) ∧
 0<SourceCreditSource.exchange.units ∧
 flowAt (model.source.code.law.actualDebit payment.before.current SourceCreditSource.exchange.payment)
  SourceCreditSource.exchange.payer SourceCreditSource.exchange.unit=SourceCreditSource.exchange.units ∧
 flowAt (model.source.code.law.actualCredit payment.before.current SourceCreditSource.exchange.payment)
  SourceCreditSource.exchange.provider SourceCreditSource.exchange.unit=SourceCreditSource.exchange.units ∧
 bill.origin=payment.cursor.cut ∧ payment.cursor.cut<row.cursor.cut ∧ externalAcceptance row=true ∧
 row.submitted=[SourceCreditSource.exchange.acceptance] ∧
 (∀ item∈StageTrace.items row,model.source.code.law.Valid item.before item.request))

structure Receipt (allow : Bool) where
 private mk ::
 row : StageTrace.Record (code := model.source.code)
 actual : row∈(recovery allow).rows
 matched : eligible row=true

inductive Result (allow : Bool) where
 | pending
 | completed (receipt : Receipt allow)

def produce (allow : Bool) : Result allow :=
 match found : (recovery allow).rows.find? eligible with
 | none => .pending
 | some row => .completed ⟨row,List.mem_of_find?_eq_some found,List.find?_some found⟩

def origins (allow : Bool) := ((recovery allow).rows.filter eligible).map fun row => (bill.origin,row.cursor.cut)

theorem every_completed_receipt_keeps_both_actual_paid_origins (allow : Bool) (receipt : Receipt allow) :
 receipt.row∈(recovery allow).rows ∧
 payment.submitted=[SourceCreditSource.exchange.payment] ∧
 SourceCreditSource.exchange.payment.signer=SourceCreditSource.exchange.payer ∧
 SourceCreditSource.exchange.acceptance.signer=SourceCreditSource.exchange.provider ∧
 (∀ item∈StageTrace.items payment,model.source.code.law.Valid item.before item.request) ∧
 0<SourceCreditSource.exchange.units ∧
 flowAt (model.source.code.law.actualDebit payment.before.current SourceCreditSource.exchange.payment)
  SourceCreditSource.exchange.payer SourceCreditSource.exchange.unit=SourceCreditSource.exchange.units ∧
 flowAt (model.source.code.law.actualCredit payment.before.current SourceCreditSource.exchange.payment)
  SourceCreditSource.exchange.provider SourceCreditSource.exchange.unit=SourceCreditSource.exchange.units ∧
 bill.origin=payment.cursor.cut ∧ payment.cursor.cut<receipt.row.cursor.cut ∧ externalAcceptance receipt.row=true ∧
 receipt.row.submitted=[SourceCreditSource.exchange.acceptance] ∧
 (∀ item∈StageTrace.items receipt.row,model.source.code.law.Valid item.before item.request) :=
 ⟨receipt.actual,of_decide_eq_true receipt.matched⟩

theorem actual_late_participation_generates_a_completed_receipt :
 (∃ receipt,produce true=.completed receipt) ∧ (origins true).length=1 := by
 constructor
 · unfold produce
   split
   · rename_i missing
     have present : ((recovery true).rows.find? eligible).isSome=true := by decide +kernel
     rw [missing] at present
     contradiction
   · exact ⟨_,rfl⟩
 · decide +kernel

theorem absence_of_actual_acceptance_keeps_the_receipt_pending : produce false=.pending := by
 unfold produce
 split
 · rfl
 · rename_i row found
   have absent : (recovery false).rows.find? eligible=none := by decide +kernel
   rw [absent] at found
   contradiction

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderReceipt
