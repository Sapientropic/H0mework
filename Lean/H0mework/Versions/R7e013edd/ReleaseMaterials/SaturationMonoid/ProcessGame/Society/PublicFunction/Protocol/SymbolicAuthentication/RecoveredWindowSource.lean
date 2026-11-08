import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceWindowCache

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecoveredProductiveSource (snapshot prior recycling feeding)
noncomputable section

def model := prior.actual.model
def origin : Cursor model.source.code := snapshot.cursor
def before : Feedback.State model.source.code := snapshot.before
def donatedPoint := SourceWindowCache.point model.source.code recycling origin before false true
def donated := SourceWindowCache.after model.source.code recycling origin before false true
def suppliedPoint := SourceWindowCache.point (PaidInvocationSource.code model.source.code recycling)
 feeding donatedPoint donated true true
def supplied := SourceWindowCache.after (PaidInvocationSource.code model.source.code recycling)
 feeding donatedPoint donated true true

theorem the_unpaid_supplier_attempt_cannot_mint_a_window :
 SourceWindowCache.admitted model.source.code recycling origin before false true=false := by decide +kernel

theorem the_refused_window_still_records_the_actual_supplier_action :
 (SourceWindowCache.delivery model.source.code recycling origin before false true).submitted=
 [RecycledQuorumMaterial.recycle] := by decide +kernel

theorem the_real_waste_payment_and_feed_delivery_generate_a_window :
 SourceWindowCache.admitted (PaidInvocationSource.code model.source.code recycling)
 feeding donatedPoint donated true true=true := by decide +kernel

theorem the_two_actual_windows_replenish_from_the_original_provider :
 supplied.current.stock 1 .feedstock=2 ∧ supplied.current.stock 2 .energy=3 ∧
 supplied.current.stock 2 .labor=3 ∧ supplied.remaining=donated.remaining-2+feeding.steps := by
 and_intros <;> decide +kernel

theorem removing_delivery_cannot_generate_a_window :
 SourceWindowCache.admitted (PaidInvocationSource.code model.source.code recycling)
 feeding donatedPoint donated true false=false := by decide +kernel

theorem removing_payment_cannot_generate_a_window :
 SourceWindowCache.admitted (PaidInvocationSource.code model.source.code recycling)
 feeding donatedPoint donated false true=false := by decide +kernel

theorem a_wrong_provider_cannot_generate_a_window :
 SourceWindowCache.admitted (PaidInvocationSource.code model.source.code recycling)
  {feeding with provider := 1} donatedPoint donated true true=false := by decide +kernel

theorem the_two_attempts_keep_all_claims_and_charge_the_actual_clock :
 (∀ instrument debtor creditor,
  supplied.current.claims instrument debtor creditor=before.current.claims instrument debtor creditor) ∧
 supplied.current.clock=before.current.clock+4 := by
 and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowSource
