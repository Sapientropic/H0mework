import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open WorkerInputSource
open MaterialRoundSource (Bound)
variable (old : Bound) (count : Nat)

theorem actual_upstream_inputs_are_consumed_once_by_the_original_fuel_and_service_producer
    (same : old.source.code.law = WorkerInputLaw.law)
    (needed : Needed (before old count)) (inputs : WorkerInputLaw.Inputs (before old count)) :
    let finish := MaterialRoundSource.prepared (arrived old count) (count+1) (nextArrival old count)
    finish.stock 0 .energy = (before old count).stock 0 .energy-1 ∧
      finish.stock 0 .labor = (before old count).stock 0 .labor-1 ∧
      finish.stock 1 .waste = (before old count).stock 1 .waste-1 ∧
      finish.stock 1 .service = (before old count).stock 1 .service+3 ∧
      finish.stock 2 .waste = (before old count).stock 2 .waste ∧
      finish.stock 2 .energy = (before old count).stock 2 .energy ∧
      finish.stock 2 .labor = (before old count).stock 2 .labor ∧
      finish.claims = (before old count).claims ∧ finish.technology = (before old count).technology := by
  have upstream := a_funded_actual_deficit_generates_the_worker_inputs old count same needed inputs
  have next := FuelMaterialSource.source_generated_fuel_is_consumed_by_the_actual_service_recovery
    (arrived old count) (count+1) same upstream.2.2.1
  have endpoint : MaterialRoundSource.before (arrived old count) (count+1) = WorkerInputLaw.successor (before old count) := upstream.2.1
  rw [next.2.1,endpoint]
  simp [RenewedQuorumMaterial.successor,FuelMandateLaw.successor,WorkerInputLaw.successor]

theorem every_upstream_attempt_keeps_original_accounts_and_its_own_whole_ledger_and_next :
    let runtime := (Native.Runtime.facade (arrived old count).source).seed.advance (MaterialRoundSource.depth old count+1)
    (∀ ordinal ≤ MaterialRoundSource.depth old count+1,
      Native.Coupling.Match old.source.code old.source.input (arrived old count).source.input
        (Financial.accountAt old.source.input ordinal) (Financial.accountAt (arrived old count).source.input ordinal)) ∧
      (produce old count).upstream = Native.Authority.fullGenerate (arrived old count) (MaterialRoundSource.depth old count) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (Native.Runtime.facade (arrived old count).source).process.stateAt
        ((Native.Runtime.facade (arrived old count).source).process.successor runtime.state) := by
  have rooted := (Native.Runtime.facade (arrived old count).source).readoutAt_factorizes
    ((Native.Runtime.facade (arrived old count).source).seed.advance (MaterialRoundSource.depth old count+1)) .responsibilities
  exact ⟨fun ordinal earlier => Machine.Continuation.complete_financial_prefix old.source count _ ordinal earlier,
    rfl,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputConsumer
