import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Current)
open WorkerInputSource

def initial (energy labor waste worker : Nat) : Current where
  stock := fun party good =>
    if party = 0 ∧ good = .energy then energy
    else if party = 0 ∧ good = .labor then labor
    else if party = 1 ∧ good = .waste then waste
    else if party = 2 ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then worker else 0
  claims := fun _ _ _ => 0
  technology := ⟨true,0,none,none,none⟩
  clock := 0
  round := 0
abbrev code (released : Bool) (energy labor waste worker : Nat) :=
  {FuelMaterialControls.code released 0 with initial := initial energy labor waste worker}
abbrev source (released : Bool) (energy labor waste worker : Nat) :
    Machine Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
      (Mandate.State Delegation.Funded.Party Bool) Unit where
  code := code released energy labor waste worker
  reference := fun _ _ => []
  reference_generated := by
    apply (code released energy labor waste worker).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code released energy labor waste worker).publicPrefix
  original := (code released energy labor waste worker).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev bound (released : Bool) (energy labor waste worker : Nat) : MaterialRoundSource.Bound :=
  ⟨FuelMandateLaw.base released,Repayment.Recovery.scope,source released energy labor waste worker,rfl,rfl⟩
abbrev funded := bound true 1 2 2 0
abbrev readySource := arrived funded 0
abbrev arrival := nextArrival funded 0

theorem an_empty_worker_receives_real_upstream_inputs_before_new_fuel_and_service :
    Needed (before funded 0) ∧ WorkerInputLaw.Inputs (before funded 0) ∧
      incoming funded 0 = WorkerInputLaw.word ∧
      (afterInput funded 0).stock 0 .energy = 0 ∧ (afterInput funded 0).stock 0 .labor = 1 ∧
      (afterInput funded 0).stock 1 .waste = 1 ∧ (afterInput funded 0).stock 2 .waste = 1 ∧
      (afterInput funded 0).stock 2 .energy = 1 ∧ (afterInput funded 0).stock 2 .labor = 1 ∧
      (afterInput funded 0).claims () 1 2 = 7 ∧
      (MaterialRoundSource.inspect readySource 1 arrival).isSome = true := by decide +kernel

def entry := (MaterialRoundSource.inspect readySource 1 arrival).get
  an_empty_worker_receives_real_upstream_inputs_before_new_fuel_and_service.2.2.2.2.2.2.2.2.2.2
abbrev completed := MaterialRoundSource.actual readySource 1 arrival entry

theorem primitive_inputs_call_the_uniform_actual_producer :
    let finish := MaterialRoundSource.prepared readySource 1 arrival
    finish.stock 0 .energy = (before funded 0).stock 0 .energy-1 ∧
      finish.stock 0 .labor = (before funded 0).stock 0 .labor-1 ∧
      finish.stock 1 .waste = (before funded 0).stock 1 .waste-1 ∧
      finish.stock 1 .service = (before funded 0).stock 1 .service+3 ∧
      finish.stock 2 .waste = (before funded 0).stock 2 .waste ∧
      finish.stock 2 .energy = (before funded 0).stock 2 .energy ∧
      finish.stock 2 .labor = (before funded 0).stock 2 .labor ∧
      finish.claims = (before funded 0).claims ∧ finish.technology = (before funded 0).technology :=
  WorkerInputConsumer.actual_upstream_inputs_are_consumed_once_by_the_original_fuel_and_service_producer
    funded 0 rfl an_empty_worker_receives_real_upstream_inputs_before_new_fuel_and_service.1
      an_empty_worker_receives_real_upstream_inputs_before_new_fuel_and_service.2.1

theorem actual_input_payments_are_consumed_by_a_new_authenticated_quorum :
    status funded 0 = .decided true ∧ (MaterialRoundSource.before completed 6).claims () 1 2 = 6 ∧
      (MaterialRoundSource.before completed 6).stock 1 .service = 0 ∧
      (MaterialRoundSource.before completed 6).stock 2 .waste = 0 ∧
      (MaterialRoundSource.before completed 6).stock 2 .energy = 0 ∧
      (MaterialRoundSource.before completed 6).stock 2 .labor = 0 ∧
      (MaterialRoundSource.before completed 6).stock 0 .energy = 0 ∧
      (MaterialRoundSource.before completed 6).stock 0 .labor = 1 := by decide +kernel

theorem individual_missing_inputs_and_closed_permission_are_real_refusals :
    incoming (bound true 0 2 2 0) 0 = [] ∧ status (bound true 0 2 2 0) 0 = .phaseRefused ∧
      incoming (bound true 1 1 2 0) 0 = [] ∧ status (bound true 1 1 2 0) 0 = .phaseRefused ∧
      incoming (bound true 1 2 1 0) 0 = [] ∧ status (bound true 1 2 1 0) 0 = .phaseRefused ∧
      status (bound false 1 2 2 0) 0 = .historyRefused := by decide +kernel

theorem stocked_workers_skip_upstream_debits_and_still_use_the_original_quorum :
    incoming (bound true 0 1 1 1) 0 = [] ∧ status (bound true 0 1 1 1) 0 = .decided true := by decide +kernel

abbrev tampered : List RecycledQuorumMaterial.Action :=
  [{WorkerInputLaw.energyLabor with signer := 2},WorkerInputLaw.waste]
abbrev replayed := WorkerInputLaw.word ++ WorkerInputLaw.word
abbrev attempted (raw : List RecycledQuorumMaterial.Action) : MaterialRoundSource.Bound :=
  ⟨funded.base,funded.scope,Machine.Continuation.extend funded.source 0 raw,rfl,rfl⟩
theorem deleting_impersonating_or_replaying_upstream_inputs_cannot_mint_completion :
    FuelMaterialSource.status funded 0 = .phaseRefused ∧
      FuelMaterialSource.status (attempted tampered) 1 = .historyRefused ∧
      (MaterialRoundSource.before (attempted tampered) 1).stock 0 .energy = 1 ∧
      FuelMaterialSource.status (attempted replayed) 1 = .historyRefused ∧
      (MaterialRoundSource.before (attempted replayed) 1).stock 0 .energy = 0 := by decide +kernel

abbrev emitter := MaterialRoundSource.emitter readySource 1 arrival entry
abbrev input := MaterialRoundSource.input readySource 1 arrival entry
abbrev protocol := MaterialRoundSource.protocol readySource 1 arrival entry
abbrev environment := MaterialRoundSource.environment readySource 1 arrival entry
abbrev vocabulary := MaterialRoundSource.vocabulary readySource 1 arrival entry
abbrev encoding := MaterialRoundSource.encoding readySource 1 arrival entry
abbrev reception := MaterialRoundSource.reception readySource 1 arrival entry
abbrev slot := MaterialRoundSource.slot readySource 1 arrival entry

theorem upstream_funding_does_not_replace_new_source_delivery_timing_or_quorum :
    SubjectQuorum.produce emitter input 0 protocol (fun _ _ _ => none) vocabulary encoding reception 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding ⟨fun _ _ => slot,0⟩ 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 6 slot 2 = .blocked .missingQuorum := by
  and_intros <;> decide +kernel

abbrev doubleFunded := bound true 2 3 3 0
abbrev doubleArrival : MaterialRoundSource.Bound :=
  ⟨doubleFunded.base,doubleFunded.scope,Machine.Continuation.extend doubleFunded.source 0 replayed,rfl,rfl⟩
theorem repeated_funded_inputs_are_distinct_real_payments_rather_than_duplicate_receipts :
    (doubleFunded.source.code.law.rawItems (before doubleFunded 0) replayed).all
      (fun item => decide (doubleFunded.source.code.law.Valid item.before item.request)) = true ∧
      FuelMaterialSource.status doubleArrival 1 = .decided true ∧
      (MaterialRoundSource.before doubleArrival 1).stock 0 .energy = 0 ∧
      (MaterialRoundSource.before doubleArrival 1).stock 2 .energy = 2 := by decide +kernel

abbrev subject := (ApplicationSubject.resolve emitter input 0 protocol environment vocabulary slot).get (by decide +kernel)
theorem actual_subject_is_generated_from_the_new_payment :
    MaterialRoundSource.outcome readySource 1 arrival entry = .decided true subject := by decide +kernel

theorem the_new_payment_is_consumed_by_its_original_inventory_whole_ledger_and_next :
    let consumed := ControlResponsibility.produce entry.bound input 0 protocol environment vocabulary encoding reception rfl 0
    let runtime := ControlResponsibility.runtime entry.bound input 0 protocol environment vocabulary encoding reception rfl 0
    (∃ item, (item,true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
      flowAt (emitter.code.law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt (emitter.code.law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      (emitter.code.law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor = subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade entry.bound input 0 protocol environment vocabulary encoding reception rfl).process.stateAt
        ((CommunicationRuntime.facade entry.bound input 0 protocol environment vocabulary encoding reception rfl).process.successor runtime.state) :=
  MaterialRoundConsumer.every_completed_new_round_consumes_its_entire_payment_responsibility_and_next
    readySource 1 arrival entry true subject actual_subject_is_generated_from_the_new_payment

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputControls
