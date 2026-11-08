import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
abbrev net := NetworkReentryControls.firstNet
abbrev old := ActualRoundNetworkSource.code net
abbrev start := ActualRoundNetworkSource.start net
abbrev past := (DispatchControlSource.actual net (DispatchControlControls.follow net)
  (DispatchControlControls.immediate net) 3).stages
abbrev saved := EventHistory.execute start past
abbrev batch := DonorRegenerationLaw.word
abbrev extra := AtomicWorkSource.catalogue old batch
abbrev code := AtomicWorkSource.code old batch
theorem original : saved.side = .original := rfl
abbrev quiet : Rule code := SilentWindow.quiet
abbrev none : Opponent code := EventStep.fixed Option.none
-- Waiting belongs to the same original cursor, with one fewer dispatch turn.
-- No physical stock or old packet is replenished by this silent step.
abbrev oldWaited := saved.after SilentWindow.quiet SilentWindow.environment
theorem waitedOriginal : oldWaited.side = .original := rfl
abbrev ready := AtomicWorkSource.cursor old batch oldWaited
abbrev offer := AtomicWorkConsumer.offered old oldWaited true
abbrev work := AtomicWorkSource.protocol old batch offer
abbrev production := AtomicWorkSource.row old batch oldWaited offer none
abbrev generated := AtomicWorkSource.next old batch oldWaited offer none
abbrev delivery : Opponent code := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (by decide +kernel)⟩
abbrev stages := [(work,none),(quiet,delivery)]
abbrev vocabulary := ActualRoundNetworkSource.vocabulary net
abbrev encoding := ActualRoundNetworkSource.encoding net
abbrev origin := CatalogueHandoffConsumer.remember start (past ++ [(SilentWindow.quiet,SilentWindow.environment)])
  vocabulary encoding 0 (ActualRoundNetworkSource.reception net)
abbrev fullPast := past ++ [(SilentWindow.quiet,SilentWindow.environment)]
theorem sameSaved : CatalogueHandoffConsumer.saved start fullPast = oldWaited := by
  change EventHistory.execute start (past ++ [(SilentWindow.quiet,SilentWindow.environment)]) = oldWaited
  rw [OriginQueue.execute_append];rfl
theorem handoffOriginal : (CatalogueHandoffConsumer.saved start fullPast).side = .original := by rw [sameSaved];rfl
theorem sameResumption : CatalogueHandoffConsumer.resumed start fullPast extra handoffOriginal = ready := by
  change AtomicWorkSource.cursor old batch (CatalogueHandoffConsumer.saved start fullPast) = _
  rw [sameSaved]
abbrev law : StageReception.Law code := ⟨fun _ _ => ActualRoundNetworkSource.scope net,3⟩
abbrev received := CatalogueHandoffConsumer.run start fullPast extra handoffOriginal vocabulary encoding law stages 0 origin 2
abbrev wire : StageTransport.Wire (code := old) :=
  ((CatalogueHandoffConsumer.candidates start fullPast vocabulary encoding).head?).get (by decide +kernel)
abbrev receipt : StageReception.Receipt (code := old) := ⟨wire,1,5⟩

theorem actual_batch_regenerates_fuel_in_one_owned_cut_with_a_live_packet :
    AtomicWorkConsumer.select old oldWaited true = .produced ∧
      AtomicWorkConsumer.assess old oldWaited true none = .executed ∧
      production.submitted = batch ∧
      production.before.current.stock 2 .feedstock = 0 ∧
      production.after.current.stock 2 .feedstock = 1 ∧
      production.after.current.stock 0 .energy = 0 ∧
      production.after.current.stock 0 .labor = 1 ∧
      production.after.current.stock 1 .waste = 2 ∧
      production.after.current.claims = production.before.current.claims ∧
      production.after.current.clock = production.before.current.clock + 1 ∧
      production.after.current.round = production.before.current.round + 1 ∧
      production.after.frame.sent = production.before.frame.sent ∧
      production.before.frame.sent.length = 1 := by
  and_intros <;> decide +kernel

theorem the_old_authenticated_wire_and_new_paid_batch_coexist :
    received.receipts = [receipt] ∧ received.audit.length = 2 ∧
      (EventStep.seed (EventHistory.execute ready stages)).current.stock 2 .feedstock = 1 ∧
      (EventStep.seed (EventHistory.execute ready stages)).current.claims () 1 2 = 6 := by
  and_intros <;> decide +kernel

abbrev withheld := AtomicWorkSource.row old batch oldWaited false none
abbrev forgedBatch := [{WorkerInputLaw.energyLabor with signer := 2},WorkerInputLaw.waste,DonorRegenerationLaw.recycle]
abbrev forgedCode := AtomicWorkSource.code old forgedBatch
abbrev forgedNone : Opponent forgedCode := EventStep.fixed Option.none
abbrev forged := AtomicWorkSource.row old forgedBatch oldWaited true forgedNone
abbrev deletedBatch := WorkerInputLaw.word
abbrev deletedCode := AtomicWorkSource.code old deletedBatch
abbrev deletedNone : Opponent deletedCode := EventStep.fixed Option.none
abbrev deleted := AtomicWorkSource.row old deletedBatch oldWaited true deletedNone

theorem real_refusals_do_not_manufacture_fuel_or_relabel_external_time_as_execution :
    AtomicWorkSource.assess old batch oldWaited false none = .withheld ∧
      withheld.submitted = [] ∧ withheld.after.current.stock 2 .feedstock = 0 ∧
      AtomicWorkSource.assess old batch saved true none = .external ∧
      AtomicWorkSource.assess old forgedBatch oldWaited true forgedNone = .refused ∧
      forged.submitted = forgedBatch ∧ forged.after.current.stock 2 .feedstock = 0 ∧
      deleted.submitted = deletedBatch ∧ deleted.after.current.stock 2 .feedstock = 0 ∧
      ¬ DonorRegenerationLaw.Inputs production.after.current := by
  and_intros <;> decide +kernel

abbrev absent := CatalogueHandoffConsumer.run start fullPast extra handoffOriginal vocabulary encoding law
  [(work,none),(quiet,none)] 0 origin 2
abbrev deliveryRow := StageTrace.material generated quiet delivery
abbrev check := CatalogueHandoffConsumer.check start fullPast extra vocabulary
abbrev wrongSigner : StageTransport.Wire (code := old) := {wire with ballot := {wire.ballot with actor := 0}}
abbrev stale : StageReception.Law code := ⟨fun _ _ => {ActualRoundNetworkSource.scope net with epoch := 0},3⟩
abbrev late : StageReception.Law code := ⟨law.scope,0⟩
theorem material_success_does_not_replace_delivery_authentication_timing_or_freshness :
    absent.receipts = [] ∧
      check encoding law 0 deliveryRow [] wrongSigner = .rejected .unauthenticated ∧
      check encoding stale 0 deliveryRow [] wire = .rejected .staleScope ∧
      check encoding late 0 deliveryRow [] wire = .rejected .late ∧
      check encoding law 0 deliveryRow [(wire.ballot.cut,wire.ballot.position)] wire = .rejected .duplicate := by
  and_intros <;> decide +kernel

theorem materialLaw : old.law = DonorRegenerationLaw.law := by
  rw [NetworkReentryConsumer.admitted_network_preserves_the_original_material_law,
    NetworkReentryConsumer.admitted_network_uses_the_actual_prepared_state
      NetworkReentryControls.seed true true {} net (Option.some_get _).symm]
  rfl
abbrev actualReproduction := AtomicWorkConsumer.actual_reproduction_and_original_primitive_debits old oldWaited true none materialLaw
  actual_batch_regenerates_fuel_in_one_owned_cut_with_a_live_packet.2.1
abbrev actualWord := AtomicWorkConsumer.executed_batch_has_one_raw_occurrence old batch oldWaited offer none
  actual_batch_regenerates_fuel_in_one_owned_cut_with_a_live_packet.2.1
abbrev oneVisit := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old batch oldWaited offer none [(quiet,delivery)]
abbrev prefixPreserved := CatalogueHandoffSource.completeFinancialPrefix old extra oldWaited waitedOriginal stages
abbrev actualDelivery := CatalogueHandoffConsumer.receipt_consumes_the_new_native_delivery start fullPast extra
  handoffOriginal vocabulary encoding law stages 0 origin 2 receipt
  (by rw [the_old_authenticated_wire_and_new_paid_batch_coexist.1];exact List.mem_singleton_self _)
def bound : Native.Authority.Bound (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨net.entry.bound.base,net.entry.bound.scope,ready.source,net.entry.bound.law_exact,net.entry.bound.task_exact⟩
abbrev native := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  bound ready stages vocabulary
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkControls
