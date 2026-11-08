import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMandateLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMaterialSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action material)
open MaterialRoundSource (Bound)

def incoming (old : Bound) (count : Nat) : List Action :=
  if (MaterialRoundSource.before old count).stock 0 .feedstock < 1 ∧
      FuelMandateLaw.Inputs (MaterialRoundSource.before old count)
    then FuelMandateLaw.word else []
abbrev produce (old : Bound) (count : Nat) := MaterialRoundConsumer.produce old count (incoming old count)
abbrev status (old : Bound) (count : Nat) := MaterialRoundConsumer.status old count (incoming old count)

structure Inputs (current : Current) : Prop where
  recovery : FuelMandateLaw.Inputs current
  material : ResupplyLaw.Restorable (material current)
  fuel : 0 ≤ current.stock 0 .feedstock
  deficit : current.stock 0 .feedstock < 1
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy

theorem actual_worker_resources_restore_the_original_material_inputs
    (current : Current) (inputs : Inputs current) :
    RenewedQuorumMaterial.Inputs (FuelMandateLaw.successor current) := by
  obtain ⟨recovery,material,fuel,_,labor,energy⟩ := inputs
  obtain ⟨waste,we,wl,feed,willing⟩ := recovery
  obtain ⟨pf,wf,ww,_,stock,pe,pl,_,_⟩ := material
  constructor
  · constructor <;> simp_all [RecycledQuorumMaterial.material,FuelMandateLaw.successor]
  · simp [FuelMandateLaw.successor];linarith
  · simpa [FuelMandateLaw.successor] using labor
  · simpa [FuelMandateLaw.successor] using energy

variable (old : Bound) (count : Nat)

theorem the_stock_deficit_emits_and_executes_the_actual_upstream_word
    (same : old.source.code.law = FuelMandateLaw.law true)
    (inputs : Inputs (MaterialRoundSource.before old count)) :
    incoming old count = FuelMandateLaw.word ∧
      MaterialRoundSource.afterInput old count (incoming old count) =
        FuelMandateLaw.successor (MaterialRoundSource.before old count) ∧
      ∀ item ∈ old.source.code.law.rawItems (MaterialRoundSource.before old count) (incoming old count),
        old.source.code.law.Valid item.before item.request := by
  have selected : incoming old count = FuelMandateLaw.word := by
    simp [incoming,inputs.deficit,inputs.recovery]
  have actual := MaterialRoundSource.the_incoming_and_recovery_are_literal_successive_actual_occurrences
    old count (incoming old count)
  refine ⟨selected,?_,?_⟩
  · rw [actual.2.2.1,same,selected]
    exact (FuelMandateLaw.actual_recovery _ inputs.recovery).1
  · rw [same,selected]
    exact (FuelMandateLaw.actual_recovery _ inputs.recovery).2

theorem source_generated_fuel_is_consumed_by_the_actual_service_recovery
    (same : old.source.code.law = FuelMandateLaw.law true)
    (inputs : Inputs (MaterialRoundSource.before old count)) :
    MaterialRoundSource.recovery old count (incoming old count) = RenewedQuorumMaterial.word ∧
      MaterialRoundSource.prepared old count (incoming old count) =
        RenewedQuorumMaterial.successor (FuelMandateLaw.successor (MaterialRoundSource.before old count)) ∧
      ∀ item ∈ old.source.code.law.rawItems
        (MaterialRoundSource.afterInput old count (incoming old count))
        (MaterialRoundSource.recovery old count (incoming old count)), old.source.code.law.Valid item.before item.request := by
  have upstream := the_stock_deficit_emits_and_executes_the_actual_upstream_word old count same inputs
  have possible := actual_worker_resources_restore_the_original_material_inputs _ inputs
  have ready : RenewedQuorumMaterial.Inputs (MaterialRoundSource.afterInput old count (incoming old count)) := by
    rwa [upstream.2.1]
  have selected : MaterialRoundSource.recovery old count (incoming old count) = RenewedQuorumMaterial.word := by
    simp [MaterialRoundSource.recovery,ready]
  have actual := MaterialRoundSource.the_incoming_and_recovery_are_literal_successive_actual_occurrences
    old count (incoming old count)
  refine ⟨selected,?_,?_⟩
  · rw [actual.2.2.2.2.2,same,selected]
    rw [(FuelMandateLaw.original_material_recovery_is_preserved true _ ready).1,upstream.2.1]
  · rw [same,selected]
    exact (FuelMandateLaw.original_material_recovery_is_preserved true _ ready).2

theorem the_full_preparation_conserves_supplier_fuel_and_pays_the_upstream_worker
    (same : old.source.code.law = FuelMandateLaw.law true)
    (inputs : Inputs (MaterialRoundSource.before old count)) :
    let before := MaterialRoundSource.before old count
    let after := MaterialRoundSource.prepared old count (incoming old count)
    after.stock 0 .feedstock = before.stock 0 .feedstock ∧
      after.stock 1 .service = before.stock 1 .service + 3 ∧
      after.stock 2 .waste = before.stock 2 .waste - 1 ∧
      after.stock 2 .energy = before.stock 2 .energy - 1 ∧
      after.stock 2 .labor = before.stock 2 .labor - 1 ∧
      after.claims = before.claims ∧ after.technology = before.technology := by
  rw [(source_generated_fuel_is_consumed_by_the_actual_service_recovery old count same inputs).2.1]
  simp [RenewedQuorumMaterial.successor,FuelMandateLaw.successor]

theorem both_actual_occurrences_keep_the_original_finance_and_dispositions :
    (∀ ordinal ≤ MaterialRoundSource.depth old count+1,
      Native.Coupling.Match old.source.code old.source.input
        (MaterialRoundSource.attempted old count (incoming old count)).source.input
        (Financial.accountAt old.source.input ordinal)
        (Financial.accountAt (MaterialRoundSource.attempted old count (incoming old count)).source.input ordinal)) ∧
      (produce old count).incomingDisposition = Native.Authority.fullGenerate
        (MaterialRoundSource.supplied old count (incoming old count)) (MaterialRoundSource.depth old count) ∧
      (produce old count).recoveryDisposition = Native.Authority.fullGenerate
        (MaterialRoundSource.attempted old count (incoming old count)) (MaterialRoundSource.depth old count+1) := by
  exact ⟨fun ordinal earlier => MaterialRoundConsumer.every_raw_input_and_recovery_retains_original_accounts_even_when_refused
    old count (incoming old count) ordinal earlier,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMaterialSource
