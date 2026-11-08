import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMaterialSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMaterialControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Current Action)
open MaterialRoundSource

-- The new source declares its worker reserves and transfer interface at genesis.
def initial (reserve : Nat) : Current where
  stock := fun party good =>
    if party = 0 ∧ good = .labor then 1
    else if party = 1 ∧ good = .waste then 1
    else if party = 2 ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then reserve else 0
  claims := fun _ _ _ => 0
  technology := ⟨true,0,none,none,none⟩
  clock := 0
  round := 0
abbrev code (released : Bool) (reserve : Nat) : Code Delegation.Funded.Party Repayment.Recovery.Good
    Delegation.Funded.Port (Mandate.State Delegation.Funded.Party Bool) Unit :=
  {RenewedQuorumSource.code RenewedQuorumConsumer.resources 0 true with
    law := FuelMandateLaw.law released
    initial := initial reserve
    bootstrap := [RenewedQuorumSource.issue]}
abbrev source (released : Bool) (reserve : Nat) : Machine Delegation.Funded.Party Repayment.Recovery.Good
    Delegation.Funded.Port (Mandate.State Delegation.Funded.Party Bool) Unit where
  code := code released reserve
  reference := fun _ _ => []
  reference_generated := by
    apply (code released reserve).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code released reserve).publicPrefix
  original := (code released reserve).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev bound (released : Bool) (reserve : Nat) : Bound :=
  ⟨FuelMandateLaw.base released,Repayment.Recovery.scope,source released reserve,rfl,rfl⟩
abbrev old := bound true 2
abbrev arrival := FuelMaterialSource.incoming old 0

theorem actual_upstream_waste_energy_and_labor_generate_fuel_and_private_readiness :
    (before old 0).stock 0 .feedstock = 0 ∧ arrival = FuelMandateLaw.word ∧
      (afterInput old 0 arrival).stock 0 .feedstock = 1 ∧
      (prepared old 0 arrival).stock 0 .feedstock = 0 ∧
      (prepared old 0 arrival).stock 1 .service = 3 ∧
      (prepared old 0 arrival).stock 2 .waste = 1 ∧
      (prepared old 0 arrival).stock 2 .energy = 1 ∧
      (prepared old 0 arrival).stock 2 .labor = 1 ∧
      (prepared old 0 arrival).claims () 1 2 = 7 ∧ (inspect old 0 arrival).isSome = true := by
  decide +kernel
def firstEntry : Ready old 0 arrival := (inspect old 0 arrival).get
  actual_upstream_waste_energy_and_labor_generate_fuel_and_private_readiness.2.2.2.2.2.2.2.2.2
abbrev first := actual old 0 arrival firstEntry

theorem the_recovered_upstream_material_is_consumed_by_the_actual_paid_quorum :
    FuelMaterialSource.status old 0 = .decided true ∧
      (before first 6).stock 0 .feedstock = 0 ∧ (before first 6).stock 1 .service = 0 ∧
      (before first 6).claims () 1 2 = 6 := by
  decide +kernel

abbrev secondArrival := FuelMaterialSource.incoming first 6
theorem the_literal_successor_generates_the_next_supply_without_resetting_old_debt :
    secondArrival = FuelMandateLaw.word ∧ (afterInput first 6 secondArrival).stock 0 .feedstock = 1 ∧
      (prepared first 6 secondArrival).stock 0 .feedstock = 0 ∧
      (prepared first 6 secondArrival).stock 2 .waste = 0 ∧
      (prepared first 6 secondArrival).stock 2 .energy = 0 ∧
      (prepared first 6 secondArrival).stock 2 .labor = 0 ∧
      (prepared first 6 secondArrival).claims () 1 2 = 6 ∧ (inspect first 6 secondArrival).isSome = true := by
  decide +kernel
def secondEntry : Ready first 6 secondArrival := (inspect first 6 secondArrival).get
  the_literal_successor_generates_the_next_supply_without_resetting_old_debt.2.2.2.2.2.2.2
abbrev second := actual first 6 secondArrival secondEntry

theorem both_actual_decisions_consume_fresh_subjects_and_the_remaining_upstream_reserves :
    FuelMaterialSource.status first 6 = .decided true ∧ (before second 6).claims () 1 2 = 5 ∧
      slot old 0 arrival firstEntry ≠ slot first 6 secondArrival secondEntry ∧
      FuelMaterialSource.incoming second 6 = [] ∧ FuelMaterialSource.status second 6 = .phaseRefused := by
  decide +kernel

theorem primitive_source_resources :
    FuelMaterialSource.Inputs (before old 0) ∧ FuelMaterialSource.Inputs (before first 6) := by
  constructor <;> repeat' constructor <;> decide +kernel

theorem actual_consumer_uses_the_general_material_producer :
    let start := before old 0
    let finish := prepared old 0 arrival
    finish.stock 0 .feedstock = start.stock 0 .feedstock ∧
      finish.stock 1 .service = start.stock 1 .service + 3 ∧
      finish.stock 2 .waste = start.stock 2 .waste - 1 ∧
      finish.stock 2 .energy = start.stock 2 .energy - 1 ∧
      finish.stock 2 .labor = start.stock 2 .labor - 1 ∧
      finish.claims = start.claims ∧ finish.technology = start.technology :=
  FuelMaterialSource.the_full_preparation_conserves_supplier_fuel_and_pays_the_upstream_worker
    old 0 rfl primitive_source_resources.1

theorem no_permission_no_worker_reserve_and_wrong_signer_are_real_refusals :
    FuelMaterialSource.status (bound false 2) 0 = .historyRefused ∧
      (afterInput (bound false 2) 0 (FuelMaterialSource.incoming (bound false 2) 0)).stock 0 .feedstock = 0 ∧
      FuelMaterialSource.incoming (bound true 0) 0 = [] ∧
      FuelMaterialSource.status (bound true 0) 0 = .phaseRefused ∧
      (FuelMandateLaw.law true).actualCredit
        ((FuelMandateLaw.law true).step (before old 0) FuelMandateLaw.recycle)
        {FuelMandateLaw.give with signer := 1} = [] := by
  decide +kernel

theorem the_new_source_declares_its_law_and_does_not_reinterpret_the_old_permission :
    (¬ (FuelMandateLaw.law false).Valid
      ((FuelMandateLaw.law false).step (before old 0) FuelMandateLaw.recycle) FuelMandateLaw.give) ∧
      (source true 2).code.law = Mandate.law (FuelMandateLaw.base true) Repayment.Recovery.scope ∧
      (source true 2).code.initial = initial 2 := by
  exact ⟨by decide +kernel,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMaterialControls
