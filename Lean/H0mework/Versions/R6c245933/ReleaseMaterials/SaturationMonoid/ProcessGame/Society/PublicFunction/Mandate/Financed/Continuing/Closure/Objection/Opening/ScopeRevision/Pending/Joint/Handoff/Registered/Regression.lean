import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Source.ProgrammeControl
noncomputable section
abbrev authority := Handoff.Regression.authority
abbrev inventory := Handoff.Regression.late
abbrev fresh := Handoff.Regression.fresh
abbrev before := Handoff.start fresh
abbrev localLaw := Handoff.law fresh

def front := Handoff.Method.reserved.front fresh before
def signedPair : List Action :=
  let first := localLaw.execute before 0 front |>.final
  let proposal := Mandate.request fresh.scope first false (.propose true)
  [proposal,Mandate.request fresh.scope (localLaw.step first proposal) true .accept]
def access : Action := ⟨true,[],.service,[.service],.transfer true false [(.service,1)]⟩
def payment : Action := ⟨false,[],.resource,[],.transfer false true [(.service,3)]⟩
def services : List Action := (Handoff.services fresh).map fun item => {item with signer := true}
def serving := front ++ signedPair ++ [access,payment] ++ services
def word : List Action := serving

theorem the_registered_captured_service_word_is_legal_and_pays_the_original_task :
    (∀ item ∈ localLaw.rawItems before word,localLaw.Valid item.before item.request) ∧
    (∀ index, (Handoff.source fresh).SlotPaid before word index) := by decide +kernel

theorem the_original_source_service_word_is_also_actually_paid :
    (∀ index,(Handoff.source fresh).SlotPaid before (Handoff.firstWord fresh) index) :=
  Handoff.Regression.reserved_new_epoch_really_pays_each_original_content_and_keeps_the_old_principal.2.1

theorem accessAvailable : (Kernel.Discovery.accesses localLaw before word).head?.isSome = true := by decide +kernel
def foundAccess := (Kernel.Discovery.accesses localLaw before word).head?.get accessAvailable
theorem returnAvailable : (Kernel.Discovery.ReturnIncidence.directReturns localLaw before word foundAccess).head?.isSome = true := by decide +kernel
def foundReturn := (Kernel.Discovery.ReturnIncidence.directReturns localLaw before word foundAccess).head?.get returnAvailable
theorem disposalAvailable : (Kernel.Discovery.disposals localLaw before word foundAccess).head?.isSome = true := by decide +kernel
def foundDisposal := (Kernel.Discovery.disposals localLaw before word foundAccess).head?.get disposalAvailable

def proposal : Kernel.Proposal localLaw before word := ⟨foundAccess,foundReturn,foundDisposal⟩

theorem original_control_access_payment_and_disposal_are_checked_together :
    proposal.Checks localLaw before word := by decide +kernel

def kernel : Kernel.CapitalRelationKernel localLaw before word :=
  (Kernel.compile localLaw before word proposal).get (by simp [Kernel.compile,original_control_access_payment_and_disposal_are_checked_together])

theorem the_source_census_contains_this_same_original_control_return :
    kernel ∈ Kernel.Discovery.ReturnIncidence.kernels localLaw before word := by
  have accessIn : foundAccess ∈ Kernel.Discovery.accesses localLaw before word := by
    apply List.mem_of_mem_head?
    exact (Option.some_get accessAvailable).symm
  have returnIn : foundReturn ∈ Kernel.Discovery.ReturnIncidence.directReturns localLaw before word foundAccess := by
    apply List.mem_of_mem_head?
    exact (Option.some_get returnAvailable).symm
  have disposalIn : foundDisposal ∈ Kernel.Discovery.disposals localLaw before word foundAccess := by
    apply List.mem_of_mem_head?
    exact (Option.some_get disposalAvailable).symm
  exact Kernel.Discovery.ReturnIncidence.every_successfully_compiled_direct_return_is_in_the_census
    localLaw before word foundAccess accessIn foundReturn returnIn foundDisposal disposalIn kernel
    (by change Kernel.compile localLaw before word proposal = some kernel
        simp [kernel,Kernel.compile,original_control_access_payment_and_disposal_are_checked_together])

theorem legAvailable : (Kernel.Discovery.ReturnIncidence.route localLaw before word kernel).head?.isSome = true := by decide +kernel
def leg := (Kernel.Discovery.ReturnIncidence.route localLaw before word kernel).head?.get legAvailable

theorem the_actual_payment_is_selected_by_the_original_full_source_census :
    Kernel.Discovery.ReturnIncidence.selected localLaw before word 6 = true := by
  apply (Kernel.Discovery.ReturnIncidence.selected_exact _ _ _ _).mpr
  refine ⟨kernel,the_source_census_contains_this_same_original_control_return,leg,?_,?_,?_⟩
  · apply List.mem_of_mem_head?
    exact (Option.some_get legAvailable).symm
  · decide +kernel
  · decide +kernel

theorem the_selected_occurrence_really_transfers_three_original_service_units :
    leg.item.val.index = 6 ∧
    flowAt (localLaw.actualCredit leg.item.val.before leg.item.val.request) true .service = 3 := by
  constructor <;> decide +kernel

theorem the_old_source_word_has_no_remaining_private_phase (port : Mandate.Source.Port) (recipient : Bool) :
    ¬ PrivatePhase localLaw (localLaw.next before (Handoff.firstWord fresh)) port recipient := by
  cases port <;> cases recipient <;> decide +kernel

theorem the_old_source_word_has_no_control_return_kernel :
    Kernel.Discovery.ReturnIncidence.kernels localLaw before (Handoff.firstWord fresh) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro generated _
  exact the_old_source_word_has_no_remaining_private_phase _ _ generated.checked.1.2.2.2.2.2

theorem the_source_selected_alternative_does_not_select_a_fictitious_payment (index : Nat) :
    Kernel.Discovery.ReturnIncidence.selected localLaw before (Handoff.firstWord fresh) index = false := by
  simp only [Kernel.Discovery.ReturnIncidence.selected,Kernel.Discovery.ReturnIncidence.selectedBy,
    the_old_source_word_has_no_control_return_kernel,Kernel.Discovery.ReturnIncidence.positionsOf,List.flatMap_nil,List.any_nil]

def positiveTransfers (submitted : List Action) :=
  (localLaw.rawItems before submitted).filterMap fun original => match original.request.operation with
    | .transfer payer _ _ =>
      let quantity := flowAt (localLaw.actualDebit original.before original.request) false .service
      if payer = false ∧ 0 < quantity then some (original.index,quantity) else none
    | _ => none

def controlReturnDebit (submitted : List Action) : ℚ :=
  ((positiveTransfers submitted).map fun entry =>
    if Kernel.Discovery.ReturnIncidence.selected localLaw before submitted entry.1 then entry.2 else 0).sum

theorem the_real_same_unit_control_return_debit_is_three_and_the_original_alternative_is_zero :
    controlReturnDebit word = 3 ∧ controlReturnDebit (Handoff.firstWord fresh) = 0 := by
  constructor
  · have shape : positiveTransfers word = [(6,3)] := by decide +kernel
    simp only [controlReturnDebit,shape,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      the_actual_payment_is_selected_by_the_original_full_source_census,ite_true]
  · unfold controlReturnDebit
    apply List.sum_eq_zero
    intro value member
    obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member
    rw [the_source_selected_alternative_does_not_select_a_fictitious_payment]
    rfl


theorem the_registered_word_and_original_alternative_are_both_consumed_as_paid :
    (Registered.Runtime.fromRoot authority inventory fresh word).assessment.isPaid = true ∧
    (Registered.Runtime.fromRoot authority inventory fresh (Handoff.firstWord fresh)).assessment.isPaid = true := by
  constructor
  · apply (Registered.actual_paid_is_checked_not_supplied authority inventory fresh word).mpr
    change (∀ item ∈ localLaw.rawItems (Registered.actual authority inventory fresh word).before
      (Registered.actual authority inventory fresh word).submitted,localLaw.Valid item.before item.request) ∧ _
    rw [(Registered.literal_input_and_original_in_window_cut authority inventory fresh word).1,
      (Registered.literal_input_and_original_in_window_cut authority inventory fresh word).2]
    exact the_registered_captured_service_word_is_legal_and_pays_the_original_task
  · apply (Registered.actual_paid_is_checked_not_supplied authority inventory fresh (Handoff.firstWord fresh)).mpr
    change (∀ item ∈ localLaw.rawItems (Registered.actual authority inventory fresh (Handoff.firstWord fresh)).before
      (Registered.actual authority inventory fresh (Handoff.firstWord fresh)).submitted,localLaw.Valid item.before item.request) ∧ _
    rw [(Registered.literal_input_and_original_in_window_cut authority inventory fresh (Handoff.firstWord fresh)).1,
      (Registered.literal_input_and_original_in_window_cut authority inventory fresh (Handoff.firstWord fresh)).2]
    have chosen := Handoff.Regression.reserved_new_epoch_really_pays_each_original_content_and_keeps_the_old_principal.1
    cases found : Handoff.select fresh before with
    | none => simp only [found,Option.map_none] at chosen; cases chosen
    | some paid =>
      have legal := (Handoff.selected_word_pays_the_generated_scope fresh before paid found).1
      exact ⟨legal,the_original_source_service_word_is_also_actually_paid⟩

theorem the_two_real_responses_have_the_same_clock_and_different_literal_inputs :
    (Registered.final authority inventory fresh word).clock =
      (Registered.final authority inventory fresh (Handoff.firstWord fresh)).clock ∧ word ≠ Handoff.firstWord fresh := by
  refine ⟨by decide +kernel,?_⟩
  have lengths : word.length ≠ (Handoff.firstWord fresh).length := by decide +kernel
  intro same
  exact lengths (congrArg List.length same)

def paymentWithoutService := front ++ signedPair ++ [access,payment]

theorem payment_without_an_original_necessary_use_does_not_generate_a_control_kernel :
    Kernel.Discovery.ReturnIncidence.kernels localLaw before paymentWithoutService = [] := by
  have absent : (Kernel.Discovery.accesses localLaw before paymentWithoutService).isEmpty = true := by decide +kernel
  have empty := List.nil_of_isEmpty absent
  simp only [Kernel.Discovery.ReturnIncidence.kernels,empty,List.flatMap_nil]

theorem explicit_empty_input_and_payment_without_service_do_not_forge_public_payment :
    (Registered.Runtime.fromRoot authority inventory fresh []).assessment.isPaid = false ∧
    (Registered.Runtime.fromRoot authority inventory fresh paymentWithoutService).assessment.isPaid = false := by decide +kernel



end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Regression
