import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 160000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource FuelControlConsumer

abbrev never : Controller := fun _ _ => false
abbrev always : Controller := fun _ _ => true
abbrev firstHold : Controller := fun cut _ => decide (cut = 0)
abbrev secondHold : Controller := fun cut _ => decide (cut = 2)
abbrev lateRelease : Controller := fun cut _ => decide (cut < 4)
abbrev latest : Nat → Opponent code := fun _ => QueueScheduler.opponent code (OriginQueue.baseline start)
abbrev delayed : Nat → Opponent code := fun cut => if cut = 3 then EventStep.fixed none else latest cut
abbrev silent : Nat → Opponent code := fun _ => EventStep.fixed none
abbrev originalScope := MaterialRoundSource.slot FuelMaterialControls.old 0 FuelMaterialControls.arrival FuelMaterialControls.firstEntry
abbrev lastHold : Nat → Opponent code := fun cut => if cut = 5 then EventStep.fixed none else latest cut

def conforms (control : Controller) (rivals : Nat → Opponent code) : Bool :=
  (List.range window).all fun index => decide (intake (actual control rivals index)
    (rivals (actual control rivals index).cursor.cut) ∈ choices (actual control rivals index))
theorem conforms_iff (control : Controller) (rivals : Nat → Opponent code) :
    conforms control rivals = true ↔ Within control rivals window := by
  simp only [conforms,Within,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem every_opportunity_can_really_be_withheld_without_forced_restoration :
    conforms always latest = true ∧
      (finished always latest).omissions = [(0,0),(2,0),(4,0)] ∧
      capacity < (finished always latest).omissions.length ∧
      (finished always latest).attempts[2]? = some (2,true,true) ∧
      (material (actual always latest 2) true (latest 2)).call = .own 0 none ∧
      result (finished always latest) = .blocked .missingSourceSubject ∧
      (finished always latest).state.current.claims () 1 2 = 7 ∧
      (finished always latest).state.current.stock 1 .service = 3 := by decide +kernel

theorem a_late_actual_signature_cannot_borrow_a_missing_send_or_receipt :
    conforms lateRelease latest = true ∧
      (finished lateRelease latest).omissions = [(0,0),(2,0)] ∧
      ((originSubject (finished lateRelease latest)).map fun subject => subject.1.cut) = some 4 ∧
      ((originSubject (finished lateRelease latest)).map fun subject => subject.2.epoch) = some (originalScope.epoch+4) ∧
      result (finished lateRelease latest) = .blocked .missingQuorum ∧
      (finished lateRelease latest).state.current.claims () 1 2 = 6 ∧
      (finished lateRelease latest).state.current.stock 1 .service = 2 := by decide +kernel

theorem actual_remaining_budget_requires_delivery_at_the_last_external_opportunity :
    allowance (actual firstHold latest 5) = 0 ∧ conforms firstHold latest = true ∧
      conforms firstHold lastHold = false ∧ result (finished firstHold lastHold) = .blocked .missingQuorum ∧
      conforms never delayed = true ∧ released (finished firstHold latest) = true := by decide +kernel

theorem released_opportunities_generate_the_real_payment_and_quorum :
    Complete (finished firstHold latest) ∧ Complete (finished never delayed) := by
  have one : conforms firstHold latest = true := actual_remaining_budget_requires_delivery_at_the_last_external_opportunity.2.1
  have free : released (finished firstHold latest) = true := actual_remaining_budget_requires_delivery_at_the_last_external_opportunity.2.2.2.2.2
  have two : conforms never delayed = true := actual_remaining_budget_requires_delivery_at_the_last_external_opportunity.2.2.2.2.1
  exact ⟨every_actual_released_opportunity_completes_the_paid_subject _ _ ((conforms_iff _ _).mp one) free,
    every_actual_released_opportunity_completes_the_paid_subject _ _ ((conforms_iff _ _).mp two) (by decide +kernel)⟩

theorem the_release_condition_is_sufficient_and_is_not_a_success_certificate :
    released (finished secondHold latest) = false ∧ Complete (finished secondHold latest) := by
  have checked : completeCheck (finished secondHold latest) = true := by decide +kernel
  exact ⟨by decide +kernel,checked_is_complete _ checked⟩

theorem absent_delivery_and_stale_origin_never_become_decisions :
    conforms never silent = false ∧ result (finished never silent) = .blocked .missingQuorum ∧
      StagePaymentQuorum.produce (FuelControlSource.vocabulary originalScope) start
        (FuelControlSource.encoding (finished firstHold latest) originalScope)
        (FuelControlSource.reception originalScope) (finished firstHold latest).stages
        0 originalScope 1 = .blocked .missingSourceSubject := by decide +kernel

abbrev withoutOrigin : Node := {finished firstHold latest with rows := (finished firstHold latest).rows.drop 3}
theorem deleting_the_new_payment_origin_cannot_be_repaired_by_its_old_readout :
    originSubject withoutOrigin = none ∧ result withoutOrigin = .blocked .missingSourceSubject := by decide +kernel


abbrev rawDeviation : Nat → Opponent code := fun cut history past frame =>
  if frame.sent.isEmpty then some ⟨.activate 0,by decide⟩ else delayed cut history past frame

theorem raw_owned_impersonation_is_retained_but_cannot_mint_an_admitted_event :
    conforms never rawDeviation = true ∧ released (finished never rawDeviation) = true ∧
      (material (actual never rawDeviation 1) false (rawDeviation 1)).call = .external (some ⟨.activate 0,by decide⟩) ∧
      StageTransport.admission (material (actual never rawDeviation 1) false (rawDeviation 1)) = none ∧
      Complete (finished never rawDeviation) := by
  have checked : completeCheck (finished never rawDeviation) = true := by decide +kernel
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,checked_is_complete _ checked⟩

theorem removing_actual_timing_still_blocks_the_paid_source_subject :
    StagePaymentQuorum.produce (vocabulary originalScope) start (encoding (finished never delayed) originalScope)
      ⟨fun _ _ => originalScope,1⟩ (finished never delayed).stages 0 originalScope 1 = .blocked .missingQuorum := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlControls
