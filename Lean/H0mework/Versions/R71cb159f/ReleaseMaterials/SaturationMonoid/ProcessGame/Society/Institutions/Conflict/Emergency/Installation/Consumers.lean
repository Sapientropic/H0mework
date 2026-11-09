import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Protection
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.PaidService
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Consumers.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Consumers

open Capitalism.Universal.Source.Program Capitalism.Universal.Root
open PublicFunction PublicFunction.Mandate
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm (withCutoff scanPaidService)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term (PaidAt)
open Emergency.Consumers (Party Port Raw Req Word scope initial originalWord)

def provisioned : RawLaw Party Unit Port Unit Unit :=
  { Emergency.Consumers.base with
    necessities := fun _ _ => [((), 1)]
    mandatoryMaintenance := fun _ _ => [((), 1)] }

def payService : Word :=
  [⟨2, [], .service, [.service], .use 0 [((), 1)] .maintenance⟩,
    ⟨2, [], .service, [.service], .use 1 [((), 1)] .maintenance⟩]

def scheduled : List Word := [payService, []]

def independentUse (bearer : Party) : Req :=
  ⟨bearer, [], .resource, [], .use bearer [((), 1)] .necessity⟩

def menu (_ : Raw) : List Req := (List.finRange 3).map independentUse

def opening? : Option (Opening provisioned scope 0 1 () initial originalWord scheduled) :=
  match compileProtected provisioned scope 0 1 () initial menu originalWord scheduled with
  | .installed opened _ _ => some opened
  | _ => none

theorem installs : opening?.isSome = true := by decide +kernel

def opened := opening?.get installs

theorem publishes_three_and_preserves_the_original_service_due :
    opened.installedScope.task.deadline = 3 ∧
      (opened.source menu 0 Emergency.Consumers.source.positive).source.seed.task.deadline = 4 := by
  decide +kernel

def envelope :=
  longestProtected? provisioned scope 0 1 () initial ([] :: originalWord :: scheduled) menu

theorem the_exact_latest_boundary_is_open_at_four :
    (envelope.map SafeTerm.ceiling = some 4) ∧
      ∀ candidate, envelope = some candidate → ¬ candidate.Allows candidate.ceiling := by
  have exactMap : envelope.map SafeTerm.ceiling = some 4 := by decide +kernel
  refine ⟨exactMap, ?_⟩
  intro candidate found fit
  have top : candidate.ceiling = 4 := by
    simpa [found] using exactMap
  have appointment : candidate.cell.target.clock = 4 := by
    have mapTime : envelope.map (fun term => term.cell.target.clock) = some 4 := by decide +kernel
    simpa [found] using mapTime
  have early := ((term_band_exact scope.task candidate.cell candidate.assigned _).mp fit.2).2.1
  rw [top, appointment] at early
  exact (lt_irrefl (4 : ℚ)) early

noncomputable section

abbrev input := opened.input menu 0 Emergency.Consumers.source.positive
abbrev actual := opened.actual menu 0 Emergency.Consumers.source.positive
abbrev whole := opened.wholeLedger menu 0 Emergency.Consumers.source.positive
abbrev next := opened.next menu 0 Emergency.Consumers.source.positive

theorem the_original_authorization_is_signed_at_one_with_generated_cutoff_three :
    ((opened.originalGrants menu 0 Emergency.Consumers.source.positive).map fun event =>
      (event.grant.candidate, event.grant.acceptance.item.val.before.clock)) = [(2, 1)] ∧
      opened.installedScope.task.deadline = 3 := by
  decide +kernel

theorem both_reviewers_pay_and_the_original_claim_and_generated_next_remain :
    (actual.interpreted.items.map fun item =>
      (law provisioned opened.installedScope).actualDebit item.before item.request) =
        [locate 0 scope.revisionCost, locate 1 scope.revisionCost] ∧
      actual.after.technology.holder = none ∧
      actual.after.claims () 0 1 = 2 ∧
      actual.after.clock = 5 ∧
      actual.after = ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input 5).current := by
  have release :=
    opened.generated_review_consumes_both_costs_on_the_original_root menu 0 Emergency.Consumers.source.positive
  have positions :=
    opened.actual_reviews_are_the_registered_paid_word menu 0 Emergency.Consumers.source.positive
  refine ⟨?_, release.1, ?_, ?_, release.2.2.2⟩
  · exact opened.the_two_original_review_positions_charge_their_own_material
      menu 0 Emergency.Consumers.source.positive
  · rw [actual.after_exact, positions.1, positions.2]
    decide +kernel
  · rw [actual.after_exact, positions.1, positions.2]
    decide +kernel

def completeService :=
  scanPaidService (opened.source menu 0 Emergency.Consumers.source.positive) [] opened.inputs

theorem the_native_service_archive_contains_two_distinct_paid_positions :
    PaidAt (opened.source menu 0 Emergency.Consumers.source.positive) [] opened.inputs := by
  have ready : (match completeService with | .paid _ => true | .blocked _ => false) = true := by decide +kernel
  cases computed : completeService with
  | paid service => exact service
  | blocked failure => rw [computed] at ready; cases ready

theorem the_original_financial_history_reaches_the_paid_successor :
    (Financial.accountAt input 4).current.history <+: (Financial.accountAt input 5).current.history :=
  Financial.whole_native_history_is_retained input 4

theorem every_original_party_has_a_generated_independent_offer (bearer : Party) :
    independentUse bearer ∈ opened.independentOffers menu bearer := by
  apply (opened.independent_offers_exact menu bearer (independentUse bearer)).mpr
  refine ⟨List.mem_map.mpr ⟨bearer, List.mem_finRange bearer, rfl⟩, ?_⟩
  fin_cases bearer <;> decide +kernel

theorem every_original_party_can_pay_an_independent_use_on_the_original_next (bearer : Party) :
    let source := (opened.source menu 0 Emergency.Consumers.source.positive).source
    let paid := OutstandingSource.History.actualExecution source
      (opened.inputs ++ [[independentUse bearer]]) 4
    paid.before = actual.after ∧ paid.submitted = [independentUse bearer] ∧
      (law provisioned opened.installedScope).actualDebit paid.before (independentUse bearer) =
        locate bearer ((law provisioned opened.installedScope).necessities paid.before bearer) := by
  have emitted := opened.selected_independent_offer_pays_on_the_original_following_visit
    menu 0 Emergency.Consumers.source.positive bearer (independentUse bearer)
    (every_original_party_has_a_generated_independent_offer bearer)
  exact ⟨emitted.1.trans
      (opened.after_review_is_the_original_physical_successor menu 0 Emergency.Consumers.source.positive).symm,
    emitted.2.1, emitted.2.2.1⟩

end

def drainSecond : Req := ⟨1, [], .resource, [], .transfer 1 0 [((), 4)]⟩

def drained : List Word := [payService, [drainSecond]]

theorem the_identical_service_with_an_unfunded_second_reviewer_cannot_install :
    ∀ expiry, ¬ Feasible provisioned scope 0 1 () initial ([] :: originalWord :: drained) expiry := by
  exact (shortest_eq_none_iff provisioned scope 0 1 () initial _).mp (by decide +kernel)

theorem the_shortage_is_at_the_second_original_payers_material_address :
    let current := (replay provisioned scope 3 initial ([] :: originalWord :: drained)).2
    let active := law provisioned (withCutoff scope 3)
    let middle := active.step current (request (withCutoff scope 3) current 0 .review)
    active.Valid current (request (withCutoff scope 3) current 0 .review) ∧
      middle.stock 1 () = 0 ∧
      ¬ active.Valid middle (request (withCutoff scope 3) middle 1 .review) := by
  decide +kernel

def failureAddress : Option ((Party × Unit) × ℚ) :=
  match compileProtected provisioned scope 0 1 () initial menu originalWord drained with
  | .blocked _ explain =>
    match explain 3 with
    | .calendar (.review _ _ _ (.secondRefused _ (some shortage))) => some (shortage.entry.1, Shortage.missing provisioned scope 3 shortage)
    | _ => none
  | _ => none

theorem solver_names_the_original_second_reviewer_and_the_missing_unit :
    failureAddress = some ((1, ()), 1) := by decide +kernel

def withoutSecondExit (_ : Raw) : List Req := [independentUse 0, independentUse 2]

def blockedExit : Option Party :=
  match compileProtected provisioned scope 0 1 () initial withoutSecondExit originalWord scheduled with
  | .blocked _ explain =>
    match explain 3 with
    | .independentExit _ _ _ bearer _ _ => some bearer
    | _ => none
  | _ => none

theorem paid_service_and_review_cannot_install_by_removing_an_original_exit :
    blockedExit = some 1 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Consumers
