import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open OwnedAttestation
open Distributed.Recall.Information.Agency.Protocol

abbrev origin := Distributed.Recall.Information.Regression.source
def yes : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 1)] .external⟩
def no : Mandate.Source.Action := ⟨false, [], .challenge, [], .use false [((), 1)] .external⟩
def nextPhase : Mandate.Source.Action := ⟨false, [], .service, [], .use false [((), 1)] .external⟩
def free : Mandate.Source.Action := ⟨false, [], .resource, [], .present⟩
def wrong : Mandate.Source.Action := ⟨true, [], .resource, [], .use false [((), 1)] .external⟩
def huge : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 100)] .external⟩

abbrev code := {origin.code with
  actions := [yes, no, nextPhase, free, wrong, huge]
  actionLimit := 3
  signals := 2
  initialSignal := 0
  memoryReady := fun _ => true
  readLocal := fun _ _ => 0
  afterSend := fun _ _ _ reading => reading
  afterDelivery := fun _ _ _ reading => reading
  afterAction := fun _ _ _ => 1
  eventAlphabet := [.activate 0, .adversary yes, .adversary wrong]
  eventLimit := 0}

def work : code.Policy := fun key _ => if key.2 = 0 then [yes, no, nextPhase] else [no]
theorem work_generated : work ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split <;> simp

def activation (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.activate site, by
    have same : site = 0 := Subsingleton.elim _ _
    subst site
    simp [code]⟩, by
      have same : site = 0 := Subsingleton.elim _ _
      subst site
      simp [ownMoves, code]⟩

abbrev rule : Rule code := ⟨⟨work, work_generated⟩, fun key _ => activation key.1⟩
abbrev source : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {origin with
    code := code
    reference := work
    reference_generated := work_generated
    opponent := fun _ _ _ => none
    feedback? := none
    feedbackOverrides := []}
abbrev entry : Input code := ⟨fun _ _ _ => none, 4⟩
def environment : Opponent code := fun _ _ _ => some ⟨.adversary yes, by simp [code]⟩
abbrev vocabulary : Vocabulary (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨(fun port => match port with
      | .resource => some (⟨0, 0, 0⟩, true)
      | .challenge => some (⟨0, 0, 0⟩, false)
      | .service => some (⟨0, 0, 1⟩, true)), fun _ => 0, ()⟩
abbrev inspectAt := OwnedAttestation.inspect source entry 0 rule environment vocabulary
abbrev ballot (n position : Nat) (scope : Scope) (choice : Bool) : Ballot source :=
  ⟨n, position, 0, false, scope, choice, 1⟩
abbrev support := ballot 0 0 ⟨0, 0, 0⟩ true
abbrev oppose := ballot 0 1 ⟨0, 0, 0⟩ false
abbrev phase := ballot 0 2 ⟨0, 0, 1⟩ true

theorem local_actions_generate_paid_explicit_ballots_and_keep_phase_separate :
    inspectAt 0 0 = .attested support ∧ inspectAt 0 1 = .attested oppose ∧
      inspectAt 0 2 = .attested phase ∧
      conflicts source support oppose = true ∧ conflicts source oppose phase = false ∧
      (OwnedAttestation.evidence source entry 0 rule environment vocabulary 1).length = 2 := by
  decide +kernel

theorem the_same_site_changes_its_action_after_its_actual_local_record_changes :
    (OwnedAttestation.execution source entry 0 rule environment 0).submitted = [yes, no, nextPhase] ∧
      (localState source entry 0 rule environment 2).frame.inbox 0 = 1 ∧
      (OwnedAttestation.execution source entry 0 rule environment 2).submitted = [no] ∧
      inspectAt 2 0 = .attested (ballot 2 0 ⟨0, 0, 0⟩ false) := by
  decide +kernel

theorem external_valid_paid_impersonation_has_effects_but_generates_no_own_ballot :
    (OwnedAttestation.execution source entry 0 rule environment 1).submitted = [yes] ∧
      code.law.Valid (OwnedAttestation.execution source entry 0 rule environment 1).before yes ∧
      flowAt (code.law.actualDebit (OwnedAttestation.execution source entry 0 rule environment 1).before yes) false () = 1 ∧
      inspectAt 1 0 = .rejected .notOwnedActivation ∧
      (audit source entry 0 rule environment vocabulary 1).map (fun row => row.1.request) = [yes] := by
  decide +kernel

theorem forged_fields_missing_source_and_expired_scope_are_rejected :
    OwnedAttestation.verify source entry 0 rule environment vocabulary support = true ∧
      OwnedAttestation.verify source entry 0 rule environment vocabulary {support with actor := true} = false ∧
      OwnedAttestation.verify source entry 0 rule environment vocabulary {support with choice := false} = false ∧
      OwnedAttestation.verify source entry 0 rule environment vocabulary {support with fee := 2} = false ∧
      OwnedAttestation.verify source entry 0 rule environment vocabulary {support with cut := 1} = false ∧
      OwnedAttestation.verify source entry 0 rule environment vocabulary {support with position := 9} = false ∧
      OwnedAttestation.inspect source entry 0 rule environment {vocabulary with epoch := fun _ => 1} 0 0 = .rejected .expired ∧
      inspectAt 4 0 = .rejected .notOwnedActivation := by
  decide +kernel

abbrev continued := {source with continuation := [[yes]]}

theorem a_preloaded_continuation_cannot_impersonate_a_new_owned_activation :
    (OwnedAttestation.execution continued entry 0 rule environment 0).submitted = [yes] ∧
      OwnedAttestation.inspect continued entry 0 rule environment vocabulary 0 0 = .rejected .notOwnedActivation := by
  decide +kernel

theorem wrong_signer_and_unpaid_requests_fail_even_when_raw_admission_accepts :
    code.law.Valid code.initial wrong ∧ code.law.Valid code.initial free ∧
      classify source vocabulary 0 0 0 ⟨0, code.initial, wrong⟩ = .rejected .wrongSigner ∧
      classify source vocabulary 0 0 0 ⟨0, code.initial, free⟩ = .rejected .unpaid := by
  decide +kernel

def malformedWork : code.Policy := fun _ _ => [wrong, free, huge]
theorem malformed_generated : malformedWork ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [malformedWork])
abbrev malformed : Rule code := {rule with work := ⟨malformedWork, malformed_generated⟩}
abbrev withholding : Rule code := {rule with events := fun _ _ => ⟨none, List.mem_cons_self⟩}

theorem actual_bad_implementation_and_withholding_do_not_mint_ballots :
    (OwnedAttestation.execution source entry 0 malformed environment 0).submitted = [wrong, free, huge] ∧
      (audit source entry 0 malformed environment vocabulary 0).map (fun row => row.2) =
        [.rejected .wrongSigner, .rejected .unpaid, .rejected .invalid] ∧
      (OwnedAttestation.execution source entry 0 withholding environment 0).submitted = [] ∧
      OwnedAttestation.inspect source entry 0 withholding environment vocabulary 0 0 = .rejected .notOwnedActivation := by
  decide +kernel

theorem the_generated_ledger_does_not_duplicate_occurrence_receipts :
    (ledger source entry 0 rule environment vocabulary 4).map (fun body => (body.cut, body.position)) =
      [(0, 0), (0, 1), (0, 2), (2, 0)] := by
  decide +kernel

theorem an_independent_consumer_recovers_the_own_selected_word_and_paid_origin :
    (OwnedAttestation.execution source entry 0 rule environment 0).submitted = code.action rule.work.val 0
      ((localState source entry 0 rule environment 0).frame.inbox 0) ∧
      ∃ site item,
        owner source entry 0 rule environment 0 = some site ∧
        (code.law.rawItems (OwnedAttestation.execution source entry 0 rule environment 0).before
          (OwnedAttestation.execution source entry 0 rule environment 0).submitted)[0]? = some item ∧
        code.law.Valid item.before item.request ∧ item.request.signer = code.siteParty site ∧
        vocabulary.decode item.request.purpose = some (support.scope, support.choice) ∧
        support.scope.epoch = vocabulary.epoch item.before ∧
        support.cut = 0 ∧ support.position = 0 ∧ support.key = site ∧
        support.actor = code.siteParty site ∧
        support.fee = flowAt (code.law.actualDebit item.before item.request) support.actor vocabulary.feeUnit ∧
        0 < support.fee := by
  exact ⟨owned_activation_is_actual_selected_local_work source entry 0 rule environment rfl 0 0
    (by decide +kernel), attested_has_owned_paid_origin source entry 0 rule environment vocabulary 0 0 support
      (by decide +kernel)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationControls
