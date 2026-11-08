import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 160000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open FinancedRoundSource

abbrev parent := OwnedQuorumConsumer.finished OwnedQuorumControls.always OwnedQuorumControls.latest
abbrev old : Bound := ⟨RenewedQuorumMaterial.base,Repayment.Recovery.scope,parent.cursor.source,rfl,rfl⟩
abbrev oldCount := parent.cursor.cut

theorem old_round_is_exhausted_and_the_original_credit_is_the_new_source :
    parent.state.remaining = 0 ∧ parent.state.current.stock 0 .feedstock = 0 ∧
      bill old oldCount = 3 ∧ gap old oldCount = 3 ∧
      (current old oldCount).claims () 1 2 = 7 ∧
      (prepared old oldCount).claims () 1 2 = 10 ∧
      (prepared old oldCount).stock 1 .service = 3 ∧
      (prepared old oldCount).stock 2 .service = 0 ∧
      (ready old oldCount).isSome = true := by
  decide +kernel

def entry : Ready old oldCount := (ready old oldCount).get
  old_round_is_exhausted_and_the_original_credit_is_the_new_source.2.2.2.2.2.2.2.2

abbrev subject : ApplicationSubject.Subject (emitter old oldCount entry) :=
  (ballot old oldCount entry,⟨0,(slot old oldCount entry).epoch,1,(),1,2,1,.service,1,10⟩)

theorem the_next_round_generates_its_full_payment_subject_from_no_paid_vote :
    (slot old oldCount entry).epoch = 53 ∧ window old oldCount entry = 6 ∧
      OwnedAttestation.ledger (emitter old oldCount entry) (input old oldCount entry) 0 (protocol old oldCount entry)
        (environment old oldCount entry) (vocabulary old oldCount entry) 0 = [] ∧
      outcome old oldCount entry = .decided true subject ∧
      (observed old oldCount entry).receipts.length = 1 ∧
      ((actual old oldCount entry).source.feedbackState
        (CommunicationRuntime.actualInput (bound entry) (input old oldCount entry) 0 (protocol old oldCount entry) (environment old oldCount entry)) 6).current.claims () 1 2 = 9 := by
  decide +kernel

theorem the_source_producer_really_opens_a_new_paid_round :
    FinancedRoundConsumer.status old oldCount = .decided true := by
  decide +kernel

abbrev second := actual old oldCount entry
abbrev secondCount := window old oldCount entry

theorem the_next_attempt_cannot_reissue_the_old_credit_or_erase_its_new_debt :
    (current second secondCount).claims () 1 2 = 9 ∧
      (current second secondCount).stock 1 .service = 0 ∧
      (current second secondCount).stock 2 .service = 1 ∧
      (prepared second secondCount).claims () 1 2 = 9 ∧
      (ready second secondCount).isSome = false ∧
      FinancedRoundConsumer.status second secondCount = .historyRefused ∧
      ((attempted second secondCount).source.code.law.rawItems (current second secondCount) (arrival second secondCount)).all
        (fun item => decide ((attempted second secondCount).source.code.law.Valid item.before item.request)) = false := by
  decide +kernel

theorem deleting_the_actual_financing_restores_the_original_payment_refusal :
    ¬ old.source.code.law.Valid (current old oldCount) payment ∧
      old.source.code.law.Valid (prepared old oldCount) payment ∧
      Settlement.classify old.source.code.law 0 ⟨0,current old oldCount,payment⟩ = .rejected .invalidRequest ∧
      (old.source.code.law.next (current old oldCount)
        [⟨2,[],.reserve 2,[],.transfer 2 1 [(.service,gap old oldCount)]⟩]).stock 1 .service = 0 := by
  decide +kernel

abbrev inspect (rival : Opponent (code old oldCount entry))
    (encode : AttestationTransport.Encoding (emitter old oldCount entry))
    (law : AttestationReception.ReceptionLaw (emitter old oldCount entry)) (threshold : Nat) :=
  SubjectQuorum.produce (emitter old oldCount entry) (input old oldCount entry) 0 (protocol old oldCount entry)
    rival (vocabulary old oldCount entry) encode law 0 6 6 (slot old oldCount entry) threshold

theorem actual_delivery_timing_scope_owner_and_quorum_are_independently_required :
    inspect (fun _ _ _ => none) (encoding old oldCount entry) (reception old oldCount entry) 1 = .blocked .missingQuorum ∧
      inspect (environment old oldCount entry) (encoding old oldCount entry) {reception old oldCount entry with maxDelay := 0} 1 = .blocked .missingQuorum ∧
      inspect (environment old oldCount entry) (fun _ => some {ballot old oldCount entry with actor := 2})
        (reception old oldCount entry) 1 = .blocked .missingQuorum ∧
      inspect (environment old oldCount entry) (fun _ => some {ballot old oldCount entry with scope := RenewedQuorumSource.slot true})
        (reception old oldCount entry) 1 = .blocked .missingQuorum ∧
      inspect (environment old oldCount entry) (encoding old oldCount entry) (reception old oldCount entry) 2 = .blocked .missingQuorum := by
  decide +kernel

theorem a_prior_round_body_or_a_forged_payment_cannot_become_the_new_subject :
    ApplicationSubject.verify (emitter old oldCount entry) (input old oldCount entry) 0 (protocol old oldCount entry)
      (environment old oldCount entry) (vocabulary old oldCount entry) (slot old oldCount entry)
      (subject.1,{subject.2 with priorClaim := 7}) = false ∧
      ApplicationSubject.verify (emitter old oldCount entry) (input old oldCount entry) 0 (protocol old oldCount entry)
        (environment old oldCount entry) (vocabulary old oldCount entry) (slot old oldCount entry)
        (subject.1,{subject.2 with quantity := 2}) = false ∧
      SubjectQuorum.produce {emitter old oldCount entry with continuation := [[payment]]}
        (input old oldCount entry) 0 (protocol old oldCount entry) (environment old oldCount entry)
        (vocabulary old oldCount entry) (encoding old oldCount entry) ⟨fun _ _ => slot old oldCount entry,1⟩ 0 6 6
        (slot old oldCount entry) 1 = .blocked .missingSourceSubject := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundControls
