import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceQuorum

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EncodingAgreement
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem conflicting_support_from_distinct_encodings_exposes_source_capacity
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    StageQuorum.support (InterfaceQuorum.observed start vocabulary leftEncoding leftLaw leftStages left) scope a ∩
      StageQuorum.support (InterfaceQuorum.observed start vocabulary rightEncoding rightLaw rightStages right) scope b ⊆
        InterfaceDeviationEnvelope.affected start.source vocabulary scope := by
  intro key member
  obtain ⟨one,present,scopeOne,valueOne,keyOne⟩ := (StageQuorum.mem_support_iff _ scope a key).mp (Finset.mem_inter.mp member).1
  obtain ⟨two,received,scopeTwo,valueTwo,keyTwo⟩ := (StageQuorum.mem_support_iff _ scope b key).mp (Finset.mem_inter.mp member).2
  have originOne := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary leftEncoding leftLaw start leftStages left leftStages.length one present
  have originTwo := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary rightEncoding rightLaw start rightStages right rightStages.length two received
  have exposed := InterfaceDeviationEnvelope.conflicting_actual_ballots_expose_a_source_affected_key vocabulary start
    leftStages rightStages scope one.wire.ballot two.wire.ballot originOne originTwo
    (keyOne.trans keyTwo.symm) scopeOne scopeTwo (by intro same; exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [keyOne] using exposed

theorem supported_values_from_distinct_encodings_agree
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (first : threshold ≤ (StageQuorum.support (InterfaceQuorum.observed start vocabulary leftEncoding leftLaw leftStages left) scope a).card)
    (second : threshold ≤ (StageQuorum.support (InterfaceQuorum.observed start vocabulary rightEncoding rightLaw rightStages right) scope b).card)
    (safe : code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold + threshold) : a = b := by
  by_contra different
  have exposed := Finset.card_le_card (conflicting_support_from_distinct_encodings_exposes_source_capacity start vocabulary leftEncoding rightEncoding leftLaw rightLaw
    leftStages rightStages left right scope a b different)
  have union : (StageQuorum.support (InterfaceQuorum.observed start vocabulary leftEncoding leftLaw leftStages left) scope a ∪
      StageQuorum.support (InterfaceQuorum.observed start vocabulary rightEncoding rightLaw rightStages right) scope b).card ≤ code.sites := by
    simpa only [Fintype.card_fin] using (StageQuorum.support (InterfaceQuorum.observed start vocabulary leftEncoding leftLaw leftStages left) scope a ∪
      StageQuorum.support (InterfaceQuorum.observed start vocabulary rightEncoding rightLaw rightStages right) scope b).card_le_univ
  have counted := Finset.card_union_add_card_inter
    (StageQuorum.support (InterfaceQuorum.observed start vocabulary leftEncoding leftLaw leftStages left) scope a)
    (StageQuorum.support (InterfaceQuorum.observed start vocabulary rightEncoding rightLaw rightStages right) scope b)
  change _ + (InterfaceDeviationEnvelope.affected start.source vocabulary scope).card < _ at safe
  omega

theorem original_decisions_agree_with_distinct_actual_encodings
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : InterfaceQuorum.produce start vocabulary leftEncoding leftLaw leftStages left scope threshold = .decided a)
    (two : InterfaceQuorum.produce start vocabulary rightEncoding rightLaw rightStages right scope threshold = .decided b) : a = b := by
  obtain ⟨safe,first⟩ := InterfaceQuorum.decision_consumes_source_interface_budget_and_actual_quorum start vocabulary leftEncoding leftLaw leftStages left scope threshold a one
  obtain ⟨_,second⟩ := InterfaceQuorum.decision_consumes_source_interface_budget_and_actual_quorum start vocabulary rightEncoding rightLaw rightStages right scope threshold b two
  exact supported_values_from_distinct_encodings_agree start vocabulary leftEncoding rightEncoding leftLaw rightLaw leftStages rightStages left right scope threshold a b
    (StageQuorum.decided_has_positive_quorum _ scope threshold a first).2
    (StageQuorum.decided_has_positive_quorum _ scope threshold b second).2 safe

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EncodingAgreement
