import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionHistory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponseRuntime

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionClaims
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

theorem readAt_retains_its_actual_index (past : List (EventHistory.Stage (code := code)))
    (receiver : Fin code.sites) (index : Nat) (entry : ReceptionEvidence.Entry start past vocabulary encoding law receiver)
    (read : ReceptionEvidence.readAt start past vocabulary encoding law receiver index = some entry) : entry.index = index := by
  unfold ReceptionEvidence.readAt at read
  repeat' first | split at read | contradiction
  cases Option.some.inj read
  rfl

theorem every_original_rejection_identity_survives_actual_extension
    (past more : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (entry : ReceptionEvidence.Entry start past vocabulary encoding law receiver) :
    (receiver, entry.index) ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law (past ++ more) := by
  have bound := ReceptionEvidence.bounded start past vocabulary encoding law receiver entry
  have oldAuth := ReceptionEvidence.incoming_has_its_actual_authenticated_origin start past vocabulary encoding law receiver entry
  have incoming := (StagePrefix.incoming_at start past more vocabulary encoding entry.index bound).trans entry.incoming
  have nextAuth := StagePrefix.incoming_is_authenticated start (past ++ more) vocabulary encoding entry.index
    (by simp only [List.length_append]; omega) entry.wire incoming
  have rejected : StageReception.check vocabulary encoding law start (past ++ more) receiver entry.row
      (ReceptionEvidence.seen start (past ++ more) vocabulary encoding law receiver entry.index) entry.wire = .rejected entry.reason := by
    have original := entry.rejected
    simp only [ReceptionEvidence.seen, StagePrefix.run_at start past more vocabulary encoding law receiver entry.index (by omega)]
    simpa only [StageReception.check, nextAuth, oldAuth] using original
  have existsEntry : (ReceptionEvidence.readAt start (past ++ more) vocabulary encoding law receiver entry.index).isSome = true := by
    have actual := (StagePrefix.record_at start past more entry.index bound).trans entry.actual
    unfold ReceptionEvidence.readAt
    split
    · rename_i absent
      rw [actual] at absent
      contradiction
    · rename_i record found
      cases Option.some.inj (found.symm.trans actual)
      split
      · rename_i absent
        rw [incoming] at absent
        contradiction
      · rename_i wire foundWire
        cases Option.some.inj (foundWire.symm.trans incoming)
        split
        · split
          · rename_i other accepted
            rw [rejected] at accepted
            contradiction
          · rfl
        · rename_i unintended
          exact False.elim (unintended entry.intended)
  obtain ⟨actual, read⟩ := Option.isSome_iff_exists.mp existsEntry
  apply (AdaptiveRejectionInventory.mem_identities start vocabulary encoding law _ receiver entry.index).mpr
  refine ⟨actual, List.mem_filterMap.mpr ⟨entry.index, List.mem_range.mpr (by simp only [List.length_append]; omega), read⟩, ?_⟩
  exact readAt_retains_its_actual_index start vocabulary encoding law _ receiver entry.index actual read

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem every_native_response_identity_is_paid_by_an_actual_rejection
    (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
    (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
    (answer : RejectionResponse.Answer model start vocabulary encoding law)
    (inside : answer ∈ RejectionResponse.journal model start past vocabulary encoding law) :
    RejectionResponse.Answer.id model start vocabulary encoding law answer ∈
      AdaptiveRejectionInventory.identities start vocabulary encoding law past := by
  have prefixHistory : answer.pastStages <+: past :=
    (List.prefix_append _ _).trans
      (RejectionResponse.every_answer_retains_its_actual_source_prefix model start past vocabulary encoding law answer inside)
  obtain ⟨more, same⟩ := prefixHistory
  rw [← same]
  exact every_original_rejection_identity_survives_actual_extension start vocabulary encoding law
    answer.pastStages more answer.response.receiver answer.response.evidence

theorem distinct_native_response_identities_have_the_same_source_budget
    (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
    (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
    (allowance : Nat) (compliant : AdaptiveRejectionHistory.Compliant start allowance past) :
    ((RejectionResponse.journal model start past vocabulary encoding law).map
      (RejectionResponse.Answer.id model start vocabulary encoding law)).toFinset.card ≤
        AdaptiveReceptionBudget.capacity (code := model.source.code) := by
  have included : ((RejectionResponse.journal model start past vocabulary encoding law).map
      (RejectionResponse.Answer.id model start vocabulary encoding law)).toFinset ⊆
        AdaptiveRejectionInventory.identities start vocabulary encoding law past := by
    intro id member
    obtain ⟨answer, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact every_native_response_identity_is_paid_by_an_actual_rejection vocabulary model start past encoding law answer inside
  exact (Finset.card_le_card included).trans
    (AdaptiveRejectionHistory.the_actual_history_generates_its_own_rejection_capacity start vocabulary encoding law allowance past compliant)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionClaims
