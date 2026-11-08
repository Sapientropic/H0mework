import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionRegistration

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionProgress
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev count (past : List (EventHistory.Stage (code := model.source.code))) :=
  (RejectionResponse.journal model start past vocabulary encoding law).length

abbrev handled (past : List (EventHistory.Stage (code := model.source.code))) :=
  ((RejectionResponse.journal model start past vocabulary encoding law).map
    (RejectionResponse.Answer.id model start vocabulary encoding law)).toFinset

def remaining (past : List (EventHistory.Stage (code := model.source.code))) :=
  AdaptiveReceptionBudget.capacity (code := model.source.code) - count model start vocabulary encoding law past

theorem handled_card (past : List (EventHistory.Stage (code := model.source.code))) :
    (handled model start vocabulary encoding law past).card = count model start vocabulary encoding law past := by
  rw [handled, List.toFinset_card_of_nodup
    (RejectionRegistration.the_original_journal_never_registers_one_identity_twice model start vocabulary encoding law past), List.length_map]

theorem handled_subset (past : List (EventHistory.Stage (code := model.source.code))) :
    handled model start vocabulary encoding law past ⊆ AdaptiveRejectionInventory.identities start vocabulary encoding law past := by
  intro id member
  obtain ⟨answer, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact AdaptiveRejectionClaims.every_native_response_identity_is_paid_by_an_actual_rejection vocabulary model start past encoding law answer inside

theorem count_never_decreases (past later : List (EventHistory.Stage (code := model.source.code)))
    (extendsHistory : past <+: later) :
    count model start vocabulary encoding law past ≤ count model start vocabulary encoding law later := by
  obtain ⟨more, rfl⟩ := extendsHistory
  exact (RejectionRegistration.actual_history_extension_preserves_the_literal_original_journal
    model start vocabulary encoding law past more).length_le

theorem handled_never_disappears (past later : List (EventHistory.Stage (code := model.source.code)))
    (extendsHistory : past <+: later) :
    handled model start vocabulary encoding law past ⊆ handled model start vocabulary encoding law later := by
  obtain ⟨more, rfl⟩ := extendsHistory
  have retained := (RejectionRegistration.actual_history_extension_preserves_the_literal_original_journal
    model start vocabulary encoding law past more).map (RejectionResponse.Answer.id model start vocabulary encoding law)
  intro id member
  exact List.mem_toFinset.mpr (retained.sublist.subset (List.mem_toFinset.mp member))

theorem rejection_births_never_disappear (past later : List (EventHistory.Stage (code := model.source.code)))
    (extendsHistory : past <+: later) :
    AdaptiveRejectionInventory.identities start vocabulary encoding law past ⊆
      AdaptiveRejectionInventory.identities start vocabulary encoding law later := by
  obtain ⟨more, rfl⟩ := extendsHistory
  intro id member
  obtain ⟨entry, _, index⟩ :=
    (AdaptiveRejectionInventory.mem_identities start vocabulary encoding law past id.1 id.2).mp member
  have retained := AdaptiveRejectionClaims.every_original_rejection_identity_survives_actual_extension
    start vocabulary encoding law past more id.1 entry
  simpa only [index, Prod.mk.eta] using retained

theorem an_actual_ready_response_increases_the_count
    (past : List (EventHistory.Stage (code := model.source.code)))
    (response : RejectionResponse.Ready model start past vocabulary encoding law)
    (selected : RejectionResponse.produce model start past vocabulary encoding law = .ready response)
    (rival : Opponent model.source.code) :
    count model start vocabulary encoding law
      (past ++ [(RejectionResponse.protocol model start past vocabulary encoding law response, rival)]) =
      count model start vocabulary encoding law past + 1 := by
  have actual := congrArg List.length (RejectionResponse.a_generated_response_is_registered_once
    model start past vocabulary encoding law response rival selected)
  simpa only [List.length_map, List.length_append, List.length_singleton] using actual

theorem an_actual_compliant_response_strictly_consumes_remaining_capacity
    (past : List (EventHistory.Stage (code := model.source.code)))
    (response : RejectionResponse.Ready model start past vocabulary encoding law)
    (selected : RejectionResponse.produce model start past vocabulary encoding law = .ready response)
    (rival : Opponent model.source.code) (allowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start allowance
      (past ++ [(RejectionResponse.protocol model start past vocabulary encoding law response, rival)])) :
    remaining model start vocabulary encoding law
      (past ++ [(RejectionResponse.protocol model start past vocabulary encoding law response, rival)]) <
      remaining model start vocabulary encoding law past := by
  have growth := an_actual_ready_response_increases_the_count model start vocabulary encoding law past response selected rival
  have bound := RejectionRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
    model start vocabulary encoding law _ allowance compliant
  dsimp only [remaining, count] at growth bound ⊢
  omega

theorem unhandled_membership (past : List (EventHistory.Stage (code := model.source.code)))
    (id : Fin model.source.code.sites × Nat) :
    id ∈ UnifiedResponse.rejections model start vocabulary encoding law past ↔
      id ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law past ∧
      id ∉ handled model start vocabulary encoding law past := by
  simp only [UnifiedResponse.rejections, List.mem_filter, decide_eq_true_eq, handled, List.mem_toFinset]
  constructor
  · rintro ⟨member, absent⟩
    obtain ⟨receiver, _, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨entry, inside, same⟩ := List.mem_map.mp mapped
    subst id
    exact ⟨(AdaptiveRejectionInventory.mem_identities start vocabulary encoding law past receiver entry.index).mpr
      ⟨entry, inside, rfl⟩, absent⟩
  · rintro ⟨member, absent⟩
    obtain ⟨entry, inside, same⟩ :=
      (AdaptiveRejectionInventory.mem_identities start vocabulary encoding law past id.1 id.2).mp member
    refine ⟨List.mem_flatMap.mpr ⟨id.1, List.mem_finRange _, List.mem_map.mpr ⟨entry, inside, ?_⟩⟩, absent⟩
    exact Prod.ext rfl same

theorem exhausting_the_source_response_capacity_clears_the_actual_rejections
    (past : List (EventHistory.Stage (code := model.source.code))) (allowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start allowance past)
    (saturated : AdaptiveReceptionBudget.capacity (code := model.source.code) ≤ count model start vocabulary encoding law past) :
    UnifiedResponse.rejections model start vocabulary encoding law past = [] := by
  have bound := AdaptiveRejectionHistory.the_actual_history_generates_its_own_rejection_capacity start vocabulary encoding law allowance past compliant
  have same := Finset.eq_of_subset_of_card_le (handled_subset model start vocabulary encoding law past)
    (bound.trans (saturated.trans_eq (handled_card model start vocabulary encoding law past).symm))
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro id member
  obtain ⟨inside, absent⟩ := (unhandled_membership model start vocabulary encoding law past id).mp member
  exact absent (same.symm ▸ inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionProgress
