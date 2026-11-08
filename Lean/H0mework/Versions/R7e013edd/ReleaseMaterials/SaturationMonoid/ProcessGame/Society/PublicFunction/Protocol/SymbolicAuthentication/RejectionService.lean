import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionService
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RejectionProgress

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

-- Availability is checked at the fresh local prefix, and the actual next row must execute it.
def ServedAt (past : List (EventHistory.Stage (code := model.source.code))) (n : Nat) : Prop :=
  ∃ response : RejectionResponse.Ready model start (past.take n) vocabulary encoding law,
    RejectionResponse.produce model start (past.take n) vocabulary encoding law = .ready response ∧
    ∃ rival, past[n]? = some (RejectionResponse.protocol model start (past.take n) vocabulary encoding law response, rival)

theorem actual_service_registers_one_new_response
    (past : List (EventHistory.Stage (code := model.source.code))) (n : Nat)
    (served : ServedAt model start vocabulary encoding law past n) :
    count model start vocabulary encoding law (past.take (n + 1)) =
      count model start vocabulary encoding law (past.take n) + 1 := by
  obtain ⟨response, selected, rival, actual⟩ := served
  rw [List.take_add_one, actual]
  exact an_actual_ready_response_increases_the_count model start vocabulary encoding law _ response selected rival

def ServiceWindows (past : List (EventHistory.Stage (code := model.source.code))) (birth width : Nat) : Prop :=
  ∀ k < AdaptiveReceptionBudget.capacity (code := model.source.code),
    UnifiedResponse.rejections model start vocabulary encoding law (past.take (birth + width * k)) ≠ [] →
    ∃ n, birth + width * k ≤ n ∧ n < birth + width * (k + 1) ∧
      ServedAt model start vocabulary encoding law past n

-- A birth horizon constrains incoming evidence, not completion or native disposition.
def BirthsWithin (past : List (EventHistory.Stage (code := model.source.code))) (birth : Nat) : Prop :=
  AdaptiveRejectionInventory.identities start vocabulary encoding law past ⊆
    AdaptiveRejectionInventory.identities start vocabulary encoding law (past.take birth)

theorem bounded_actual_service_clears_every_rejection_born_within_the_window
    (past : List (EventHistory.Stage (code := model.source.code))) (allowance birth width : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start allowance past)
    (births : BirthsWithin model start vocabulary encoding law past birth)
    (scheduled : ServiceWindows model start vocabulary encoding law past birth width)
    (room : birth + width * AdaptiveReceptionBudget.capacity (code := model.source.code) ≤ past.length) :
    let stop := birth + width * AdaptiveReceptionBudget.capacity (code := model.source.code)
    (past.take stop).length = stop ∧
    UnifiedResponse.rejections model start vocabulary encoding law (past.take stop) = [] ∧
    UnifiedResponse.rejections model start vocabulary encoding law past = [] := by
  let stop := birth + width * AdaptiveReceptionBudget.capacity (code := model.source.code)
  have covers : AdaptiveRejectionInventory.identities start vocabulary encoding law past ⊆
      handled model start vocabulary encoding law (past.take stop) := by
    intro id born
    by_contra unhandled
    have pendingAt : ∀ n, birth ≤ n → n ≤ stop →
        id ∈ UnifiedResponse.rejections model start vocabulary encoding law (past.take n) := by
      intro n afterBirth beforeStop
      apply (unhandled_membership model start vocabulary encoding law _ id).mpr
      refine ⟨rejection_births_never_disappear model start vocabulary encoding law _ _
        (List.take_prefix_take_left afterBirth) (births born), ?_⟩
      intro wasHandled
      exact unhandled (handled_never_disappears model start vocabulary encoding law _ _
        (List.take_prefix_take_left beforeStop) wasHandled)
    have progress : ∀ k ≤ AdaptiveReceptionBudget.capacity (code := model.source.code),
        k ≤ count model start vocabulary encoding law (past.take (birth + width * k)) := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro bounded
        have beforeStop : birth + width * k ≤ stop :=
          Nat.add_le_add_left (Nat.mul_le_mul_left width (by omega)) birth
        obtain ⟨n, lower, upper, service⟩ := scheduled k (by omega) (by
          intro empty
          have member := pendingAt (birth + width * k) (by omega) beforeStop
          rw [empty] at member
          contradiction)
        have before := count_never_decreases model start vocabulary encoding law
          (past.take (birth + width * k)) (past.take n) (List.take_prefix_take_left lower)
        have afterService := count_never_decreases model start vocabulary encoding law
          (past.take (n + 1)) (past.take (birth + width * (k + 1)))
          (List.take_prefix_take_left (show n + 1 ≤ birth + width * (k + 1) by omega))
        have paid := actual_service_registers_one_new_response model start vocabulary encoding law past n service
        have previous := ih (by omega)
        omega
    have enough := progress _ (Nat.le_refl _)
    have included := (handled_subset model start vocabulary encoding law (past.take stop)).trans
      (rejection_births_never_disappear model start vocabulary encoding law _ _ (List.take_prefix _ _))
    have bound := AdaptiveRejectionHistory.the_actual_history_generates_its_own_rejection_capacity
      start vocabulary encoding law allowance past compliant
    have same := Finset.eq_of_subset_of_card_le included
      (bound.trans (enough.trans_eq (handled_card model start vocabulary encoding law (past.take stop)).symm))
    exact unhandled (same.symm ▸ born)
  refine ⟨by simp only [List.length_take]; exact Nat.min_eq_left room, ?_, ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro id member
    obtain ⟨born, unhandled⟩ := (unhandled_membership model start vocabulary encoding law _ id).mp member
    exact unhandled (covers (rejection_births_never_disappear model start vocabulary encoding law _ _ (List.take_prefix _ _) born))
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro id member
    obtain ⟨born, unhandled⟩ := (unhandled_membership model start vocabulary encoding law _ id).mp member
    exact unhandled (handled_never_disappears model start vocabulary encoding law _ _ (List.take_prefix _ _) (covers born))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionService
