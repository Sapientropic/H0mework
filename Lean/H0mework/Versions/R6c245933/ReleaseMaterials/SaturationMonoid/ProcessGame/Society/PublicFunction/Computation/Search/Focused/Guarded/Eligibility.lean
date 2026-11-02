import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded.Comparison
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Tail
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal.Plan

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Segmented.Publication Segmented.Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : View (code := model.source.code))
  (send : Rule model.source.code) (announcements : List (Rule model.source.code))

abbrev fixed := Reservation.reservedBlock model original worker receiver quote quotas announcements
abbrev fee := Reservation.fee model original receiver quote
abbrev past := Segmented.reserved model original worker quote quotas
abbrev Candidate := Prefix.Candidate model domain original (past model original worker quote quotas) reference

theorem an_eligible_registration_is_a_literal_bounded_prefix
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    candidate.protocol.controls.take (fixed model original worker receiver quote quotas announcements).length =
      fixed model original worker receiver quote quotas announcements ∧
    (fixed model original worker receiver quote quotas announcements).length ≤ horizon domain := by
  have registered := (Bool.and_eq_true_iff.mp suitable).1
  have retained := (Reservation.eligible_iff model domain original reference worker receiver quote quotas announcements candidate).mp registered
  have size : (fixed model original worker receiver quote quotas announcements).length = quotas.length+announcements.length+1 := by
    simp only [fixed,Reservation.reservedBlock,Segmented.reserved,List.length_append,List.length_replicate,List.length_singleton]
  refine ⟨by simpa only [size] using retained,?_⟩
  have bound := congrArg List.length retained
  simp only [List.length_take,←size] at bound
  have fits : (fixed model original worker receiver quote quotas announcements).length ≤ candidate.protocol.controls.length :=
    calc
      _ = min (fixed model original worker receiver quote quotas announcements).length candidate.protocol.controls.length := bound.symm
      _ ≤ _ := Nat.min_le_right _ _
  exact fits.trans candidate.protocol.bounded

def programme (candidate : Candidate model domain original reference worker quote quotas) :=
  normalize domain original (fee model original receiver quote) candidate.protocol
    (fixed model original worker receiver quote quotas announcements).length

theorem the_eligible_normal_form_keeps_its_entire_registered_prefix
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    (programme model domain original reference worker receiver quote quotas announcements candidate).controls.take
      (fixed model original worker receiver quote quotas announcements).length = fixed model original worker receiver quote quotas announcements := by
  have retained := an_eligible_registration_is_a_literal_bounded_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable
  exact normalization_keeps_the_literal_prefix _ _ _ _ _ retained.1 retained.2

theorem the_eligible_normal_form_keeps_the_actual_paid_prefix
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    (programme model domain original reference worker receiver quote quotas announcements candidate).controls.take
      (past model original worker quote quotas).length = past model original worker quote quotas := by
  have retained := the_eligible_normal_form_keeps_its_entire_registered_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable
  have earlier := congrArg (List.take (past model original worker quote quotas).length) retained
  have size : (past model original worker quote quotas).length ≤ (fixed model original worker receiver quote quotas announcements).length := by
    simp only [past,fixed,Reservation.reservedBlock,List.length_append,List.length_singleton]
    omega
  rw [List.take_take,Nat.min_eq_left size] at earlier
  simpa only [fixed,Reservation.reservedBlock,past,List.append_assoc,List.take_append_length] using earlier

def representative (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    Candidate model domain original reference worker quote quotas :=
  ⟨Sparse.tail domain (past model original worker quote quotas)
      (programme model domain original reference worker receiver quote quotas announcements candidate),by
    rw [Sparse.extension_recovers_the_generated_protocol _ _ _
      (the_eligible_normal_form_keeps_the_actual_paid_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable)]
    exact (normalization_preserves_original_acceptance model domain original (fee model original receiver quote) candidate.protocol reference _).mpr candidate.accepted⟩

theorem the_representative_is_the_generated_complete_programme
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).protocol =
      programme model domain original reference worker receiver quote quotas announcements candidate :=
  Sparse.extension_recovers_the_generated_protocol _ _ _
    (the_eligible_normal_form_keeps_the_actual_paid_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable)

theorem the_source_clock_owner_is_in_the_generated_mask
    (member : point.point ∈ domain) (index : Nat)
    (owned : Renewal.owner model point index = some worker) : worker ∈ owners domain index := by
  apply List.mem_filterMap.mpr
  refine ⟨point.point,member,?_⟩
  exact owned

theorem normalization_keeps_the_original_renewal_profile
    (member : point.point ∈ domain)
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    Renewal.profile model domain original reference worker receiver quote quotas point send announcements
      (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable) = true := by
  have originalProfile := (Bool.and_eq_true_iff.mp suitable).2
  apply List.all_eq_true.mpr
  intro index inside
  have bound := List.mem_range.mp inside
  have retained := List.all_eq_true.mp originalProfile index inside
  unfold Renewal.checkAt at retained ⊢
  rw [the_representative_is_the_generated_complete_programme]
  by_cases earlier : index < Renewal.start model quotas announcements
  · simp only [if_pos earlier]
  · simp only [if_neg earlier] at retained ⊢
    have identity := normalization_keeps_each_fee_identity domain original (fee model original receiver quote) candidate.protocol
      (fixed model original worker receiver quote quotas announcements).length index bound
    by_cases marked : Renewal.FeeAt model domain receiver quotas point announcements index
    · simp only [if_pos marked,decide_eq_true_eq] at retained ⊢
      exact identity.mpr retained
    · simp only [if_neg marked,decide_eq_true_eq] at retained ⊢
      refine ⟨fun same => retained.1 (identity.mp same),?_⟩
      intro owned signal
      have kept := normalization_keeps_each_source_owned_row domain original (fee model original receiver quote) candidate.protocol
        (fixed model original worker receiver quote quotas announcements).length index bound worker signal
        (the_source_clock_owner_is_in_the_generated_mask model domain worker point member index owned)
      exact ⟨kept.1.trans (retained.2 owned signal).1,kept.2.trans (retained.2 owned signal).2⟩

theorem normalization_keeps_original_eligibility
    (member : point.point ∈ domain)
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    Renewal.eligible model domain original reference worker receiver quote quotas point send announcements
      (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable) = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,normalization_keeps_the_original_renewal_profile model domain original reference worker receiver quote quotas point send announcements member candidate suitable⟩
  apply (Reservation.eligible_iff _ _ _ _ _ _ _ _ _ _).mpr
  rw [the_representative_is_the_generated_complete_programme]
  have retained := the_eligible_normal_form_keeps_its_entire_registered_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable
  simpa only [fixed,Reservation.reservedBlock,Segmented.reserved,List.length_append,List.length_replicate,List.length_singleton] using retained

/-- This is a separate qualification catalogue; the original global comparison
    pool and its immutable paid prefix are not restricted to this block. -/
def eligibleTails : List (Program model.source.code (horizon domain)) :=
  (catalogue domain (fixed model original worker receiver quote quotas announcements) (fee model original receiver quote)).map
    (Sparse.tail domain (past model original worker quote quotas))

theorem every_original_eligible_candidate_has_a_generated_eligible_tail
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).tail ∈
      eligibleTails model domain original worker receiver quote quotas announcements := by
  apply List.mem_map.mpr
  refine ⟨programme model domain original reference worker receiver quote quotas announcements candidate,?_,rfl⟩
  exact every_guarded_programme_has_a_direct_representative _ _ _ _ _
    (an_eligible_registration_is_a_literal_bounded_prefix model domain original reference worker receiver quote quotas point send announcements candidate suitable).1

theorem the_eligible_representative_keeps_every_original_benefit
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    Selection.benefit model domain original
      (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).protocol =
      Selection.benefit model domain original candidate.protocol := by
  rw [the_representative_is_the_generated_complete_programme]
  exact normalization_preserves_every_original_benefit _ _ _ _ _ _

def globalChoice (choice : Prefix.Choice model domain original (past model original worker quote quotas) reference)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements choice.policy = true) :
    Prefix.Choice model domain original (past model original worker quote quotas) reference where
  policy := representative model domain original reference worker receiver quote quotas point send announcements choice.policy suitable
  original := List.mem_filterMap.mpr ⟨(representative model domain original reference worker receiver quote quotas point send announcements choice.policy suitable).tail,
    every_bounded_program_is_source_generated _ _ _,by
    simp only [Prefix.check,dif_pos (representative model domain original reference worker receiver quote quotas point send announcements choice.policy suitable).accepted]⟩
  maximal := by
    intro other inside
    have maximal := choice.maximal other inside
    simpa only [Distributed.Improves,Distributed.NoWorse,
      congrFun (the_eligible_representative_keeps_every_original_benefit model domain original reference worker receiver quote quotas point send announcements choice.policy suitable)] using maximal

structure Coverage : Prop where
  generated : ∀ candidate suitable,
    (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).tail ∈
      eligibleTails model domain original worker receiver quote quotas announcements
  eligible : ∀ candidate suitable,
    Renewal.eligible model domain original reference worker receiver quote quotas point send announcements
      (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable) = true
  comparison : ∀ candidate suitable,
    Selection.benefit model domain original
      (representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).protocol =
      Selection.benefit model domain original candidate.protocol
  maximal : ∀ choice suitable,
    Renewal.eligible model domain original reference worker receiver quote quotas point send announcements
      (globalChoice model domain original reference worker receiver quote quotas point send announcements choice suitable).policy = true

theorem source_generated_qualification_coverage (member : point.point ∈ domain) :
    Coverage model domain original reference worker receiver quote quotas point send announcements :=
  ⟨every_original_eligible_candidate_has_a_generated_eligible_tail model domain original reference worker receiver quote quotas point send announcements,
    normalization_keeps_original_eligibility model domain original reference worker receiver quote quotas point send announcements member,
    the_eligible_representative_keeps_every_original_benefit model domain original reference worker receiver quote quotas point send announcements,
    fun choice suitable => normalization_keeps_original_eligibility model domain original reference worker receiver quote quotas point send announcements member choice.policy suitable⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
