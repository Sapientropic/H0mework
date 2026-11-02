import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Observation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Proposal
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code)
  (record : Publication.Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

  (initial : List (View (code := model.source.code)))

abbrev past := Observation.controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
abbrev posterior := Observation.posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
abbrev prior := record.plan.choice.policy.protocol
abbrev priorTail := clip (horizon domain) (Splice.word ((prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length))
abbrev learned := Rolling.Receipt.rule model (posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) original (priorTail model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record)
  ((prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).at original (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length)
abbrev proposed := extension (horizon domain) (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (Splice.word [learned model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial])

inductive Decision where
  | admitted (accepted : Selection.acceptable model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial))
  | refused (rejected : Selection.Rejection model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial))

def inspect : Decision model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial :=
  match Distributed.inspect (Selection.holds model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial))
      (Replanning.rows model domain) with
  | .accepted all => .admitted all
  | .rejected row generated broken => .refused ⟨row,generated,broken⟩

def programme : Program model.source.code (horizon domain) :=
  match inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial with
  | .admitted _ => proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  | .refused _ => prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record

theorem the_original_paid_and_communication_prefix_is_within_the_original_domain :
    (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ≤ horizon domain := by
  have retained := (Plan.eligible_iff model domain original reference worker quote quotas record.plan.announcements record.plan.choice.policy).mp record.plan.publicationPrefix
  have size := congrArg List.length retained
  have bound := record.plan.choice.policy.protocol.bounded
  simp only [List.length_take,List.length_append,List.length_replicate] at size
  change (reserved model original worker quote quotas ++ record.plan.announcements).length ≤ _
  simp only [List.length_append,List.length_replicate]
  omega

theorem the_generated_programme_retains_the_entire_actual_paid_and_communication_past :
    (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
  unfold programme
  cases inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial with
  | admitted accepted =>
      exact every_completion_preserves_the_committed_control_prefix (code := model.source.code) (horizon domain)
        (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (Splice.word [learned model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial])
        (the_original_paid_and_communication_prefix_is_within_the_original_domain model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record)
  | refused rejected =>
      simpa only [past,Observation.controls,List.length_append,List.length_replicate] using
        (Plan.eligible_iff model domain original reference worker quote quotas record.plan.announcements record.plan.choice.policy).mp record.plan.publicationPrefix

theorem full_original_responsibility_admission_or_the_exact_rejected_row :
    match inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial with
    | .admitted _accepted => Selection.acceptable model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
    | .refused rejected => ¬ Selection.holds model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (proposed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) rejected.row := by
  cases inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial with
  | admitted accepted => exact accepted
  | refused rejected => exact rejected.broken

theorem the_selected_programme_is_no_worse_than_the_pre_receipt_programme :
    Selection.acceptable model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) := by
  unfold programme
  cases inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial with
  | admitted accepted => exact accepted
  | refused rejected => exact Commitment.admissible_plan_is_its_own_valid_reference model domain original reference _ record.plan.choice.policy.accepted

theorem the_initial_reference_and_every_original_opponent_are_retained :
    Selection.acceptable model domain original reference (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) :=
  Selection.acceptable_trans model domain original _ _ _
    (the_selected_programme_is_no_worse_than_the_pre_receipt_programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) record.plan.choice.policy.accepted

private theorem nondomination_survives_nonstrict_improvement
    {Policy Coordinate : Type} (axes : List Coordinate) (benefit : Policy → Coordinate → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes benefit old other)
    (improved : Distributed.NoWorse axes benefit next old) :
    ¬ Distributed.Improves axes benefit next other := by
  intro strict
  apply maximal
  refine ⟨?_,?_⟩
  · intro axis member
    exact (strict.1 axis member).trans (improved axis member)
  · intro reverse
    apply strict.2
    intro axis member
    exact (improved axis member).trans (reverse axis member)

theorem no_original_paid_candidate_dominates_the_received_programme
    (other : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference)
    (inside : other ∈ Prefix.candidates model domain original (reserved model original worker quote quotas) reference) :
    ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
      (Selection.benefit model domain original) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) other.protocol := by
  exact nondomination_survives_nonstrict_improvement
    (Selection.axes (fuel := horizon domain) model domain) (Selection.benefit model domain original)
    (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) other.protocol
    (record.plan.choice.maximal other inside)
    (Selection.acceptance_bounds_every_benefit model domain original (prior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
      (the_selected_programme_is_no_worse_than_the_pre_receipt_programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial))


def tail : Program model.source.code (horizon domain) :=
  clip (horizon domain) (Splice.word ((programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length))

theorem the_post_receipt_tail_reconstructs_the_same_full_original_programme :
    extension (horizon domain) (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) (tail model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) = programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial := by
  unfold tail
  rw [tail_normalization_does_not_change_any_consumed_prefix_extension]
  have joined : past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls := by
    calc
      _ = (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ++
          (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length :=
        congrArg (fun earlier => earlier ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length)
          (the_generated_programme_retains_the_entire_actual_paid_and_communication_past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).symm
      _ = _ := List.take_append_drop _ _
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length).take (horizon domain) = (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls
  rw [joined,List.take_of_length_le (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).bounded]

theorem the_locked_past_and_all_finite_futures_are_independently_reviewed :
    Prefix.verify model domain original (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) reference (tail model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) = true := by
  apply (Prefix.verify_iff _ _ _ _ _ _).mpr
  rw [the_post_receipt_tail_reconstructs_the_same_full_original_programme]
  refine ⟨the_initial_reference_and_every_original_opponent_are_retained model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial,?_⟩
  intro future accepted
  let appended := Splice.word (record.plan.announcements ++ future.2.controls)
  have same : extension (horizon domain) (reserved model original worker quote quotas) appended =
      extension (horizon domain) (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) future.2 := by
    unfold appended extension Splice.word past Observation.controls
    rw [List.append_assoc]
  have originalAccepted : Selection.acceptable model domain original reference
      (extension (horizon domain) (reserved model original worker quote quotas) appended) := by
    rw [same];exact accepted
  obtain ⟨candidate,included,identity⟩ := every_accepted_completion_is_generated model domain original
    (reserved model original worker quote quotas) reference ⟨_,appended⟩ originalAccepted
  have maximal := no_original_paid_candidate_dominates_the_received_programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial candidate included
  rw [identity,same] at maximal
  exact maximal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Proposal
