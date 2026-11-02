import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Review
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {reference : Program model.source.code (horizon domain)}

def tail (work : Work model domain original reference) : Program model.source.code (horizon domain) :=
  clip (horizon domain) (Splice.word (work.programme.controls.drop work.past.length))

theorem reconstruct (work : Work model domain original reference) :
    extension (horizon domain) work.past (tail work) = work.programme := by
  unfold tail
  rw [tail_normalization_does_not_change_any_consumed_prefix_extension]
  have joined : work.past ++ work.programme.controls.drop work.past.length = work.programme.controls := by
    calc
      _ = work.programme.controls.take work.past.length ++ work.programme.controls.drop work.past.length :=
        congrArg (fun earlier => earlier ++ work.programme.controls.drop work.past.length) work.retained.symm
      _ = _ := List.take_append_drop _ _
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change (work.past ++ work.programme.controls.drop work.past.length).take (horizon domain) = work.programme.controls
  rw [joined,List.take_of_length_le work.programme.bounded]

theorem the_full_original_domain_independently_reviews_every_generated_plan
    (work : Work model domain original reference) :
    verify model domain original [] reference work.programme = true := by
  have same : extension (horizon domain) [] work.programme = work.programme := by
    change clip (horizon domain) work.programme = work.programme
    exact Complete.clipping_a_bounded_program_is_itself _
  apply (verify_iff model domain original [] reference work.programme).mpr
  rw [same]
  exact ⟨work.accepted,fun other accepted => work.maximal _ accepted⟩

theorem the_locked_past_and_all_finite_future_tails_are_independently_reviewed
    (work : Work model domain original reference) :
    verify model domain original work.past reference (tail work) = true := by
  apply (verify_iff model domain original work.past reference (tail work)).mpr
  rw [reconstruct]
  exact ⟨work.accepted,fun other accepted => work.maximal _ accepted⟩


theorem every_available_original_full_responsibility_improvement_is_retained
    (work : Work model domain original reference)
    (available : ∃ other : Program model.source.code (horizon domain),
      Selection.acceptable model domain original reference other ∧
        Improves model domain original reference other) :
    Improves model domain original reference work.programme := by
  constructor
  · exact Selection.acceptance_bounds_every_benefit model domain original _ _ work.accepted
  · intro backward
    obtain ⟨other,accepted,strict⟩ := available
    apply work.maximal other accepted
    constructor
    · intro axis inside
      exact (strict.1 axis inside).trans (backward axis inside)
    · intro reverse
      apply strict.2
      intro axis inside
      exact (backward axis inside).trans (reverse axis inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Review
