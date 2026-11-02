import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Comparison

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def tail (domain : List (Cursor code)) (past : List (Rule code))
    (programme : Program code (horizon domain)) : Program code (horizon domain) :=
  ⟨programme.controls.drop past.length,by
    rw [List.length_drop]
    exact (Nat.sub_le _ _).trans programme.bounded⟩

def tails (domain : List (Cursor code)) (past : List (Rule code)) : List (Program code (horizon domain)) :=
  (Focused.catalogue domain past).map (tail domain past)

theorem extension_recovers_the_generated_protocol
    (domain : List (Cursor code)) (past : List (Rule code))
    (programme : Program code (horizon domain))
    (retained : programme.controls.take past.length = past) :
    Prefix.extension (horizon domain) past (tail domain past programme) = programme := by
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change (past ++ programme.controls.drop past.length).take (horizon domain) = programme.controls
  have joined : past ++ programme.controls.drop past.length = programme.controls :=
    (congrArg (fun initial => initial ++ programme.controls.drop past.length) retained.symm).trans (List.take_append_drop _ _)
  rw [joined,List.take_of_length_le programme.bounded]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Program model.source.code (horizon domain))
  (room : past.length ≤ horizon domain)

def normal (raw : Program model.source.code (horizon domain)) :=
  Focused.normalize domain original (Prefix.extension (horizon domain) past raw) past.length

include room in
theorem the_generated_normal_protocol_retains_the_paid_past (raw : Program model.source.code (horizon domain)) :
    (normal model domain original past raw).controls.take past.length = past :=
  Focused.normalization_keeps_the_literal_paid_prefix domain past original _
    (Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ room) room

include room in
theorem the_generated_normal_tail_is_in_the_direct_catalogue (raw : Program model.source.code (horizon domain)) :
    tail domain past (normal model domain original past raw) ∈ tails domain past := by
  apply List.mem_map.mpr
  exact ⟨normal model domain original past raw,
    Focused.every_normalized_paid_programme_has_a_generated_sparse_representative domain past original _
      (Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ room),rfl⟩

include room in
theorem the_sparse_tail_rebuilds_its_complete_normal_protocol (raw : Program model.source.code (horizon domain)) :
    Prefix.extension (horizon domain) past (tail domain past (normal model domain original past raw)) = normal model domain original past raw :=
  extension_recovers_the_generated_protocol domain past _
    (the_generated_normal_protocol_retains_the_paid_past model domain original past room raw)

include room in
def representative (candidate : Prefix.Candidate model domain original past reference) :
    Prefix.Candidate model domain original past reference :=
  ⟨tail domain past (normal model domain original past candidate.tail),by
    rw [the_sparse_tail_rebuilds_its_complete_normal_protocol model domain original past room candidate.tail]
    exact (Focused.normalization_preserves_original_acceptance model domain original candidate.protocol past.length reference).mpr candidate.accepted⟩

include room in
theorem representative_preserves_every_original_benefit
    (candidate : Prefix.Candidate model domain original past reference) :
    Selection.benefit model domain original (representative model domain original past reference room candidate).protocol =
      Selection.benefit model domain original candidate.protocol := by
  change Selection.benefit model domain original (Prefix.extension _ _ _) = _
  dsimp only [representative]
  rw [the_sparse_tail_rebuilds_its_complete_normal_protocol model domain original past room candidate.tail]
  exact Focused.the_normalizer_keeps_every_original_benefit model domain original candidate.protocol past.length


theorem normalization_preserves_each_original_test
    (raw : Program model.source.code (horizon domain)) (row : Replanning.Row model domain) :
    Selection.holds model domain original reference (normal model domain original past raw) row ↔
      Selection.holds model domain original reference (Prefix.extension (horizon domain) past raw) row := by
  rcases row with ⟨world,table,test⟩
  simp only [Selection.holds,normal]
  rw [Focused.the_normalizer_keeps_each_complete_comparison_row model domain original
    (Prefix.extension (horizon domain) past raw) past.length world table]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
