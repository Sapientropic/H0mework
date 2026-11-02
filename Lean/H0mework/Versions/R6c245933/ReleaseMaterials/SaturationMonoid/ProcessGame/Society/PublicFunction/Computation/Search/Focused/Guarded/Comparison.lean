import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded.Catalogue
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Comparison

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation Continuation.Whole
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

theorem the_owner_projection_is_the_original_source_projection
    (domain : List (Cursor code)) (original fee : Rule code) (programme : Program code fuel) (frozen : Nat) :
    Focused.normalize domain original (normalize domain original fee programme frozen) 0 =
      Focused.normalize domain original programme 0 := by
  apply (Program.mk.injEq ..).mpr
  apply List.map_congr_left
  intro ordinal inside
  simp only [Focused.projected,Nat.not_lt_zero,ite_false,
    each_normalized_stage_is_generated domain original fee programme frozen ordinal (List.mem_range.mp inside)]
  unfold projected
  split
  · rfl
  · exact projection_keeps_the_owner_rows _ _ _ _

theorem normalization_keeps_the_literal_prefix
    (domain : List (Cursor code)) (fixed : List (Rule code)) (original fee : Rule code)
    (programme : Program code fuel) (retained : programme.controls.take fixed.length = fixed)
    (room : fixed.length ≤ Complete.horizon domain) :
    (normalize domain original fee programme fixed.length).controls.take fixed.length = fixed := by
  have size : fixed.length ≤ programme.controls.length := by
    have sizes := congrArg List.length retained
    simp only [List.length_take] at sizes
    omega
  apply Eq.trans (b := programme.controls.take fixed.length) ?_ retained
  apply List.ext_getElem
  · simp only [normalize,List.length_take,List.length_map,List.length_range]
    omega
  · intro index left right
    have inside : index < fixed.length := by
      have upper := List.length_take_le fixed.length (normalize domain original fee programme fixed.length).controls
      omega
    have present : index < programme.controls.length := inside.trans_le size
    simp only [List.getElem_take,normalize,List.getElem_map,List.getElem_range,projected,if_pos inside,
      Program.at,List.getElem?_eq_getElem present,Option.getD_some]

theorem normalization_keeps_each_fee_identity
    (domain : List (Cursor code)) (original fee : Rule code) (programme : Program code fuel) (frozen ordinal : Nat)
    (inside : ordinal < Complete.horizon domain) :
    (normalize domain original fee programme frozen).at original ordinal = fee ↔ programme.at original ordinal = fee := by
  rw [each_normalized_stage_is_generated _ _ _ _ _ _ inside]
  unfold projected
  split
  · rfl
  · exact projection_keeps_exact_fee_identity _ _ _ _

theorem projection_keeps_each_owned_row
    (active : List (Fin code.sites)) (fee rule : Rule code) (site : Fin code.sites) (signal : Fin code.signals)
    (owned : site ∈ active) : rowEqual code (project code active fee rule) rule (site,signal) := by
  unfold project
  split
  · rename_i same;subst rule;exact ⟨rfl,rfl⟩
  · split
    · exact mask_keeps_each_requested_row _ _ _ _ _ (.inl owned)
    · split
      · exact mask_keeps_each_requested_row _ _ _ _ _ (.inl owned)
      · contradiction

theorem normalization_keeps_each_source_owned_row
    (domain : List (Cursor code)) (original fee : Rule code) (programme : Program code fuel) (frozen ordinal : Nat)
    (inside : ordinal < Complete.horizon domain) (site : Fin code.sites) (signal : Fin code.signals)
    (owned : site ∈ owners domain ordinal) :
    rowEqual code ((normalize domain original fee programme frozen).at original ordinal) (programme.at original ordinal) (site,signal) := by
  rw [each_normalized_stage_is_generated _ _ _ _ _ _ inside]
  unfold projected
  split
  · exact ⟨rfl,rfl⟩
  · exact projection_keeps_each_owned_row _ _ _ _ _ owned

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (point : Cursor model.source.code) (member : point ∈ domain)
  (original fee : Rule model.source.code) (programme : Program model.source.code fuel) (frozen : Nat)

include member in
theorem normalization_preserves_the_complete_actual_input (rival : Opponent model.source.code) :
    (Continuation.Whole.source point original (normalize domain original fee programme frozen) rival).input =
      (Continuation.Whole.source point original programme rival).input := by
  calc
    _ = (Continuation.Whole.source point original
        (Focused.normalize domain original (normalize domain original fee programme frozen) 0) rival).input :=
      (Focused.the_normalizer_emits_the_same_complete_actual_input domain point member original _ 0 rival).symm
    _ = (Continuation.Whole.source point original (Focused.normalize domain original programme 0) rival).input := by
      rw [the_owner_projection_is_the_original_source_projection]
    _ = _ := Focused.the_normalizer_emits_the_same_complete_actual_input domain point member original programme 0 rival

include member in
theorem normalization_preserves_the_complete_evaluation (rival : Opponent model.source.code) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model point original (normalize domain original fee programme frozen) rival =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model point original programme rival := by
  calc
    _ = Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model point original (Focused.normalize domain original (normalize domain original fee programme frozen) 0) rival :=
      (Focused.the_normalizer_preserves_the_complete_responsibility_evaluation model domain point member original _ 0 rival).symm
    _ = Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model point original (Focused.normalize domain original programme 0) rival := by
      rw [the_owner_projection_is_the_original_source_projection]
    _ = _ := Focused.the_normalizer_preserves_the_complete_responsibility_evaluation model domain point member original programme 0 rival

theorem normalization_preserves_each_original_comparison_row
    (candidate : Program model.source.code (Complete.horizon domain)) (frozen : Nat)
    (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.readTable model domain original world (normalize domain original fee candidate frozen) table =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.readTable model domain original world candidate table :=
  normalization_preserves_the_complete_evaluation model domain world.val world.property original fee candidate frozen _

theorem normalization_preserves_every_original_benefit
    (candidate : Program model.source.code (Complete.horizon domain)) (frozen : Nat) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original (normalize domain original fee candidate frozen) =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original candidate := by
  funext axis
  cases axis <;> simp only [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit,normalization_preserves_each_original_comparison_row]

theorem normalization_preserves_original_acceptance
    (candidate reference : Program model.source.code (Complete.horizon domain)) (frozen : Nat) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable model domain original reference (normalize domain original fee candidate frozen) ↔
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable model domain original reference candidate := by
  rw [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable_iff_every_common_external_opponent,
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable_iff_every_common_external_opponent]
  apply forall_congr'
  intro world
  apply forall_congr'
  intro rival
  rw [normalization_preserves_the_complete_evaluation model domain world.val world.property original fee candidate frozen rival]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
