import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.History
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Source

set_option autoImplicit false
set_option maxRecDepth 8192

open private forPositions from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Input
open private original_body_is_single from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Source
open private a_paid_suffix_preserves_its_original_head from
  H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Execution (primitiveScript endAt)
open Reparation.Consumers (warCut)
open Conflict.Consumers.Evolving (R W)
open Allocation
open Allocation.Consumers (bodyPosition)

noncomputable section

abbrev bodyInput (request : R) := Allocation.Consumers.tick request

abbrev Row := Occurrence warCut (id : Bool → Bool) × Balance

theorem primitive_position_list (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request])) :
    itemPositions (seed := warCut) (primitiveScript earlier) (bodyInput request) =
      [bodyPosition earlier request paid] := by
  have width : (Boundary.Actual.items (endAt warCut (primitiveScript earlier)) (bodyInput request)).length = 1 :=
    congrArg List.length (original_body_is_single earlier request paid)
  have listed : (itemPositions (seed := warCut) (primitiveScript earlier) (bodyInput request)).length = 1 :=
    List.length_finRange.trans width
  obtain ⟨position, exactPosition⟩ := List.length_eq_one_iff.mp listed
  rw [exactPosition]
  congr 1
  apply Fin.ext
  have inside := position.isLt.trans_eq width
  change position.val = 0
  omega

theorem one_primitive_reads_its_one_item (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request])) (rows : List Row) :
    (atInput (primitiveScript earlier) (bodyInput request) rows).result =
      (atItem warCut (primitiveScript earlier) (bodyInput request) (bodyPosition earlier request paid) rows).changes.result := by
  unfold atInput
  rw [primitive_position_list earlier request paid]
  rfl

theorem the_following_native_tick_has_no_material (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request])) :
    Boundary.Actual.items (endAt warCut (primitiveScript earlier ++ [bodyInput request])) none = [] := by
  let cut := Conflict.Root.terminal warCut earlier
  have suffix := Conflict.Root.trace_after_prefix warCut _ earlier [request] paid.trace
  obtain ⟨ready, review, consents, valid, _⟩ := a_paid_suffix_preserves_its_original_head suffix
  have native := the_actual_body_must_consume_its_original_native_head cut request ready review consents valid
  rw [Quantities.Execution.endAt_append]
  exact Transport.native_step_has_no_material_items none native

/-- The canonical run uses the original material write and its following
native consumption. The second tick carries every already written row. -/
theorem the_two_original_ticks_write_the_generated_balances (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request])) :
    (run warCut id (primitiveScript (earlier ++ [request]))).stack.balances =
      (atItem warCut (primitiveScript earlier) (bodyInput request) (bodyPosition earlier request paid)
        ((run warCut id (primitiveScript earlier)).stack.balances ++
          (openings warCut id (primitiveScript earlier) (bodyInput request)).map (fun origin => (origin, opening origin)))).changes.result := by
  let past := primitiveScript earlier
  let postBody := past ++ [bodyInput request]
  let body := run warCut id postBody
  have full : primitiveScript (earlier ++ [request]) = postBody ++ [none] := by
    rw [Quantities.Execution.primitiveScript_append, primitiveScript, List.append_assoc]
    rfl
  have empty := the_following_native_tick_has_no_material earlier request paid
  have noneOpened : openings warCut id postBody none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ empty]
    rfl
  have native : (advance body none).stack.balances = body.stack.balances := by
    rw [written_balances, noneOpened, List.map_nil, List.append_nil]
    exact (no_original_items_keeps_rows postBody none body.stack.balances empty).1
  let rows := (run warCut id past).stack.balances ++
    (openings warCut id past (bodyInput request)).map (fun origin => (origin, opening origin))
  have material : body.stack.balances = (atInput past (bodyInput request) rows).result := by
    change (run warCut id (past ++ [bodyInput request])).stack.balances = _
    rw [run_snoc, written_balances]
  rw [full, run_snoc]
  exact native.trans (material.trans (one_primitive_reads_its_one_item earlier request paid rows))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint
