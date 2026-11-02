import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion.Material

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (fallback : Rule model.source.code) (raw : Program model.source.code)
  (rival : Opponent model.source.code)

private abbrev controls := Residual.scheduleAt point.source point.cut (schedule point fallback raw)
private abbrev input : Input model.source.code := ⟨controller point fallback raw rival,point.entry.budget⟩
private abbrev run (n : Nat) := Residual.run model.source.code (controls model point fallback raw)
  (input model point fallback raw rival) (Residual.seed point.source point.entry point.cut) n

variable (supported : ∀ n < Cut.horizon point.source point.entry point.cut,
    (stage model.source.code fallback raw n).supported) (checked : noSupply model.source.code = true)

include supported checked in
private theorem actual_words (n : Nat) (inside : n < Cut.horizon point.source point.entry point.cut) :
    ∀ request ∈ (source point fallback raw rival).actualExecution
      (point.source.history.length+1+(point.cut+n)) |>.submitted,creditless request = true := by
  rw [Future.future_word_is_actually_submitted point.source point.entry point.cut
    (controller point fallback raw rival) (schedule point fallback raw) rfl]
  exact each_actual_word_has_no_material_supply model.source.code checked _
    (supported_schedule point fallback raw supported n inside) _ _

include supported checked in
theorem the_complete_raw_credit_is_zero (party : Party) (good : Good) :
    (Finite.actualEvaluation model point fallback raw rival).value (.material (.credit party good)) = 0 := by
  change -((List.range (Cut.horizon point.source point.entry point.cut)).map _).sum = 0
  suffices zero : ((List.range (Cut.horizon point.source point.entry point.cut)).map fun offset =>
      model.source.code.law.totalCredit
        ((source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+offset)).interpreted.items party good).sum = 0 by
    rw [zero,neg_zero]
  apply List.sum_eq_zero
  intro amount member
  obtain ⟨offset,inside,rfl⟩ := List.mem_map.mp member
  let actual := (source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+offset)
  change model.source.code.law.totalCredit actual.interpreted.items party good = 0
  rw [actual.interpreted_exact]
  exact creditless_word_pays_no_credit model.source.code.law actual.before actual.submitted
    (by
      change ∀ request ∈ ((source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+offset)).submitted,creditless request = true
      rw [show Cut.start point.source point.cut-1+offset = point.source.history.length+1+(point.cut+offset) from by dsimp only [Cut.start];omega]
      exact actual_words model point fallback raw rival supported checked offset (List.mem_range.mp inside)) party good

include supported checked in
private theorem run_stock (n : Nat) (inside : n ≤ Cut.horizon point.source point.entry point.cut) (party : Party) (good : Good) :
    (run model point fallback raw rival n).current.stock party good ≤
      (Residual.seed point.source point.entry point.cut).current.stock party good := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have bounded : n < Cut.horizon point.source point.entry point.cut := by omega
    have noCredit := each_actual_word_has_no_material_supply model.source.code checked
      (controls model point fallback raw n) (supported_schedule point fallback raw supported n bounded)
      (input model point fallback raw rival) (run model point fallback raw rival n)
    have first := a_creditless_actual_word_cannot_increase_stock model.source.code.law
      (run model point fallback raw rival n).current _ noCredit party good
    exact first.trans (ih (by omega))

include supported checked in
theorem the_complete_raw_inventory_has_its_actual_source_bound (party : Party) (good : Good) :
    -((Residual.seed point.source point.entry point.cut).current.stock party good) ≤
      (Finite.actualEvaluation model point fallback raw rival).value (.material (.inventory party good)) := by
  change -_ ≤ -((source point fallback raw rival).currentAt (Cut.finish point.source point.entry point.cut)).stock party good
  rw [show Cut.finish point.source point.entry point.cut = point.source.history.length+2+
    (point.cut+Cut.horizon point.source point.entry point.cut) from by dsimp only [Cut.finish,Cut.start];omega]
  rw [(source point fallback raw rival).feedback_current_is_actual (entry point fallback raw rival) rfl rfl,
    Future.the_whole_future_run_is_the_actual_state]
  exact neg_le_neg (run_stock model point fallback raw rival supported checked _ (Nat.le_refl _) party good)

omit supported checked in
theorem every_actual_raw_debit_is_nonnegative (party : Party) (good : Good) :
    0 ≤ (Finite.actualEvaluation model point fallback raw rival).value (.material (.debit party good)) := by
  apply List.sum_nonneg
  intro amount inside
  obtain ⟨offset,_,rfl⟩ := List.mem_map.mp inside
  exact Institutions.Capitalism.Universal.Source.Material.total_nonnegative _ _
    (fun item _ => Institutions.Capitalism.Universal.Source.Material.paid_nonnegative model.source.code.law item party good)

omit supported checked in
theorem every_original_unpaid_coordinate_is_nonnegative (index : Nat) (holder : Party) :
    0 ≤ (Finite.actualEvaluation model point fallback raw rival).value (.unpaid index holder) := by
  let before := Normalization.RawProfile.before point.source point.entry point.cut (controller point fallback raw rival) (schedule point fallback raw)
  by_cases present : index < before.current.slots.length
  · let address : Fin before.current.slots.length := ⟨index,present⟩
    change 0 ≤ (Settlement.holdingAt _ address.val (model.source.code.parties.idxOf holder)).1
    rw [Normalization.RawProfile.holding_is_the_actual_slot_and_receipt]
    let migration := Normalization.RawProfile.migration point.source point.entry point.cut (controller point fallback raw rival) (schedule point fallback raw) address
    have member := List.mem_of_getElem? migration.present
    exact (Financial.generated_sound (source point fallback raw rival).input
      (Normalization.RawProfile.after point.source point.entry point.cut (controller point fallback raw rival) (schedule point fallback raw)) _ member).2 holder
  · have absent : (Normalization.RawProfile.holdings point.source point.entry point.cut
        (controller point fallback raw rival) (schedule point fallback raw))[index]? = none :=
      List.getElem?_eq_none (by simp only [Normalization.RawProfile.holdings,List.length_ofFn];exact Nat.le_of_not_gt present)
    change 0 ≤ (Settlement.holdingAt _ index (model.source.code.parties.idxOf holder)).1
    simp only [Settlement.holdingAt,absent,Option.getD_none,List.getElem?_nil,le_refl]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion
