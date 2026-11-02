import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure.Raw
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section

private inductive CheckedPrefix {Row : Type} (holds : Row → Prop) (rows : List Row) where
  | accepted (all : ∀ row ∈ rows,holds row)
  | refused (paidPrefix : List Row) (item : Row) (tail : List Row)
      (split : rows = paidPrefix ++ item :: tail)
      (earlier : ∀ row ∈ paidPrefix,holds row) (broken : ¬ holds item)

private def inspectPrefix {Row : Type} (holds : Row → Prop) [DecidablePred holds] :
    (rows : List Row) → CheckedPrefix holds rows
  | [] => .accepted (by simp)
  | head :: tail =>
      if valid : holds head then
        match inspectPrefix holds tail with
        | .accepted all => .accepted (by
            intro row member
            rcases List.mem_cons.mp member with same | later
            · exact same ▸ valid
            · exact all row later)
        | .refused paidPrefix item rest split earlier broken =>
            .refused (head::paidPrefix) item rest (by rw [split];rfl) (by
              intro row member
              rcases List.mem_cons.mp member with same | later
              · exact same ▸ valid
              · exact earlier row later) broken
      else .refused [] head tail rfl (by simp) valid

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (original : Rule model.source.code) (baseline : Whole.Program model.source.code fuel)
  (point : Cursor model.source.code) (rival : Opponent model.source.code)

def source := Future.target point.source point.entry point.cut
  (controller point original baseline rival) (schedule point original baseline).val

def actual (offset : Nat) := (source model original baseline point rival).actualExecution (depth point+offset)
abbrev Offset := Fin (Cut.horizon point.source point.entry point.cut)
abbrev Item := ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument

/-- The first original failure keeps every earlier complete word and every
accepted raw item in this word. Requests and intermediate currents are literal. -/
structure Fault where
  offset : Offset model point
  earlierOffsets : List (Offset model point)
  laterOffsets : List (Offset model point)
  offsetSplit : List.finRange (Cut.horizon point.source point.entry point.cut) =
    earlierOffsets ++ offset :: laterOffsets
  earlierLegal : ∀ ordinal ∈ earlierOffsets,
    Open.Legal model.source.code.law
      (actual model original baseline point rival ordinal.val).before
      (actual model original baseline point rival ordinal.val).submitted
  paidPrefix : List (Item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  item : Item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  tail : List (Item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  itemSplit : model.source.code.law.rawItems
      (actual model original baseline point rival offset.val).before
      (actual model original baseline point rival offset.val).submitted = paidPrefix ++ item :: tail
  prefixValid : ∀ prior ∈ paidPrefix,model.source.code.law.Valid prior.before prior.request
  refused : ¬ model.source.code.law.Valid item.before item.request

theorem initial_before_is_original :
    (actual model original baseline point rival 0).before = point.source.currentAt (depth point+1) := by
  have newly := (source model original baseline point rival).feedback_current_is_actual
    (Future.takeover point.source point.entry point.cut (controller point original baseline rival)) rfl rfl point.cut
  have old := point.source.feedback_current_is_actual point.entry rfl rfl point.cut
  have same := congrArg Feedback.State.current (Future.complete_state_before point.source point.entry point.cut
    (controller point original baseline rival) (schedule point original baseline).val point.cut (Nat.le_refl _))
  have aligned := newly.trans (same.trans old.symm)
  change (source model original baseline point rival).currentAt (depth point+0+1) =
    point.source.currentAt (depth point+1)
  have address : depth point+1 = point.source.history.length+2+point.cut := by
    change point.history.length+1+point.cut+1 = point.history.length+2+point.cut
    omega
  rw [Nat.add_zero,address]
  exact aligned

namespace Fault
variable {model original baseline point rival}
  (fault : Fault model original baseline point rival)
include fault

theorem item_is_original : fault.item ∈ model.source.code.law.rawItems
    (actual model original baseline point rival fault.offset.val).before
    (actual model original baseline point rival fault.offset.val).submitted := by
  rw [fault.itemSplit]
  exact List.mem_append_right _ List.mem_cons_self

theorem request_is_unchanged : fault.item.request ∈
    (actual model original baseline point rival fault.offset.val).submitted := by
  have member : fault.item.request ∈ (model.source.code.law.rawItems
      (actual model original baseline point rival fault.offset.val).before
      (actual model original baseline point rival fault.offset.val).submitted).map ExecutionItem.request :=
    List.mem_map.mpr ⟨fault.item,fault.item_is_original,rfl⟩
  change fault.item.request ∈ (model.source.code.law.execute
    (actual model original baseline point rival fault.offset.val).before 0
    (actual model original baseline point rival fault.offset.val).submitted).items.map ExecutionItem.request at member
  rw [RawLaw.inventory_requests_exact] at member
  exact member

theorem breaks_actual_legality : ¬ Failure.legal model original baseline point rival = true := by
  intro valid
  have all := (rawLegal_iff point (controller point original baseline rival)
    (schedule point original baseline)).mp valid fault.offset.val fault.offset.isLt
  exact fault.refused (all fault.item fault.item_is_original)

/-- Refuting a generated response yields the same original admission row. -/
def originalRejection {domain : List (Cursor model.source.code)}
    (world : Replanning.Point model domain) (same : point = world.val) :
    Selection.Rejection model domain original baseline baseline := by
  subst point
  exact ⟨Failure.row model domain world rival .legal,Replanning.every_row_is_source_generated _ _ _,
    fun kept => fault.breaks_actual_legality
      ((Failure.legal_is_original model domain original baseline world rival).mpr kept)⟩
end Fault

inductive Result where
  | legal (checked : Failure.legal model original baseline point rival = true)
  | refused (fault : Fault model original baseline point rival)

/-- The scan never rebases a request or constructs the external table catalogue. -/
def inspect : Result model original baseline point rival :=
  match inspectPrefix (fun ordinal : Offset model point =>
      Open.Legal model.source.code.law
        (actual model original baseline point rival ordinal.val).before
        (actual model original baseline point rival ordinal.val).submitted)
      (List.finRange (Cut.horizon point.source point.entry point.cut)) with
  | .accepted all => .legal (by
      apply (rawLegal_iff point (controller point original baseline rival) (schedule point original baseline)).mpr
      intro offset bounded
      exact all ⟨offset,bounded⟩ (List.mem_finRange _))
  | .refused earlier offset later offsetSplit earlierLegal broken =>
      match inspectPrefix (fun item : Item (Party := Party) (Good := Good) (Port := Port)
          (Technology := Technology) (Instrument := Instrument) => model.source.code.law.Valid item.before item.request)
          (model.source.code.law.rawItems
            (actual model original baseline point rival offset.val).before
            (actual model original baseline point rival offset.val).submitted) with
      | .accepted all => False.elim (broken all)
      | .refused paidPrefix item tail itemSplit prefixValid refused =>
          .refused ⟨offset,earlier,later,offsetSplit,earlierLegal,paidPrefix,item,tail,itemSplit,prefixValid,refused⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure.Raw
