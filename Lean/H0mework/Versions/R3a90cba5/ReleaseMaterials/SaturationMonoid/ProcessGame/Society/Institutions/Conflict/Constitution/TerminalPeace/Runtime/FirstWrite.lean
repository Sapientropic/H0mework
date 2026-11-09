import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Gate

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open ExposureGuard

noncomputable section

abbrev WarVisit := Visit Original.seed Original.community Original.history (fun _ => True)
abbrev WarScheduler := Scheduler Bool Bool Bool Unit Unit

def openProbe : Probe (fun _ : Original.Word => True) := fun _ => some ⟨trivial⟩

def opening : WarVisit :=
  Visit.start Original.state
    (Reparation.Actual.the_live_ledger_contains_exactly_the_original_losses
      Original.seed Original.community Original.history) trivial

/-- The installation visit is the source's own material-free recourse
input. Later proposals are still dispatched by the original Scheduler. -/
def firstWrite (answers : OwnerAnswers Original.seed) : WarVisit :=
  opening.step answers (damageGate Original.community) openProbe stop

theorem the_original_installation_writes_its_literal_first_input (answers : OwnerAnswers Original.seed) :
    (firstWrite answers).history = Original.history ++ [stop] := by
  have empty : originalItems (seed := Original.seed) opening.history stop = [] :=
    the_open_original_recourse_dispatches_a_material_free_stop Original.cut Original.review
  have written := the_original_gate_keeps_every_safe_admissible_input
    (community := Original.community) (check := openProbe)
    (no_material_is_admitted opening.roster answers opening.history stop empty)
    (Boundary.Actual.no_material_write_has_no_damage _ _ _ empty) rfl
  change opening.history ++ (opening.verdict answers (damageGate Original.community) openProbe stop).emitted = _
  unfold Visit.verdict
  rw [written]
  rfl

theorem the_installation_preserves_the_exact_old_loss (answers : OwnerAnswers Original.seed) :
    Reparation.Actual.originalLosses Original.seed Original.community (firstWrite answers).history =
      [Original.occurrence] := by
  have kept := the_selected_suffix_preserves_all_original_loss_addresses
    (opening.verdict answers (damageGate Original.community) openProbe stop)
  exact kept.trans Original.the_original_loss_is_the_only_filed_occurrence

theorem the_installation_is_the_original_whole_write (answers : OwnerAnswers Original.seed) :
    Quantities.Recorded Original.seed (firstWrite answers).history ∧
      HEq (firstWrite answers).state (Receipts.writeAfter answers Original.state [stop]) := by
  refine ⟨Quantities.record _ _, ?_⟩
  let emitted := (opening.verdict answers (damageGate Original.community) openProbe stop).emitted
  have exactWord : emitted = [stop] := by
    have literal := the_original_installation_writes_its_literal_first_input answers
    change Original.history ++ emitted = Original.history ++ [stop] at literal
    exact List.append_cancel_left literal
  change HEq (Receipts.writeAfter answers Original.state emitted) (Receipts.writeAfter answers Original.state [stop])
  have transport (left right : Original.Word) (same : left = right) :
      HEq (Receipts.writeAfter answers Original.state left) (Receipts.writeAfter answers Original.state right) := by
    subst right
    rfl
  exact transport _ _ exactWord

private theorem a_material_free_installation_needs_no_answers (left right : OwnerAnswers Original.seed) :
    Receipts.writeAfter left Original.state [stop] = Receipts.writeAfter right Original.state [stop] := by
  have empty : Boundary.Actual.items Original.cut stop = [] :=
    the_open_original_recourse_dispatches_a_material_free_stop Original.cut Original.review
  have base : Receipts.writeAfter left Original.state [] = Receipts.writeAfter right Original.state [] := by
    unfold Receipts.writeAfter
    rw [List.reverseRecOn_nil, List.reverseRecOn_nil]
  change Receipts.writeAfter left Original.state ([] ++ [stop]) = Receipts.writeAfter right Original.state ([] ++ [stop])
  rw [Receipts.writeAfter_snoc, Receipts.writeAfter_snoc, base]
  have positions : Reparation.Actual.Allocation.itemPositions (seed := Original.seed) (Original.history ++ []) stop = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [Reparation.Actual.Allocation.itemPositions, List.length_finRange, List.append_nil]
    exact congrArg List.length empty
  unfold Receipts.writeTick
  rw [positions]
  rfl

private theorem same_whole_visit (left right : WarVisit)
    (history : left.history = right.history) (state : HEq left.state right.state) : left = right := by
  cases left
  cases right
  cases history
  cases state
  rfl

/-- No input stream supplies the initial protected world. It is the one
original recourse write after the actual loss. -/
def protectedCut : WarVisit := firstWrite (fun _ _ _ _ => false)

theorem every_installation_reaches_the_same_whole_protected_cut (answers : OwnerAnswers Original.seed) :
    firstWrite answers = protectedCut := by
  have old := the_original_installation_writes_its_literal_first_input answers
  have canonical := the_original_installation_writes_its_literal_first_input (fun _ _ _ _ => false)
  apply same_whole_visit _ _ (old.trans canonical.symm)
  exact (the_installation_is_the_original_whole_write answers).2.trans
    ((heq_of_eq (a_material_free_installation_needs_no_answers answers _)).trans
      (the_installation_is_the_original_whole_write _).2.symm)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
