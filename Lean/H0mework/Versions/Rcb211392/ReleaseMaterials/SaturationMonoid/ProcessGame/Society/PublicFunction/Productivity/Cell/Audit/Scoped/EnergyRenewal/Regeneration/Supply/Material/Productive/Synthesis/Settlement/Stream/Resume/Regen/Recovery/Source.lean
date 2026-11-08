import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Opening
import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {seed : Seed} {oldRequests : Requests.Source} {permission : Material.Mode} {baseCut : Nat}
  (source : Inherited seed oldRequests permission baseCut)
  (requests : Requests.Source) (authority : Authority) (index : Nat)

structure Cut where
  private mk ::
  after : Regen.Runtime.Result source requests authority index
  exactAfter : after = Regen.Runtime.consume source requests authority index

def fromActual : Cut source requests authority index :=
  ⟨Regen.Runtime.consume source requests authority index, rfl⟩

private theorem original_result_unique
    (left right : Regen.Runtime.Result source requests authority index) : left = right := by
  have frame := left.frameExact.trans right.frameExact.symm
  have account := left.accountExact.trans right.accountExact.symm
  cases left
  cases right
  cases frame
  cases account
  rfl

def fromRecorded (read : Regen.Runtime.Result source requests authority index) : Cut source requests authority index :=
  ⟨read, original_result_unique source requests authority index read
    (Regen.Runtime.consume source requests authority index)⟩

def runFrom (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (priorSteps : Nat) (before : Frame seed.basis) : Nat → Frame seed.basis
  | 0 => before
  | n + 1 =>
    step seed requests authority permission (priorSteps + (n + 1))
      (runFrom seed requests authority permission priorSteps before n)

abbrev handoff : Nat := baseCut + 1 + (index + 1)

variable {source requests authority index} (cut : Cut source requests authority index)

abbrev OpeningAt := OpeningReady seed.basis.origin.scope cut.after.frame.raw cut.after.account

def opening :
    PLift (OpeningAt cut) ⊕ OpeningObstruction seed.basis.origin.scope cut.after.frame.raw cut.after.account :=
  inspectOpening seed.basis.origin.scope cut.after.frame.raw cut.after.account

def admittedWord (offset : Nat) (frame : Frame seed.basis) : List JointAction :=
  match opening cut with
  | .inl _ => word seed requests authority permission (index + 1 + (offset + 1)) frame
  | .inr _ => []

def admittedStep (offset : Nat) (frame : Frame seed.basis) : Frame seed.basis :=
  match opening cut with
  | .inl _ => step seed requests authority permission (index + 1 + (offset + 1)) frame
  | .inr _ => ⟨Supply.initialMemo ((law seed.basis.origin.scope).next frame.raw []), frame.protocol⟩

theorem admitted_word_when_ready (ready : OpeningAt cut) (offset : Nat) (frame : Frame seed.basis) :
    admittedWord cut offset frame = word seed requests authority permission (index + 1 + (offset + 1)) frame := by
  unfold admittedWord
  split
  · rfl
  · rename_i reason _
    exact (reason.excludes ready).elim

theorem admitted_step_when_ready (ready : OpeningAt cut) (offset : Nat) (frame : Frame seed.basis) :
    admittedStep cut offset frame = step seed requests authority permission (index + 1 + (offset + 1)) frame := by
  unfold admittedStep
  split
  · rfl
  · rename_i reason _
    exact (reason.excludes ready).elim

theorem admitted_step_uses_the_word (offset : Nat) (frame : Frame seed.basis) :
    (admittedStep cut offset frame).raw = (law seed.basis.origin.scope).next frame.raw (admittedWord cut offset frame) := by
  unfold admittedStep admittedWord
  split
  · exact step_uses_the_selected_word seed requests authority permission _ frame
  · exact Supply.initialMemo_exact _

def run : Nat → Frame seed.basis
  | 0 => cut.after.frame
  | offset + 1 => admittedStep cut offset (run offset)

theorem run_uses_original_frame_when_ready (ready : OpeningAt cut) (offset : Nat) :
    run cut offset = runFrom seed requests authority permission (index + 1) cut.after.frame offset := by
  induction offset with
  | zero => rfl
  | succ offset earlier =>
    change admittedStep cut offset (run cut offset) = _
    rw [admitted_step_when_ready cut ready, earlier]
    rfl

def input : Finance.Input :=
  let original := Regen.input source requests authority
  let emitted (current : Current) :=
    let ordinal := current.round - original.initial.round
    if ordinal < handoff (baseCut := baseCut) index then ProgrammeSource.wordAt original current
    else
      let offset := ordinal - handoff (baseCut := baseCut) index
      admittedWord cut offset (run cut offset)
  { original with emission? := some emitted }

local notation "old" => Regen.input source requests authority
local notation "revised" => input cut
local notation "atCut" => handoff (baseCut := baseCut) index

theorem material_law_eq : (revised).law = (old).law := rfl

theorem original_current_prefix (ordinal : Nat) (prior : ordinal ≤ atCut) :
    (ProgrammeHistory.visitAt revised ordinal).current = (ProgrammeHistory.visitAt old ordinal).current := by
  induction ordinal with
  | zero => rfl
  | succ ordinal earlier =>
    have within : ordinal < atCut := by omega
    change ProgrammeSource.next revised (ProgrammeHistory.visitAt revised ordinal).current =
      ProgrammeSource.next old (ProgrammeHistory.visitAt old ordinal).current
    rw [earlier (by omega)]
    have words : ProgrammeSource.wordAt revised
        (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current) =
      ProgrammeSource.wordAt old (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current) := by
      change (if (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current).round -
          (old).initial.round < atCut then _ else _) = _
      rw [ProgrammeHistory.visit_round old ordinal, Nat.add_sub_cancel_left, if_pos within]
    generalize (ProgrammeHistory.visitAt old ordinal).current = current at words ⊢
    cases current with
    | bootstrap => rfl
    | running raw past =>
      change ProgrammeSource.wordAt revised raw = ProgrammeSource.wordAt old raw at words
      change ProgrammeSource.Current.running ((law seed.basis.origin.scope).next raw (ProgrammeSource.wordAt revised raw)) (past ++ [raw]) =
        ProgrammeSource.Current.running ((law seed.basis.origin.scope).next raw (ProgrammeSource.wordAt old raw)) (past ++ [raw])
      rw [words]

theorem selected_word (offset : Nat) :
    ProgrammeSource.rawEvent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current =
      admittedWord cut offset (run cut offset) := by
  have positive : 0 < atCut + offset := by dsimp only [handoff]; omega
  obtain ⟨prior, successor⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have emitted : ProgrammeSource.rawEvent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current =
      ProgrammeSource.wordAt revised (ProgrammeSource.rawCurrent revised
        (ProgrammeHistory.visitAt revised (atCut + offset)).current) := by
    rw [successor]
    change ProgrammeSource.rawEvent revised
        (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised prior).current) =
      ProgrammeSource.wordAt revised (ProgrammeSource.rawCurrent revised
        (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised prior).current))
    generalize (ProgrammeHistory.visitAt revised prior).current = current
    cases current <;> rfl
  rw [emitted]
  change (if (ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current).round -
      (old).initial.round < atCut then _ else _) = _
  have beyond : ¬ atCut + offset < atCut := by omega
  have round := ProgrammeHistory.visit_round revised (atCut + offset)
  change (ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current).round =
    (old).initial.round + (atCut + offset) at round
  rw [round, Nat.add_sub_cancel_left, if_neg beyond, Nat.add_sub_cancel_left]

theorem own_current (offset : Nat) :
    ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current = (run cut offset).raw := by
  induction offset with
  | zero =>
    rw [show atCut + 0 = atCut by rfl, original_current_prefix cut _ (le_refl _)]
    exact (Regen.own_current source requests authority (index + 1)).trans (congrArg Frame.raw cut.after.frameExact.symm)
  | succ offset earlier =>
    change ProgrammeSource.rawCurrent revised
      (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised (atCut + offset)).current) =
      (admittedStep cut offset (run cut offset)).raw
    rw [ProgrammeSource.actual_raw_next, earlier, selected_word, admitted_step_uses_the_word]
    rfl

theorem the_registered_world_is_the_same : ProgrammeSource.N revised = ProgrammeSource.N old := rfl

theorem original_row_at_handoff (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize old)) :
    HEq (ProgrammeSource.sourceEntry revised (ProgrammeHistory.visitAt revised atCut).current row)
      (ProgrammeSource.sourceEntry old (ProgrammeHistory.visitAt old atCut).current row) := by
  rw [original_current_prefix cut _ (le_refl _)]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
