import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

structure Inherited (seed : Seed) (oldRequests : Requests.Source) (oldMode : Material.Mode) (cut : Nat) where
  private mk ::
  result : Resume.Runtime.Result seed oldRequests oldMode cut
  exactResult : result = Resume.Runtime.consume seed oldRequests oldMode cut

def inherit (seed : Seed) (oldRequests : Requests.Source) (oldMode : Material.Mode) (cut : Nat) :
    Inherited seed oldRequests oldMode cut :=
  ⟨Resume.Runtime.consume seed oldRequests oldMode cut, rfl⟩

def runFrom (seed : Seed) (requests : Requests.Source) (authority : Authority)
    (start : Frame seed.basis) : Nat → Frame seed.basis
  | 0 => start
  | ordinal + 1 => step seed requests authority (ordinal + 1) (runFrom seed requests authority start ordinal)

variable {seed : Seed} {oldRequests : Requests.Source} {oldMode : Material.Mode} {cut : Nat}
  (previous : Inherited seed oldRequests oldMode cut)
  (requests : Requests.Source) (authority : Authority)

def run : Nat → Frame seed.basis := runFrom seed requests authority previous.result.frame

theorem run_round (ordinal : Nat) :
    (run previous requests authority ordinal).raw.round = previous.result.frame.raw.round + ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal earlier =>
    change (step seed requests authority (ordinal + 1) (run previous requests authority ordinal)).raw.round = _
    rw [step_uses_the_selected_actual_word]
    change (run previous requests authority ordinal).raw.round + 1 = _
    rw [earlier]
    omega

def input : Finance.Input :=
  let original := Resume.input seed oldRequests oldMode
  let emitted (current : Current) :=
    let ordinal := current.round - original.initial.round
    if ordinal ≤ cut then ProgrammeSource.wordAt original current
    else
      let offset := ordinal - (cut + 1)
      word seed requests authority (offset + 1) (run previous requests authority offset)
  { original with emission? := some emitted }

theorem the_material_law_is_the_original_stream_law :
    (input previous requests authority).law = (Resume.input seed oldRequests oldMode).law := rfl

local notation "old" => Resume.input seed oldRequests oldMode
local notation "revised" => input previous requests authority

/-- The existing source keeps its whole physical current, including the
original past, through the handoff. The new word begins at that same cut. -/
theorem original_current_prefix (ordinal : Nat) (inOld : ordinal ≤ cut + 1) :
    (ProgrammeHistory.visitAt revised ordinal).current = (ProgrammeHistory.visitAt old ordinal).current := by
  induction ordinal with
  | zero => rfl
  | succ ordinal earlier =>
    have bound : ordinal ≤ cut := by omega
    change ProgrammeSource.next revised (ProgrammeHistory.visitAt revised ordinal).current =
      ProgrammeSource.next old (ProgrammeHistory.visitAt old ordinal).current
    rw [earlier (by omega)]
    have sameWord : ProgrammeSource.wordAt revised
        (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current) =
      ProgrammeSource.wordAt old (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current) := by
      change (if (ProgrammeSource.rawCurrent old (ProgrammeHistory.visitAt old ordinal).current).round -
          (old).initial.round ≤ cut then _ else _) = _
      rw [ProgrammeHistory.visit_round old ordinal, Nat.add_sub_cancel_left, if_pos bound]
    generalize (ProgrammeHistory.visitAt old ordinal).current = current at sameWord ⊢
    cases current with
    | bootstrap => rfl
    | running raw past =>
      change ProgrammeSource.wordAt revised raw = ProgrammeSource.wordAt old raw at sameWord
      change ProgrammeSource.Current.running ((law seed.basis.origin.scope).next raw (ProgrammeSource.wordAt revised raw)) (past ++ [raw]) =
        ProgrammeSource.Current.running ((law seed.basis.origin.scope).next raw (ProgrammeSource.wordAt old raw)) (past ++ [raw])
      rw [sameWord]

theorem selected_word_at_cut (ordinal : Nat) :
    ProgrammeSource.rawEvent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current =
      word seed requests authority (ordinal + 1) (run previous requests authority ordinal) := by
  have emitted : ProgrammeSource.rawEvent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current =
    ProgrammeSource.wordAt revised
      (ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current) := by
    rw [show cut + 1 + ordinal = cut + ordinal + 1 by omega]
    change ProgrammeSource.rawEvent revised
        (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised (cut + ordinal)).current) =
      ProgrammeSource.wordAt revised
        (ProgrammeSource.rawCurrent revised
          (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised (cut + ordinal)).current))
    generalize (ProgrammeHistory.visitAt revised (cut + ordinal)).current = prior
    cases prior <;> rfl
  rw [emitted]
  change (if (ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current).round -
      (old).initial.round ≤ cut then _ else _) = _
  have beyond : ¬ cut + 1 + ordinal ≤ cut := by omega
  have atRound := ProgrammeHistory.visit_round revised (cut + 1 + ordinal)
  change (ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current).round =
    (old).initial.round + (cut + 1 + ordinal) at atRound
  rw [atRound, Nat.add_sub_cancel_left, if_neg beyond, Nat.add_sub_cancel_left]

theorem own_current (ordinal : Nat) :
    ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current =
      (run previous requests authority ordinal).raw := by
  induction ordinal with
  | zero =>
    rw [show cut + 1 + 0 = cut + 1 by rfl, original_current_prefix previous requests authority _ (le_refl _)]
    exact (Resume.own_current seed oldRequests oldMode _).trans (congrArg Frame.raw previous.result.frameExact.symm)
  | succ ordinal earlier =>
    change ProgrammeSource.rawCurrent revised
      (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised (cut + 1 + ordinal)).current) =
        (step seed requests authority (ordinal + 1) (run previous requests authority ordinal)).raw
    rw [ProgrammeSource.actual_raw_next, earlier, selected_word_at_cut, step_uses_the_selected_actual_word]
    rfl

theorem the_registered_world_is_the_same : ProgrammeSource.N revised = ProgrammeSource.N old := rfl

theorem original_row_is_the_same_at_the_handoff
    (row : ProgrammeWorld.Row (ProgrammeSource.registrationSize old)) :
    HEq (ProgrammeSource.sourceEntry revised (ProgrammeHistory.visitAt revised (cut + 1)).current row)
      (ProgrammeSource.sourceEntry old (ProgrammeHistory.visitAt old (cut + 1)).current row) := by
  rw [original_current_prefix previous requests authority _ (le_refl _)]
  rfl

def handoffOccurrence :
    ConstructivePresentation
      ((ProgrammeSource.source old).toRootSource.actual.OccurrenceAt (ProgrammeHistory.visitAt old (cut + 1)).current)
      ((ProgrammeSource.source revised).toRootSource.actual.OccurrenceAt (ProgrammeHistory.visitAt revised (cut + 1)).current) where
  forward := fun _ => ProgrammeSource.emitted revised (ProgrammeHistory.visitAt revised (cut + 1)).current
  backward := fun _ => ProgrammeSource.emitted old (ProgrammeHistory.visitAt old (cut + 1)).current
  backward_forward := fun actual => (ProgrammeSource.occurrence_eq_emitted old actual).symm
  forward_backward := fun actual => (ProgrammeSource.occurrence_eq_emitted revised actual).symm

theorem handoff_is_the_exact_original_after :
    ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (cut + 1)).current =
      (Resume.Runtime.execution seed oldRequests oldMode cut).after := by
  rw [Resume.Runtime.actual_after_is_the_published_frame, ← previous.exactResult]
  exact own_current previous requests authority 0

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen
