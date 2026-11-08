import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.AccountRun

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {seed : Seed} {oldRequests : Requests.Source} {oldPermission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests oldPermission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  (cut : Cut source requests authority index) (count : Nat)

/-- A continuation inherits the complete generated frame and account, not
just equal public balances or a newly issued copy of the old claims. -/
structure Snapshot where
  private mk ::
  frame : Frame seed.basis
  frameExact : frame = Recovery.run cut count
  account : Finance.Account
  accountExact : account = Financial.Family.continueVisits Finance.sources (Recovery.input cut)
    (handoff (baseCut := baseCut) index) count cut.after.account

def capture : Snapshot cut count :=
  ⟨Recovery.run cut count, rfl,
    Financial.Family.continueVisits Finance.sources (Recovery.input cut)
      (handoff (baseCut := baseCut) index) count cut.after.account, rfl⟩

variable {cut count} (original : Snapshot cut count)
  (futureRequests : Requests.Source) (futureAuthority : Authority) (futurePermission : Material.Mode)

abbrev startAt : Nat := handoff (baseCut := baseCut) index + count

def opening := inspectOpening seed.basis.origin.scope original.frame.raw original.account

def word (offset : Nat) (frame : Frame seed.basis) : List JointAction :=
  match opening original with
  | .inl _ => Recovery.word seed futureRequests futureAuthority futurePermission
      (index + 1 + count + (offset + 1)) frame
  | .inr _ => []

def step (offset : Nat) (frame : Frame seed.basis) : Frame seed.basis :=
  match opening original with
  | .inl _ => Recovery.step seed futureRequests futureAuthority futurePermission
      (index + 1 + count + (offset + 1)) frame
  | .inr _ => ⟨Supply.initialMemo ((law seed.basis.origin.scope).next frame.raw []), frame.protocol⟩

theorem step_uses_its_actual_word (offset : Nat) (frame : Frame seed.basis) :
    (step original futureRequests futureAuthority futurePermission offset frame).raw =
      (law seed.basis.origin.scope).next frame.raw
        (word original futureRequests futureAuthority futurePermission offset frame) := by
  unfold step word
  split
  · exact step_uses_the_selected_word seed futureRequests futureAuthority futurePermission _ frame
  · exact Supply.initialMemo_exact _

def evolve (offset : Nat) (frame : Frame seed.basis) : Nat → Frame seed.basis
  | 0 => frame
  | n + 1 => step original futureRequests futureAuthority futurePermission (offset + n)
      (evolve offset frame n)

def run : Nat → Frame seed.basis := evolve original futureRequests futureAuthority futurePermission 0 original.frame

theorem run_succ (n : Nat) :
    run original futureRequests futureAuthority futurePermission (n + 1) =
      step original futureRequests futureAuthority futurePermission n
        (run original futureRequests futureAuthority futurePermission n) := by
  simp only [run, evolve, Nat.zero_add]

theorem every_actual_after_generates_the_remaining_future (first later : Nat) :
    evolve original futureRequests futureAuthority futurePermission first
      (run original futureRequests futureAuthority futurePermission first) later =
        run original futureRequests futureAuthority futurePermission (first + later) := by
  induction later with
  | zero => simp only [evolve, Nat.add_zero]
  | succ later previous =>
    change step original futureRequests futureAuthority futurePermission (first + later) _ = _
    rw [previous]
    simpa only [Nat.add_assoc] using
      (run_succ original futureRequests futureAuthority futurePermission (first + later)).symm

def input : Finance.Input :=
  let old := Recovery.input cut
  let emitted (current : Current) :=
    let ordinal := current.round - old.initial.round
    if ordinal < startAt (baseCut := baseCut) (index := index) (count := count) then ProgrammeSource.wordAt old current
    else
      let offset := ordinal - startAt (baseCut := baseCut) (index := index) (count := count)
      word original futureRequests futureAuthority futurePermission offset
        (run original futureRequests futureAuthority futurePermission offset)
  { old with emission? := some emitted }

local notation "old" => Recovery.input cut
local notation "revised" => input original futureRequests futureAuthority futurePermission
local notation "atCut" => startAt (baseCut := baseCut) (index := index) (count := count)

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
      word original futureRequests futureAuthority futurePermission offset
        (run original futureRequests futureAuthority futurePermission offset) := by
  have positive : 0 < atCut + offset := by dsimp only [startAt, handoff]; omega
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
    ProgrammeSource.rawCurrent revised (ProgrammeHistory.visitAt revised (atCut + offset)).current =
      (run original futureRequests futureAuthority futurePermission offset).raw := by
  induction offset with
  | zero =>
    rw [show atCut + 0 = atCut by rfl,
      original_current_prefix original futureRequests futureAuthority futurePermission _ (le_refl _)]
    exact (Recovery.own_current cut count).trans (congrArg Frame.raw original.frameExact.symm)
  | succ offset earlier =>
    rw [run_succ]
    change ProgrammeSource.rawCurrent revised
      (ProgrammeSource.next revised (ProgrammeHistory.visitAt revised (atCut + offset)).current) =
      (step original futureRequests futureAuthority futurePermission offset
        (run original futureRequests futureAuthority futurePermission offset)).raw
    rw [ProgrammeSource.actual_raw_next, earlier, selected_word, step_uses_its_actual_word]
    rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future
