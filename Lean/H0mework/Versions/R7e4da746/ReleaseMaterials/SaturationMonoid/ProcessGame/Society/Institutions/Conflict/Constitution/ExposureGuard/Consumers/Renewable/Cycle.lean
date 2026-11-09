import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Material
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable normalise)
open Installed (Raw Req)
open Quantities Evolving.Epoch

noncomputable section

def readyCut (cut : C) : C := Execution.endAt cut (Execution.drain cut)

/-- Finish the current native mass before the next material renewal. The
new period closes the very window in which its old accounting took place. -/
def wordAt (cut : C) : Word := Execution.drain cut ++ [service]

structure StageAt (cut : C) (periods : Nat) : Prop where
  input : cut.native.input = input
  raw : cut.raw = materialAt periods
  review : cut.control.review = none

theorem initial_stage : StageAt start 0 := ⟨start_input, start_raw, start_review⟩

theorem ready_stage (cut : C) (periods : Nat) (original : StageAt cut periods) : StageAt (readyCut cut) periods := by
  refine ⟨(Execution.endAt_input cut _).trans original.input, ?_, ?_⟩
  · exact (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut).2.1.trans original.raw
  · rw [readyCut, Transition.Handoff.drain_preserves_control]
    exact original.review

theorem checked_period (cut : C) (periods : Nat) (original : StageAt cut periods) :
    Execution.PeriodChecks cut period := by
  change Public.Scope.Checks cut.native.input cut.native.depth cut.native.count
    cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast cut.native.actual.snapshot (normalise period)
  rw [normalised_period]
  let n := cut.native
  let members := Public.Scope.scope n.input n.depth n.count n.prefixLimit n.renewalLimit n.oldPast n.actual.snapshot period
  change Review.Guarded.Checks (Public.Scope.checkInput cut.native.input)
    (Capitalism.Universal.Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count)
    cut.raw members period
  rw [show Public.Scope.checkInput cut.native.input = checkInput from
    congrArg Public.Scope.checkInput original.input, original.raw]
  exact original_material_guard _ members periods

theorem body_paid (cut : C) (periods : Nat) (original : StageAt cut periods) :
    (Execution.next (readyCut cut) service).raw = materialAt (periods + 1) ∧
      Boundary.Actual.items (readyCut cut) service = material.rawItems (materialAt periods) period := by
  let source := readyCut cut
  have stage := ready_stage cut periods original
  have ready : Ready source := (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut).1
  have review : ReviewAvailable source := by
    unfold ReviewAvailable
    rw [stage.review]
    trivial
  have guard := checked_period source periods stage
  have used := Execution.a_checked_period_has_the_original_real_effect source period ready review guard
  have items := Execution.a_checked_period_has_the_original_paid_inventory source period ready review guard
  have sameLaw : Physical.Public.interpreter source.native.input = material :=
    congrArg Physical.Public.interpreter stage.input
  rw [sameLaw, stage.raw, normalised_period] at used items
  exact ⟨used.trans (material_successor periods), items⟩

theorem renewal_input_keeps_review (cut : C) (periods : Nat) (original : StageAt cut periods) :
    (Execution.next (readyCut cut) service).control.review = none := by
  let source := readyCut cut
  let query := Execution.query source service
  have ready : Ready query := (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut).1
  have phase : query.control.review = none :=
    (congrArg (fun value => value.review) (source.requery_keeps_control_and_complete_account
      (fun _ _ => .execute period)).1).trans (ready_stage cut periods original).review
  change ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual at ready
  change query.advance.control.review = none
  rw [Current.advance_eq_epoch _ ready, Evolving.Epoch.Transition.next_reads_the_written_control]
  unfold Current.afterControl Current.choice
  rw [show query.proposal = .execute period from Execution.submitted_is_original source (.execute period)]
  unfold Evolving.Epoch.select
  split
  · simp only [Evolving.Epoch.Selection.controlAfter, Dispatch.compile, Dispatch.Selection.controlAfter]
    split <;> exact phase
  · rename_i cursor observed
    rw [phase] at observed
    cases observed

theorem actual_word_succeeds (cut : C) (periods : Nat) (original : StageAt cut periods) :
    StageAt (Execution.endAt cut (wordAt cut)) (periods + 1) := by
  refine ⟨(Execution.endAt_input cut _).trans original.input, ?_, ?_⟩
  · unfold wordAt
    rw [Execution.endAt_append]
    exact (body_paid cut periods original).1
  · unfold wordAt
    rw [Execution.endAt_append]
    exact renewal_input_keeps_review cut periods original

def run : Nat → C
  | 0 => start
  | n + 1 => Execution.endAt (run n) (wordAt (run n))

def history : Nat → Word
  | 0 => []
  | n + 1 => history n ++ wordAt (run n)

theorem run_is_its_own_native_fold (n : Nat) : Execution.endAt start (history n) = run n := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [history, Execution.endAt_append, prior]
    rfl

theorem stage (n : Nat) : StageAt (run n) n := by
  induction n with
  | zero => exact initial_stage
  | succ n prior => exact actual_word_succeeds _ _ prior

theorem actual_clock (n : Nat) : (run n).raw.clock = 4 + (n : ℚ) := by
  rw [(stage n).raw, material_clock]

theorem standing (script : Word) (person : Bool) : person ∈ (Execution.endAt start script).members := by
  let reached := Execution.endAt start script
  obtain ⟨same, depth, count⟩ := Execution.the_actual_script_keeps_the_original_reader_indices start script
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  change person ∈ Capitalism.Universal.Abolition.Root.Actual.members reached.native.input reached.native.depth reached.native.count
  rw [same, depth, count]
  exact every_person_originally_stands person

theorem standing_after (n : Nat) (suffix : Word) (person : Bool) :
    person ∈ (Execution.endAt (run n) suffix).members := by
  rw [← run_is_its_own_native_fold n, ← Execution.endAt_append]
  exact standing _ person

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
