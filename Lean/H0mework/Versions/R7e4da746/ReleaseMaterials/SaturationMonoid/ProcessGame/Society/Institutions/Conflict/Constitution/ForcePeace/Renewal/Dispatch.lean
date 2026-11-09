import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument
local notation "RawInput" => Compile.RawInput Party Good Port M Instrument

private theorem control_at_query (cut : C) (input : Input) :
    (query cut input).control = cut.control := by
  cases input with
  | none => rfl
  | some _ => exact (cut.requery_keeps_control_and_complete_account _).1

private theorem stop_is_selected_when_review_allows_recourse (cut : C) (available : ReviewAvailable cut) :
    (query cut (some .stopReview)).executionRaw = .stopReview := by
  unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
  rw [control_at_query cut (some .stopReview), submitted_is_original cut .stopReview]
  unfold Evolving.Epoch.select
  split
  · rfl
  · rename_i cursor active
    have recourse : cursor.recourse = true := by simpa only [ReviewAvailable, active] using available
    rw [if_pos recourse]
    rfl

theorem a_recourse_stop_has_no_material_items (cut : C) (available : ReviewAvailable cut) :
    inventory cut [some .stopReview] = [] := by
  let asked := query cut (some .stopReview)
  change Optimality.Programme.Epoch.materialItems asked ++ [] = []
  rw [List.append_nil]
  unfold Optimality.Programme.Epoch.materialItems
  split
  · rfl
  · unfold Evolving.Epoch.Current.physicalResult
    rw [show asked.executionRaw = .stopReview from stop_is_selected_when_review_allows_recourse cut available]
    rfl

private theorem same_execution_while_review_controls (cut : C) (closed : ¬ ReviewAvailable cut)
    (first second : Input) : (query cut first).executionRaw = (query cut second).executionRaw := by
  let input := Macro.Public.Scope.checkInput cut.native.input
  let origin := Capitalism.Universal.Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count
  let choose (raw : RawInput) := (Evolving.Epoch.select input origin cut.raw cut.members
    cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit cut.control raw).executionRaw
  have sameSelection (left right : RawInput) : choose left = choose right := by
    cases reviewing : cut.control.review with
    | none => exact (closed (by simp [ReviewAvailable, reviewing])).elim
    | some cursor =>
      have noRecourse : ¬ cursor.recourse = true := by simpa only [ReviewAvailable, reviewing] using closed
      have fromReview (raw : RawInput) : choose raw =
          (Evolving.Epoch.Review.compile input origin cut.raw cut.members cursor).executionRaw := by
        unfold choose Evolving.Epoch.select
        split
        · rename_i absent
          rw [absent] at reviewing
          cases reviewing
        · rename_i actual observed
          have same := Option.some.inj (reviewing.symm.trans observed)
          subst actual
          rw [if_neg noRecourse]
          rfl
      exact (fromReview left).trans (fromReview right).symm
  unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
  rw [control_at_query cut first, control_at_query cut second]
  cases first <;> cases second <;> exact sameSelection _ _

/-- With a closed recourse port, the active review decides every material
item. Replacing the submitted input by a stop cannot erase that work. -/
theorem a_nonrecourse_review_selects_the_same_inventory (cut : C) (closed : ¬ ReviewAvailable cut)
    (first second : Input) : inventory cut [first] = inventory cut [second] := by
  change Optimality.Programme.Epoch.materialItems (query cut first) ++ [] =
    Optimality.Programme.Epoch.materialItems (query cut second) ++ []
  simp only [List.append_nil, Optimality.Programme.Epoch.materialItems]
  have same := same_execution_while_review_controls cut closed first second
  unfold Evolving.Epoch.Current.physicalResult
  rw [same]
  cases first <;> cases second <;> rfl

inductive DispatchChoice (cut : C) (input : Input)
  | forward (checked : AdmittedHistory cut [input])
  | stop (issue : Violation cut input) (available : ReviewAvailable cut)
  | blocked (issue : Violation cut input) (closed : ¬ ReviewAvailable cut)
      (noAdmissibleInput : ∀ alternative : Input, ¬ AdmittedHistory cut [alternative])

def dispatchAdmission (cut : C) (input : Input) : DispatchChoice cut input :=
  match inspectAdmission cut input with
  | .approved all => .forward all
  | .refused issue =>
    if available : ReviewAvailable cut then .stop issue available
    else .blocked issue available (fun alternative all => issue.refutes (by
      intro item listed
      rw [a_nonrecourse_review_selects_the_same_inventory cut available input alternative] at listed
      exact all item listed))

namespace DispatchChoice

variable {cut : Root.Cut Party Good Port (State Party Technology) Instrument}
  {input : Reparation.Actual.Input Party Good Port (State Party Technology) Instrument}

/-- Inputs emitted by a pre-admission decision. A blocked original review
emits nothing here. Its already-submitted work is accounted separately. -/
def selected : DispatchChoice cut input → Script
  | .forward _ => [input]
  | .stop _ _ => [some .stopReview]
  | .blocked _ _ _ => []

theorem selected_is_admissible (decision : DispatchChoice cut input) : AdmittedHistory cut decision.selected := by
  cases decision with
  | forward checked => exact checked
  | stop _ available =>
    intro item listed
    rw [selected, a_recourse_stop_has_no_material_items cut available] at listed
    exact (List.not_mem_nil listed).elim
  | blocked _ _ _ => simp [AdmittedHistory, selected, inventory]

end DispatchChoice

theorem every_admissible_input_is_forwarded (cut : C) (input : Input) (checked : AdmittedHistory cut [input]) :
    (dispatchAdmission cut input).selected = [input] := by
  unfold dispatchAdmission
  cases inspectAdmission cut input with
  | approved _ => rfl
  | refused issue => exact (issue.refutes checked).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
