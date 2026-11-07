import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)

local notation "Frame" => Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim

def VerdictAdmitted {state : Responsibility.Family.State claim}
    {law : RawLaw Party Good Port Technology Instrument} {members : List Party}
    {proposal : RawEvent Party Good Port Technology Instrument}
    (verdict : Selection.RenewalVerdict claim state law members proposal) : Prop :=
  match verdict with
  | .admitted _ => True
  | .settled .. | .gate .. | .needs .. | .residual .. => False

def Admitted (frame : Frame) (proposal : RawEvent Party Good Port Technology Instrument) : Prop :=
  VerdictAdmitted claim (Gate.readRenewal claim frame proposal)

instance (frame : Frame) (proposal : RawEvent Party Good Port Technology Instrument) :
    Decidable (Admitted claim frame proposal) := by
  unfold Admitted
  cases Gate.readRenewal claim frame proposal <;> unfold VerdictAdmitted <;> infer_instance

theorem admitted_iff_the_original_source_verdict
    (frame : Frame) (proposal : RawEvent Party Good Port Technology Instrument) :
    Admitted claim frame proposal ↔ VerdictAdmitted claim
      (Selection.renewalVerdict claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
        frame.actualLaw frame.members proposal) := by
  change VerdictAdmitted claim (renewalDecision claim frame proposal) ↔ _
  unfold renewalDecision
  rw [Input.old_state_is_literal,readLaw_eq,readMembers_eq,Input.readProposal_eq]
  rfl

theorem an_admitted_actual_next_strictly_retires_an_original_cell
    (frame : Frame) (proposal : RawEvent Party Good Port Technology Instrument)
    (admitted : Admitted claim frame proposal) :
    Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Installation.successor claim frame proposal)) <
        Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) := by
  unfold Admitted VerdictAdmitted at admitted
  cases decision : Gate.readRenewal claim frame proposal with
  | admitted permit =>
      rw [Installation.successor_is_the_policy_update]
      exact permit.strictProgress
  | settled paid needs declared noStop => simp only [decision] at admitted
  | gate issue => simp only [decision] at admitted
  | needs issue => simp only [decision] at admitted
  | residual issue noProgress => simp only [decision] at admitted

/-- A finite list contains submitted inputs, never future answers. Every
transition is exactly the same root's actual-action successor. -/
def afterInputs (frame : Frame) : List (RawEvent Party Good Port Technology Instrument) → Frame
  | [] => frame
  | proposal :: rest => afterInputs (Installation.successor claim frame proposal) rest

def AllAdmitted (frame : Frame) : List (RawEvent Party Good Port Technology Instrument) → Prop
  | [] => True
  | proposal :: rest => Admitted claim frame proposal ∧
      AllAdmitted (Installation.successor claim frame proposal) rest

theorem the_original_current_bounds_every_actual_admitted_sequence
    (frame : Frame) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (admitted : AllAdmitted claim frame inputs) :
    inputs.length + Progress.budget claim
      (Abolition.Accounting.Root.Reentry.Frame.state claim (afterInputs claim frame inputs)) ≤
        Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) := by
  induction inputs generalizing frame with
  | nil => simp only [List.length_nil,afterInputs,Nat.zero_add,Nat.le_refl]
  | cons proposal rest ih =>
      have step := an_admitted_actual_next_strictly_retires_an_original_cell claim frame proposal admitted.1
      have tail := ih (Installation.successor claim frame proposal) admitted.2
      simp only [List.length_cons,afterInputs]
      omega

theorem a_longer_actual_input_sequence_must_settle_or_return_a_typed_blocker
    (frame : Frame) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (longer : Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) < inputs.length) :
    ¬ AllAdmitted claim frame inputs := by
  intro admitted
  have bounded := the_original_current_bounds_every_actual_admitted_sequence claim frame inputs admitted
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
