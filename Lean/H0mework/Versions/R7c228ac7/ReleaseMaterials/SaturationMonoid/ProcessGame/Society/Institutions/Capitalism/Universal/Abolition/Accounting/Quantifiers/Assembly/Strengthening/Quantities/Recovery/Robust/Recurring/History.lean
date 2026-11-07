import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Branch
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event : Type u} {Signal : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal

def repairAt (observe : Observation) (policy : Policy)
    (stage : Nat) (current : C) (exposure : Script) : Script :=
  policy stage (observe stage (endAt current exposure))

def run (expose : Exposure) (observe : Observation) (policy : Policy) (events : Nat → Event) :
    Nat → C → Script :=
  fun stage current =>
    let exposure := expose stage current (events stage)
    exposure ++ repairAt observe policy stage current exposure

abbrev currentAt (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (events : Nat → Event) (stage : Nat) : C :=
  stageAt source (run expose observe policy events) stage

abbrev exposureAt (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (events : Nat → Event) (stage : Nat) : Script :=
  expose stage (currentAt source expose observe policy events stage) (events stage)

theorem equal_past_events_generate_the_same_actual_current
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (first second : Nat → Event) (stage : Nat) (same : ∀ earlier < stage, first earlier = second earlier) :
    currentAt source expose observe policy first stage = currentAt source expose observe policy second stage := by
  induction stage with
  | zero => rfl
  | succ n previous =>
    have inherited := previous (fun earlier inside => same earlier (inside.trans (Nat.lt_succ_self n)))
    simp only [currentAt, next_stage_is_the_literal_original_next, stageBody, run] at inherited ⊢
    rw [inherited, same n (Nat.lt_succ_self n)]

theorem the_committed_policy_cannot_use_an_unobserved_exposure
    (observe : Observation) (policy : Policy) (stage : Nat) (first second : C) (left right : Script)
    (same : observe stage (endAt first left) = observe stage (endAt second right)) :
    repairAt observe policy stage first left = repairAt observe policy stage second right :=
  congrArg (policy stage) same

def PaidAt (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (events : Nat → Event) (stage : Nat) : Prop :=
  let current := currentAt source expose observe policy events stage
  let exposure := exposureAt source expose observe policy events stage
  BranchPaid current exposure (repairAt observe policy stage current exposure)

def ratioAt (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (events : Nat → Event) (stage : Nat) : EReal :=
  let current := currentAt source expose observe policy events stage
  let exposure := exposureAt source expose observe policy events stage
  hourRatio current exposure (repairAt observe policy stage current exposure)

structure PolicyPaid (source : C) (expose : Exposure) (observe : Observation) (policy : Policy) : Prop where
  restoration : ∀ events stage, PaidAt source expose observe policy events stage
  clock : ∀ events, Bounds.Cofinal.ClockCofinal source (run expose observe policy events)

theorem every_recurring_repair_uses_the_actual_prefix_and_generates_the_original_next
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (events : Nat → Event) (stage : Nat)
    (paid : PaidAt source expose observe policy events stage) :
    let current := currentAt source expose observe policy events stage
    let exposure := exposureAt source expose observe policy events stage
    let repair := repairAt observe policy stage current exposure
    Recorded source (stageScript source (run expose observe policy events) stage) ∧
      Recorded current (exposure ++ repair) ∧
      Settled (endAt current exposure) repair ∧
      currentAt source expose observe policy events (stage + 1) = endAt (endAt current exposure) repair := by
  dsimp only [PaidAt] at paid
  refine ⟨record source _, paid.original, paid.paid, ?_⟩
  change stageAt source (run expose observe policy events) (stage + 1) = _
  rw [next_stage_is_the_literal_original_next]
  exact endAt_append _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring
