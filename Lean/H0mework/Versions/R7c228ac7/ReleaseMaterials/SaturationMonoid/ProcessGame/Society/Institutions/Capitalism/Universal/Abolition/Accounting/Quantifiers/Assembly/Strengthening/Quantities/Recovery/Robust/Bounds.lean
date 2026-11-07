import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Branch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Nature : Type u} {Observation : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Observation → Script

def response (origin : C) (observe : C → Observation) (policy : Policy) (exposure : Script) : Script :=
  policy (observe (Execution.endAt origin exposure))

theorem same_actual_observation_forces_the_same_repair
    (origin : C) (observe : C → Observation) (policy : Policy) (first second : Script)
    (same : observe (Execution.endAt origin first) = observe (Execution.endAt origin second)) :
    response origin observe policy first = response origin observe policy second :=
  congrArg policy same

def ValidPolicy (origin : C) (expose : Nature → Script) (observe : C → Observation) (policy : Policy) : Prop :=
  ∀ event, BranchPaid origin (expose event) (response origin observe policy (expose event))

def worst (origin : C) (expose : Nature → Script) (observe : C → Observation) (policy : Policy) : EReal :=
  ⨆ event, hourRatio origin (expose event) (response origin observe policy (expose event))

def costs (origin : C) (expose : Nature → Script) (observe : C → Observation) : Set EReal :=
  fun amount => ∃ policy, ValidPolicy origin expose observe policy ∧ worst origin expose observe policy = amount

theorem worst_le_iff_every_original_event
    (origin : C) (expose : Nature → Script) (observe : C → Observation) (policy : Policy) (allowance : EReal) :
    worst origin expose observe policy ≤ allowance ↔
      ∀ event, hourRatio origin (expose event) (response origin observe policy (expose event)) ≤ allowance := by
  unfold worst
  exact iSup_le_iff

/-- The same policy is chosen before any event. Its only runtime input is
the observation of the original current produced by that event. -/
inductive Resolution (origin : C) (expose : Nature → Script) (observe : C → Observation) : Prop
  | noEvent (absent : IsEmpty Nature)
  | attained (policy : Policy) (paid : ValidPolicy origin expose observe policy)
      (exactAmount : worst origin expose observe policy = sInf (costs origin expose observe))
      (finite : worst origin expose observe policy < ⊤)
  | approached (nonempty : (costs origin expose observe).Nonempty)
      (finite : sInf (costs origin expose observe) < ⊤)
      (strict : sInf (costs origin expose observe) ∉ costs origin expose observe)
      (near : ∀ limit, sInf (costs origin expose observe) < limit →
        ∃ policy, ValidPolicy origin expose observe policy ∧ worst origin expose observe policy < limit)
  | unbounded (nonempty : (costs origin expose observe).Nonempty)
      (noUniform : ∀ policy, ValidPolicy origin expose observe policy →
        ∀ limit < (⊤ : EReal), ∃ event,
          limit < hourRatio origin (expose event) (response origin observe policy (expose event)))
  | obstructed (failed : ∀ policy : Policy, ∃ event,
      Nonempty (BranchIssue origin (expose event) (response origin observe policy (expose event))) ∧
        Recorded origin (expose event ++ response origin observe policy (expose event)))

theorem the_original_root_resolves_precommitted_work_conversion
    (origin : C) (expose : Nature → Script) (observe : C → Observation) :
    Resolution origin expose observe := by
  classical
  by_cases occurs : Nonempty Nature
  · let feasible := costs origin expose observe
    by_cases payable : feasible.Nonempty
    · by_cases infinite : sInf feasible = ⊤
      · refine .unbounded payable ?_
        intro policy valid limit finite
        have value : worst origin expose observe policy ∈ feasible := ⟨policy, valid, rfl⟩
        have enormous := sInf_le value
        rw [infinite] at enormous
        exact lt_iSup_iff.mp (finite.trans_le enormous)
      · by_cases reached : sInf feasible ∈ feasible
        · obtain ⟨policy, paid, actual⟩ := reached
          exact .attained policy paid actual (actual.symm ▸ lt_top_iff_ne_top.mpr infinite)
        · refine .approached payable (lt_top_iff_ne_top.mpr infinite) reached ?_
          intro limit less
          obtain ⟨amount, ⟨policy, paid, rfl⟩, below⟩ := sInf_lt_iff.mp less
          exact ⟨policy, paid, below⟩
    · refine .obstructed (fun policy => ?_)
      have invalid : ¬ ValidPolicy origin expose observe policy :=
        fun paid => payable ⟨_, policy, paid, rfl⟩
      obtain ⟨event, fail⟩ := not_forall.mp invalid
      exact ⟨event, failed_branch_has_original_issue _ _ _ fail, record origin _⟩
  · exact .noEvent ⟨fun event => occurs ⟨event⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust
