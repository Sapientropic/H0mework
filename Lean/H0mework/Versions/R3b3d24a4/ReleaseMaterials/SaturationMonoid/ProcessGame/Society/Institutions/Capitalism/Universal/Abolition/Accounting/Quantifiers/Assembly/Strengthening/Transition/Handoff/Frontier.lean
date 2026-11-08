import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Accounted

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
    Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ) (deadline : WithTop ℚ)

inductive Refusal (proposal : Plan)
  | unpaid (issue : Issue source ordered task reserved held budget proposal)
  | late (passed : deadline < (handoffTime source proposal : WithTop ℚ))

def refusal (proposal : Plan) : Option (Refusal source ordered task reserved held budget deadline proposal) :=
  match inspect source ordered task reserved held budget proposal with
  | .inr blocked => some (.unpaid blocked)
  | .inl _ =>
    if passed : deadline < (handoffTime source proposal : WithTop ℚ) then some (.late passed) else none

def Admitted (proposal : Plan) : Prop :=
  (∃ paid, inspect source ordered task reserved held budget proposal = .inl paid) ∧
    (handoffTime source proposal : WithTop ℚ) ≤ deadline

theorem has_no_refusal_iff (proposal : Plan) :
    refusal source ordered task reserved held budget deadline proposal = none ↔
      Admitted source ordered task reserved held budget deadline proposal := by
  unfold refusal Admitted
  cases observed : inspect source ordered task reserved held budget proposal with
  | inr issue => simp
  | inl paid => simp [not_lt]

/-- Every coordinate is read from one complete proposal. An opening
balance budget and a deadline may be imposed independently. -/
def JointValues {Value : Type*} (read : Plan → Value) : Set Value :=
  {value | ∃ proposal, Admitted source ordered task reserved held budget deadline proposal ∧ read proposal = value}

theorem joint_values_are_exactly_the_paid_original_programmes {Value : Type*} (read : Plan → Value) :
    JointValues source ordered task reserved held budget deadline read =
      Bounds.Compiled.values source (script source)
        (refusal source ordered task reserved held budget deadline) read := by
  ext value
  constructor
  · rintro ⟨proposal, accepted, rfl⟩
    obtain ⟨paid, selected⟩ := accepted.1
    exact ⟨proposal, paid.settlement,
      (has_no_refusal_iff source ordered task reserved held budget deadline proposal).mpr accepted, rfl⟩
  · rintro ⟨proposal, _, cleared, rfl⟩
    exact ⟨proposal, (has_no_refusal_iff source ordered task reserved held budget deadline proposal).mp cleared, rfl⟩

inductive Minimum {Value : Type*} [CompleteLinearOrder Value] (read : Plan → Value) : Prop
  | attained (proposal : Plan) (paid : Admitted source ordered task reserved held budget deadline proposal)
      (least : read proposal = sInf (JointValues source ordered task reserved held budget deadline read))
  | approached (nonempty : (JointValues source ordered task reserved held budget deadline read).Nonempty)
      (unattained : sInf (JointValues source ordered task reserved held budget deadline read) ∉
        JointValues source ordered task reserved held budget deadline read)
      (closer : ∀ limit, sInf (JointValues source ordered task reserved held budget deadline read) < limit →
        ∃ proposal, Admitted source ordered task reserved held budget deadline proposal ∧ read proposal < limit)
  | blocked (reason : ∀ proposal, Recorded source (script source proposal) ∧
      Nonempty (Refusal source ordered task reserved held budget deadline proposal))

/-- Quantifies over arbitrary original preparations and migration code,
including quantities and lengths outside any finite registered menu. -/
theorem resolve {Value : Type*} [CompleteLinearOrder Value] (read : Plan → Value) :
    Minimum source ordered task reserved held budget deadline read := by
  have exactDomain := joint_values_are_exactly_the_paid_original_programmes
    source ordered task reserved held budget deadline read
  have equivalent := has_no_refusal_iff source ordered task reserved held budget deadline
  cases Bounds.Compiled.resolve source (script source) (refusal source ordered task reserved held budget deadline) read with
  | attained proposal _ checked least =>
    exact .attained proposal ((equivalent proposal).mp checked) (exactDomain.symm ▸ least)
  | approached nonempty unattained closer =>
    refine .approached (exactDomain.symm ▸ nonempty) (exactDomain.symm ▸ unattained) ?_
    intro limit bound
    obtain ⟨proposal, _, checked, below⟩ := closer limit (exactDomain ▸ bound)
    exact ⟨proposal, (equivalent proposal).mp checked, below⟩
  | obstructed fail =>
    refine .blocked fun proposal => ⟨(fail proposal).1, ?_⟩
    cases observed : refusal source ordered task reserved held budget deadline proposal with
    | some issue => exact ⟨issue⟩
    | none =>
      obtain ⟨paid, _⟩ := ((equivalent proposal).mp observed).1
      rcases (fail proposal).2 with native | ⟨issue, blocked⟩
      · obtain ⟨issue⟩ := native
        exact (issue.refutes paid.settlement.toFeasible).elim
      · rw [observed] at blocked
        cases blocked

theorem Admitted.original_successor {proposal : Plan}
    (accepted : Admitted source ordered task reserved held budget deadline proposal) :
    Recorded source (script source proposal) ∧ Evolving.Epoch.Current.ClosedAt (completed source proposal) := by
  obtain ⟨paid, _⟩ := accepted.1
  exact ⟨paid.settlement.toRecorded, paid.settlement.toRecorded.next⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
