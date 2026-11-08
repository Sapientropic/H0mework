import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger (ledgerClaims)

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

structure Reading (Party Good Instrument : Type) where
  time : ℚ
  opening : Party × Good → ℚ
  unpaid : Instrument → Party → Party → ℚ

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
    Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)
  (deadline : WithTop ℚ)

def readJoint (proposal : Plan) (allocation : Assignment source ordered task proposal) : Reading Party Good Instrument where
  time := handoffTime source proposal
  opening := requiredOpening source ordered task reserved held proposal allocation
  unpaid :=
    let after := completed source proposal
    ledgerClaims after.native.input after.native.depth after.native.count after.native.actual.actual.account.current

structure Programme where
  proposal : Plan
  allocation : Assignment source ordered task proposal

def valid (candidate : Programme source ordered task) : Prop :=
  Admitted source ordered task reserved held budget deadline candidate.proposal ∧
    Fits source ordered task reserved held budget candidate.proposal candidate.allocation

def assignedValues {Value : Type*} (read : Programme source ordered task → Value) : Set Value :=
  {value | ∃ candidate, valid source ordered task reserved held budget deadline candidate ∧ read candidate = value}

def domain : Set (Reading Party Good Instrument) :=
  assignedValues source ordered task reserved held budget deadline fun candidate =>
    readJoint source ordered task reserved held candidate.proposal candidate.allocation

theorem every_feasible_reading_has_its_one_whole_ledger (reading : Reading Party Good Instrument)
    (feasible : reading ∈ domain source ordered task reserved held budget deadline) :
    ∃ proposal allocation, readJoint source ordered task reserved held proposal allocation = reading ∧
      Recorded source (script source proposal) ∧
      (completed source proposal).raw.clock = reading.time ∧
      Evolving.Epoch.Current.ClosedAt (completed source proposal) := by
  obtain ⟨candidate, admitted, rfl⟩ := feasible
  have whole := Admitted.original_successor source ordered task reserved held budget deadline admitted.1
  exact ⟨candidate.proposal, candidate.allocation, rfl, whole.1,
    the_handoff_time_is_the_completed_root_clock _ _, whole.2⟩

def timeCost (source : C) (proposal : Plan) : EReal :=
  ((handoffTime source proposal : ℝ) : EReal)

theorem earliest_handoff :
    Minimum source ordered task reserved held budget deadline (timeCost source) :=
  resolve source ordered task reserved held budget deadline _

inductive AssignedMinimum {Value : Type*} [CompleteLinearOrder Value]
    (read : Programme source ordered task → Value) : Prop
  | attained (candidate : Programme source ordered task)
      (paid : valid source ordered task reserved held budget deadline candidate)
      (least : read candidate = sInf (assignedValues source ordered task reserved held budget deadline read))
  | approached (nonempty : (assignedValues source ordered task reserved held budget deadline read).Nonempty)
      (unattained : sInf (assignedValues source ordered task reserved held budget deadline read) ∉
        assignedValues source ordered task reserved held budget deadline read)
      (closer : ∀ limit, sInf (assignedValues source ordered task reserved held budget deadline read) < limit →
        ∃ candidate, valid source ordered task reserved held budget deadline candidate ∧ read candidate < limit)
  | blocked (why : ∀ candidate : Programme source ordered task,
      Recorded source (script source candidate.proposal) ∧
        (Nonempty (Refusal source ordered task reserved held budget deadline candidate.proposal) ∨
          ¬ Fits source ordered task reserved held budget candidate.proposal candidate.allocation))

theorem resolveAssigned {Value : Type*} [CompleteLinearOrder Value]
    (read : Programme source ordered task → Value) :
    AssignedMinimum source ordered task reserved held budget deadline read := by
  classical
  let values := assignedValues source ordered task reserved held budget deadline read
  by_cases attained : sInf values ∈ values
  · obtain ⟨candidate, paid, exactValue⟩ := attained
    exact .attained candidate paid exactValue
  by_cases feasible : values.Nonempty
  · refine .approached feasible attained fun limit closer => ?_
    obtain ⟨_, ⟨candidate, paid, rfl⟩, below⟩ := sInf_lt_iff.mp closer
    exact ⟨candidate, paid, below⟩
  · refine .blocked fun candidate => ⟨the_handoff_uses_one_original_ledger _ _, ?_⟩
    cases observed : refusal source ordered task reserved held budget deadline candidate.proposal with
    | some reason => exact .inl ⟨reason⟩
    | none =>
      have accepted := (has_no_refusal_iff source ordered task reserved held budget deadline _).mp observed
      exact .inr fun fits => feasible ⟨read candidate, candidate, ⟨accepted, fits⟩, rfl⟩

theorem tight_opening_by_the_deadline (key : Party × Good) :
    AssignedMinimum source ordered task reserved held budget deadline
      (fun candidate => ((requiredOpening source ordered task reserved held candidate.proposal
        candidate.allocation key : ℝ) : EReal)) :=
  resolveAssigned source ordered task reserved held budget deadline _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
