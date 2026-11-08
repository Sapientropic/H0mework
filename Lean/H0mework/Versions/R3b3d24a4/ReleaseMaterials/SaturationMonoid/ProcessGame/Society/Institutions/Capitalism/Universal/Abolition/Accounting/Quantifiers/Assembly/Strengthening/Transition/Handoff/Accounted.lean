import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Routing
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Decision
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Slack
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Programmes

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

local notation "Plan" => Proposal Party Good Port Technology Instrument
local notation "Address" => Party × Good

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)

abbrev Assignment (proposal : Plan) :=
  Due.Service.Need ordered.toFinset task →
    Due.Service.Supply source (script source proposal) ordered.toFinset task → ℚ

variable (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
    Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)

def requiredOpening (proposal : Plan) (allocation : Assignment source ordered task proposal) (key : Address) : ℚ :=
  let word := script source proposal
  let view := Allocation.view source word ordered task (reserved word) allocation
  Reserve.openingNeed (Allocation.heldRows ordered task held) view.address key
    (Reserve.originalSteps source word (Reserve.assignedAt view.paid)) view.required

def Fits (proposal : Plan) (allocation : Assignment source ordered task proposal) : Prop :=
  Allocation.Fits source (script source proposal) ordered task (reserved (script source proposal)) held budget allocation

structure PaidAt (proposal : Plan) : Type where
  transition : Checked source proposal
  originalDemands : Due.Service.OriginalDemands ordered.toFinset task
  settlement : Settled source (script source proposal)
  allocation : Assignment source ordered task proposal
  fits : Fits source ordered task reserved held budget proposal allocation

inductive Issue (proposal : Plan) where
  | route (issue : Failure source proposal)
  | malformed (issue : ¬ Due.Service.OriginalDemands ordered.toFinset task)
  | native (issue : Obstruction source (script source proposal))
  | allocation (conflict : Allocation.Diagnostics.Conflict
      (Allocation.Diagnostics.taggedConstraints source (script source proposal) ordered task
        (reserved (script source proposal)) held budget))

def inspect (proposal : Plan) : PaidAt source ordered task reserved held budget proposal ⊕
    Issue source ordered task reserved held budget proposal :=
  match inspectPath source proposal with
  | .inr failure => .inr (.route failure)
  | .inl path =>
    if original : Due.Service.OriginalDemands ordered.toFinset task then
      let word := script source proposal
      match Quantities.decideAt source word with
      | .blocked issue => .inr (.native issue)
      | .feasible paid =>
        match Allocation.decideAllocation source word ordered task (reserved word) held budget with
        | .paid allocation fits => .inl ⟨path.down, original, settle source word paid, allocation, fits⟩
        | .blocked impossible =>
          .inr (.allocation (Allocation.Diagnostics.jointConflictOfInfeasible source word ordered task
            (reserved word) held budget impossible))
    else .inr (.malformed original)

theorem inspection_is_complete (proposal : Plan) :
    (∃ paid, inspect source ordered task reserved held budget proposal = .inl paid) ↔
      Checked source proposal ∧ Due.Service.OriginalDemands ordered.toFinset task ∧
        Settled source (script source proposal) ∧
        ∃ allocation, Fits source ordered task reserved held budget proposal allocation := by
  constructor
  · rintro ⟨paid, _⟩
    exact ⟨paid.transition, paid.originalDemands, paid.settlement, paid.allocation, paid.fits⟩
  · rintro ⟨route, original, settled, allocation, fits⟩
    cases outcome : inspect source ordered task reserved held budget proposal with
    | inl paid => exact ⟨paid, rfl⟩
    | inr failure =>
      cases failure with
      | route issue => exact (issue.refutes route).elim
      | malformed issue => exact (issue original).elim
      | native issue => exact (issue.refutes settled.toFeasible).elim
      | allocation conflict =>
        exact (Allocation.Diagnostics.jointConflict_refutes source (script source proposal) ordered task
          (reserved (script source proposal)) held budget conflict ⟨allocation, fits⟩).elim

theorem paid_handoff_is_the_original_whole_ledger_and_next {proposal : Plan}
    (paid : PaidAt source ordered task reserved held budget proposal) :
    Settled source (script source proposal) ∧
      (completed source proposal).raw.clock = handoffTime source proposal ∧
      Evolving.Epoch.Current.ClosedAt (completed source proposal) :=
  ⟨paid.settlement, the_handoff_time_is_the_completed_root_clock source proposal,
    paid.settlement.toRecorded.next⟩

theorem paid_handoff_uses_each_original_debit_once {proposal : Plan}
    (paid : PaidAt source ordered task reserved held budget proposal)
    (ordinal : Due.Service.Ordinal source (script source proposal)) (key : Address) :
    let word := script source proposal
    let view := Allocation.view source word ordered task (reserved word) paid.allocation
    let step := Reserve.readStep source.native.handlerFace.rootRead (Reserve.assignedAt view.paid)
      (Execution.timedAt source word ordinal) ordinal.val
    Reserve.held (Allocation.heldRows ordered task held) view.address step.paid key ≤ step.debit key := by
  intro word view step
  have conservative : view.Conservative :=
    Due.Settlement.allocation_is_conservative_at_every_original_timed_debit paid.fits.1.1
  exact Reserve.the_original_material_step_cannot_pay_two_rosters_with_one_debit
    source word view.address view.deadline view.required view.paid conservative
    (Allocation.heldRows ordered task held) (List.nodup_dedup _) ordinal key step
    (Reserve.originalSteps_at _ _ _ _)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
