import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Allocation
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Accounted
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (past : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "Held" => Finset Row
local notation "Budget" => Party × Good → ℚ

structure PaidPrefix (reserved : Finset (Due.Service.Ordinal source past)) (held : Held) (budget : Budget) where
  originalDemands : Due.Service.OriginalDemands ordered.toFinset task
  settlement : Settled source past
  allocation : Row → Due.Service.Supply source past ordered.toFinset task → ℚ
  fits : Allocation.Fits source past ordered task reserved held budget allocation

def fromHandoff
    (reserved : ∀ word : Script, Finset (Due.Service.Ordinal source word)) (held : Held) (budget : Budget)
    {proposal : Proposal Party Good Port Technology Instrument}
    (paid : PaidAt source ordered task reserved held budget proposal) :
    PaidPrefix source (script source proposal) ordered task (reserved (script source proposal)) held budget :=
  ⟨paid.originalDemands, paid.settlement, paid.allocation, paid.fits⟩

variable {source past ordered task}
  {reserved : Finset (Due.Service.Ordinal source past)}
  {held : Finset (Due.Service.Need ordered.toFinset task)} {budget : Party × Good → ℚ}
  (old : PaidPrefix source past ordered task reserved held budget)
  (future : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (newReserved : Finset (Due.Service.Ordinal (Execution.endAt source past) future))

local notation "AtCut" => Execution.endAt source past
local notation "Booked" => reservations source past future reserved newReserved

structure Extension where
  fresh : Settled AtCut future
  combined : PaidPrefix source (past ++ future) ordered task Booked held budget
  kept : Keeps source past future ordered task old.allocation combined.allocation

inductive Refusal
  | native (issue : Obstruction AtCut future)
  | allocation (issue : Allocation.Diagnostics.Conflict
      (taggedSystem source past future ordered task old.allocation reserved newReserved held budget))

/-- Check each new cut's own living and maintenance bill, then extend the
one original allocation with its old paid coordinates held fixed. -/
def extend : Extension old future newReserved ⊕ Refusal old future newReserved :=
  match decideAt AtCut future with
  | .blocked reason => .inr (.native reason)
  | .feasible currentPaid =>
    let fresh := settle AtCut future currentPaid
    match allocate source past future ordered task old.allocation reserved newReserved held budget with
    | .blocked reason => .inr (.allocation reason)
    | .paid combined kept fits =>
      .inl ⟨fresh, ⟨old.originalDemands, Due.Production.append_settled source past future old.settlement fresh,
        combined, fits⟩, kept⟩

theorem extension_is_complete :
    (∃ paid, extend old future newReserved = .inl paid) ↔ Settled AtCut future ∧
      ∃ allocation, Keeps source past future ordered task old.allocation allocation ∧
        Allocation.Fits source (past ++ future) ordered task Booked held budget allocation := by
  constructor
  · rintro ⟨paid, _⟩
    exact ⟨paid.fresh, paid.combined.allocation, paid.kept, paid.combined.fits⟩
  · rintro ⟨fresh, allocation, kept, fits⟩
    cases read : extend old future newReserved with
    | inl paid => exact ⟨paid, rfl⟩
    | inr refused =>
      cases refused with
      | native issue => exact (issue.refutes fresh.toFeasible).elim
      | allocation issue =>
        exact (conflict_refutes_every_extension source past future ordered task old.allocation
          reserved newReserved held budget issue ⟨allocation, kept, fits⟩).elim

theorem Extension.the_paid_next_is_the_original_cut_and_whole_ledger
    (paid : Extension old future newReserved) :
    Execution.endAt source (past ++ future) = Execution.endAt AtCut future ∧
      Recorded source (past ++ future) ∧ Evolving.Epoch.Current.ClosedAt (Execution.endAt AtCut future) :=
  ⟨Execution.endAt_append source past future, paid.combined.settlement.toRecorded, paid.fresh.toRecorded.next⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation
