import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

abbrev StockShortage (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (additional : Party × Good → ℚ) :=
  let view := stockView source script ordered.toFinset task
  view.FirstShortageAt (view.protectedGap (Liquidity.beforeStock source script))
    (watched source script ordered task) additional

abbrev ServiceShortage (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) :=
  Deadline.FirstShortage (Service.network source script ordered.toFinset task reserved) deadline

abbrev Problem (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (additional : Party × Good → ℚ) :=
  ServiceShortage source script ordered task reserved ⊕ StockShortage source script ordered task additional

def problemTime {source : C} {script : Script} {ordered : List TaskId} {task : TaskId → Task}
    {reserved : Finset (Service.Ordinal source script)} {additional : Party × Good → ℚ} :
    Problem source script ordered task reserved additional → ℚ
  | .inl service => service.time
  | .inr stock => stock.time

/-- Return the actual first cause on the original execution. If both
constraints fail at the same cut, the service certificate is returned. -/
def firstProblem (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (additional : Party × Good → ℚ) :
    Option (Problem source script ordered task reserved additional) :=
  match serviceFrontier source script ordered task reserved, stockFrontier source script ordered task additional with
  | .clear _, .noFailure _ => none
  | .short service, .noFailure _ => some (.inl service)
  | .clear _, .blocked stock => some (.inr stock)
  | .short service, .blocked stock =>
    if service.time ≤ stock.time then some (.inl service) else some (.inr stock)

theorem first_problem_is_the_exact_original_renewal_boundary
    (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (additional : Party × Good → ℚ) :
    ((firstProblem source script ordered task reserved additional).map problemTime : WithTop ℚ) =
      renewalBoundary source script ordered task reserved additional := by
  unfold firstProblem renewalBoundary
  cases serviceFrontier source script ordered task reserved with
  | clear _ =>
    cases stockFrontier source script ordered task additional <;>
      simp [serviceTime, stockTime, problemTime] <;> rfl
  | short service =>
    cases stockFrontier source script ordered task additional with
    | noFailure _ => simp [serviceTime, stockTime, problemTime]; rfl
    | blocked stock =>
      by_cases earlier : service.time ≤ stock.time
      · simp [earlier, serviceTime, stockTime, problemTime]; rfl
      · simp [earlier, serviceTime, stockTime, problemTime,
          min_eq_right (WithTop.coe_le_coe.mpr (le_of_not_ge earlier))]; rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
