import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Joint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev StockFailure (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) :=
  (stockProfile agenda source script).FirstShortageAt
    ((stockProfile agenda source script).protectedGap (Liquidity.beforeStock source script))
    (watchedAddresses agenda source script) additional

inductive JointCause (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ)
  | service (failed : FirstFailure agenda source script)
  | stock (failed : StockFailure agenda source script additional)
  | both (service : FirstFailure agenda source script) (stock : StockFailure agenda source script additional)
      (tied : service.time = stock.time)

def JointCause.time {agenda : Agenda Party Good TaskId} {source : C} {script : Script}
    {additional : Party × Good → ℚ} : JointCause agenda source script additional → ℚ
  | .service failed => failed.time
  | .stock failed => failed.time
  | .both firstService _ _ => firstService.time

structure JointFailure (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) where
  cause : JointCause agenda source script additional
  exactClock : (cause.time : WithTop ℚ) = jointRenewalBoundary agenda source script additional

/-- At the first joint failure, preserve both independent causes if their
original clocks coincide. -/
def nameJointFailure (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) (horizon : ℚ)
    (reached : jointRenewalBoundary agenda source script additional ≤ (horizon : WithTop ℚ)) :
    JointFailure agenda source script additional := by
  cases serviceResult : inspectFrontier agenda source script with
  | clear _ =>
    cases stockResult : stockDecision agenda source script additional with
    | noFailure _ =>
      rw [jointRenewalBoundary, serviceResult, stockResult] at reached
      change (⊤ : WithTop ℚ) ≤ (horizon : WithTop ℚ) at reached
      exact (WithTop.coe_ne_top (top_le_iff.mp reached)).elim
    | blocked stock =>
      refine ⟨.stock stock, ?_⟩
      rw [jointRenewalBoundary, serviceResult, stockResult]
      exact (min_eq_right (show (stock.time : WithTop ℚ) ≤ ⊤ from le_top)).symm
  | blocked service =>
    cases stockResult : stockDecision agenda source script additional with
    | noFailure _ =>
      refine ⟨.service service, ?_⟩
      rw [jointRenewalBoundary, serviceResult, stockResult]
      exact (min_eq_left (show (service.time : WithTop ℚ) ≤ ⊤ from le_top)).symm
    | blocked stock =>
      by_cases serviceFirst : service.time < stock.time
      · refine ⟨.service service, ?_⟩
        rw [jointRenewalBoundary, serviceResult, stockResult]
        exact (min_eq_left (WithTop.coe_le_coe.mpr serviceFirst.le)).symm
      · by_cases stockFirst : stock.time < service.time
        · refine ⟨.stock stock, ?_⟩
          rw [jointRenewalBoundary, serviceResult, stockResult]
          exact (min_eq_right (WithTop.coe_le_coe.mpr stockFirst.le)).symm
        · have tied : service.time = stock.time :=
            le_antisymm (le_of_not_gt stockFirst) (le_of_not_gt serviceFirst)
          refine ⟨.both service stock tied, ?_⟩
          rw [jointRenewalBoundary, serviceResult, stockResult]
          exact (min_eq_left (WithTop.coe_le_coe.mpr tied.le)).symm

theorem a_joint_shortage_keeps_the_actual_prefix_and_original_successor
    {agenda : Agenda Party Good TaskId} {source : C} {script : Script} {additional : Party × Good → ℚ}
    (failure : JointFailure agenda source script additional) :
    Recorded source (Liquidity.committedPrefix failure.cause.time source script) ∧ Recorded source script :=
  ⟨record _ _, record _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
