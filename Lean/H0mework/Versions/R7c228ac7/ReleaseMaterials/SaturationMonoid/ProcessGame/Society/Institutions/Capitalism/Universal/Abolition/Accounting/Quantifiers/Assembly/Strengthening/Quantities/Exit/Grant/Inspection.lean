import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Eligibility

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime
open Redemption (sourceLaw sourceOrigin)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

private instance (law : RawLaw Party Good Port Technology Instrument)
    (origin current : RawCurrent Party Good Technology Instrument)
    (position : Position Party Instrument) (quantity : ℚ) :
    Decidable (Qualified law origin current position quantity) := by
  unfold Qualified Redemption.Safe
  infer_instance

inductive Decision (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan)
  | paid (actual : Eligible source position excluded task plan)
  | blocked (issue : Issue source position excluded task plan)

def decidePlan (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) : Decision source position excluded task plan :=
  if standing : Entitled source position excluded task then
    if positive : 0 < plan.quantity then
      let front := funded source plan
      match pending : inspectNative front with
      | some issue => .blocked (.native issue)
      | none =>
        if review : ReviewAvailable front then
          if grant : Qualified (sourceLaw front) (sourceOrigin front) front.raw position plan.quantity then
            match Material.inspectList (Independent source excluded) (Execution.inventory source plan.preparation) with
            | .failure item original failed => .blocked (.preparation item original failed)
            | .clear preparation =>
              let paid := redeemed source position plan
              match Material.inspectList (Independent source excluded) (Execution.inventory paid plan.continuation) with
              | .failure item original failed => .blocked (.continuation item original failed)
              | .clear continuation =>
                match service : Clock.Window.inspect paid task plan.continuation with
                | some issue => .blocked (.service issue)
                | none => .paid ⟨standing, positive, native_is_finished_without_a_pending_item front pending,
                    review, grant, preparation, continuation,
                    (Clock.Window.passes_iff_every_original_service_commits_in_time _ _ _).mp service⟩
          else .blocked (.grant grant)
        else .blocked (.review review)
    else .blocked (.emptyPayment (le_of_not_gt positive))
  else .blocked (.standing standing)

def inspectPlan (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) : Option (Issue source position excluded task plan) :=
  match decidePlan source position excluded task plan with
  | .paid _ => none
  | .blocked issue => some issue

theorem inspect_passes_iff_funded_and_independently_served
    (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) :
    inspectPlan source position excluded task plan = none ↔ Eligible source position excluded task plan := by
  unfold inspectPlan
  cases decidePlan source position excluded task plan with
  | paid actual => exact ⟨fun _ => actual, fun _ => rfl⟩
  | blocked issue =>
    constructor
    · intro impossible
      contradiction
    · intro eligible
      exact (issue.refutes eligible).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
