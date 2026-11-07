import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Plan

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

def Entitled (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) : Prop :=
  position.creditor ∈ source.members ∧ position.creditor ∉ excluded ∧
  position.debtor ∈ source.members ∧ position.debtor ∉ excluded ∧
  ∃ slot ∈ task.slots, slot.bearer = position.creditor ∧ ∃ lot ∈ slot.goods, 0 < lot.2

instance (source : C) (position : Position Party Instrument) (excluded : List Party) (task : PublicTaskSpec Party Good) :
    Decidable (Entitled source position excluded task) := by
  unfold Entitled
  infer_instance

structure Eligible (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) : Prop where
  standing : Entitled source position excluded task
  positive : 0 < plan.quantity
  native : Ready (funded source plan)
  review : ReviewAvailable (funded source plan)
  grant : Qualified (sourceLaw (funded source plan)) (sourceOrigin (funded source plan))
    (funded source plan).raw position plan.quantity
  preparation : ∀ item ∈ Execution.inventory source plan.preparation, Independent source excluded item
  continuation : ∀ item ∈ Execution.inventory (redeemed source position plan) plan.continuation,
    Independent source excluded item
  served : Clock.Window.FullyServed (redeemed source position plan) task plan.continuation

inductive Issue (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan)
  | standing (failed : ¬ Entitled source position excluded task)
  | emptyPayment (nonpositive : plan.quantity ≤ 0)
  | native (pending : NativeObstruction (funded source plan))
  | review (failed : ¬ ReviewAvailable (funded source plan))
  | grant (failed : ¬ Qualified (sourceLaw (funded source plan)) (sourceOrigin (funded source plan))
      (funded source plan).raw position plan.quantity)
  | preparation (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ Execution.inventory source plan.preparation) (failed : ¬ Independent source excluded item)
  | continuation (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ Execution.inventory (redeemed source position plan) plan.continuation)
      (failed : ¬ Independent source excluded item)
  | service (issue : Clock.Window.Shortage (redeemed source position plan) task plan.continuation)

theorem Issue.refutes {source : C} {position : Position Party Instrument} {excluded : List Party}
    {task : PublicTaskSpec Party Good} {plan : Plan} (issue : Issue source position excluded task plan) :
    ¬ Eligible source position excluded task plan := by
  intro paid
  cases issue with
  | standing failed => exact failed paid.standing
  | emptyPayment nonpositive => exact (not_lt_of_ge nonpositive) paid.positive
  | native pending => exact paid.native pending.pending
  | review failed => exact failed paid.review
  | grant failed => exact failed paid.grant
  | preparation item original failed => exact failed (paid.preparation item original)
  | continuation item original failed => exact failed (paid.continuation item original)
  | service short => exact short.refutes paid.served

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
