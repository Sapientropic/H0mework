import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Redemption (sourceLaw sourceOrigin)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- The amount is submitted before execution. Both original proposal words
can have any finite length and are interpreted at their generated cuts. -/
structure Proposal (Party Good Port Technology Instrument : Type) where
  preparation : List (Option (Compile.RawInput Party Good Port Technology Instrument))
  quantity : ℚ
  continuation : List (Option (Compile.RawInput Party Good Port Technology Instrument))

local notation "Plan" => Proposal Party Good Port Technology Instrument

def funded (source : C) (plan : Plan) : C :=
  Execution.endAt source plan.preparation

def redeemed (source : C) (position : Position Party Instrument) (plan : Plan) : C :=
  Execution.endAt (funded source plan) (grantScript (funded source plan) position plan.quantity)

def compile (source : C) (position : Position Party Instrument) (plan : Plan) : Script :=
  plan.preparation ++ grantScript (funded source plan) position plan.quantity ++ plan.continuation

theorem the_grant_and_its_continuation_share_the_actual_next
    (source : C) (position : Position Party Instrument) (plan : Plan) :
    Execution.endAt source (compile source position plan) =
      Execution.endAt (redeemed source position plan) plan.continuation := by
  simp only [compile, Execution.endAt_append, funded, redeemed]

def Independent (source : C) (excluded : List Party) (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  item.request.signer ∈ source.members ∧ item.request.signer ∉ excluded ∧ item.request.consents = [] ∧
    ∀ entry ∈ (sourceLaw source).actualDebit item.before item.request,
      0 < entry.2 → entry.1.1 = item.request.signer

instance (source : C) (excluded : List Party) (item : ExecutionItem Party Good Port Technology Instrument) :
    Decidable (Independent source excluded item) := by
  unfold Independent
  infer_instance

theorem every_grant_plan_uses_the_original_quote_and_material_body
    (source : C) (position : Position Party Instrument) (plan : Plan)
    (ready : Innovation.Contribution.Pricing.Root.Runtime.Ready (funded source plan))
    (review : Innovation.Contribution.Pricing.Root.Runtime.ReviewAvailable (funded source plan))
    (funding : Qualified (sourceLaw (funded source plan)) (sourceOrigin (funded source plan))
      (funded source plan).raw position plan.quantity) :
    PaidAt (funded source plan) position plan.quantity ∧
    Recorded source (compile source position plan) :=
  ⟨paid_grant_is_the_literal_original_issue_and_redemption _ _ _ ready review funding, record source _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
