import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Method

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

/-- Restrictions of the original source writes; no new account or receipt
is constructed, including when an attempted risk price is rejected. -/
def Accounted (source target : C) : Prop :=
  ∃ claimMap : source.native.frame.N.Claim → target.native.frame.N.Claim,
    ∃ carry : OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current) →
      OpenResponsibilityAt target.native.frame.N (target.native.frame.sourceSupport target.native.visit.current),
    Function.Injective claimMap ∧ ∀ row, (carry row).claim = claimMap row.claim ∧
      (carry row).progressBudget ≤ row.progressBudget

theorem Accounted.trans {source middle target : C}
    (first : Accounted source middle) (second : Accounted middle target) : Accounted source target := by
  obtain ⟨firstMap,firstCarry,firstInjective,firstRows⟩ := first
  obtain ⟨secondMap,secondCarry,secondInjective,secondRows⟩ := second
  refine ⟨secondMap ∘ firstMap,secondCarry ∘ firstCarry,secondInjective.comp firstInjective,?_⟩
  intro row
  have before := firstRows row
  have after := secondRows (firstCarry row)
  exact ⟨after.1.trans (congrArg secondMap before.1),after.2.trans before.2⟩

theorem the_original_actual_next_carries_every_old_row (source : C) : Accounted source source.advance :=
  ⟨Characterization.Escape.nextClaim source,Characterization.Escape.nextRow source,
    Characterization.Escape.nextClaim_does_not_merge_original_claims source,
    fun row => ⟨Characterization.Escape.nextRow_keeps_the_same_source_claim source row,
      Characterization.Escape.nextRow_never_refills_an_original_residual source row⟩⟩

theorem a_queued_refusal_next_carries_every_original_row (source : C)
    (request : Request Party Good Port Technology Instrument) : Accounted source (Runtime.afterBody source request) :=
  ⟨Characterization.Escape.nextClaim (Runtime.queued source request),
    Characterization.Escape.nextRow (Runtime.queued source request),
    Characterization.Escape.nextClaim_does_not_merge_original_claims (Runtime.queued source request),
    fun row => ⟨Characterization.Escape.nextRow_keeps_the_same_source_claim (Runtime.queued source request) row,
      Characterization.Escape.nextRow_never_refills_an_original_residual (Runtime.queued source request) row⟩⟩

theorem every_runtime_outcome_carries_its_complete_original_account
    {source : C} {word : RawEvent Party Good Port Technology Instrument}
    (outcome : Runtime.Outcome source word) : Accounted source outcome.current := by
  cases outcome with
  | completed target actual => exact actual.carries_every_original_row_and_claim_without_refilling
  | blocked front stopped request remaining split actual issue =>
      exact Accounted.trans actual.carries_every_original_row_and_claim_without_refilling
        (a_queued_refusal_next_carries_every_original_row stopped request)

variable [DecidableEq Technology]

theorem every_risk_protocol_execution_carries_all_original_responsibilities
    {source : C} {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
    (prepared : Prepared source mechanism) (nature : Request Party Good Port Technology Instrument)
    (proposed : Option ℚ) (execution : Execution prepared nature proposed) :
    Accounted source (execution.current prepared nature proposed) :=
  match execution with
  | .interrupted body _ => every_runtime_outcome_carries_its_complete_original_account body
  | .delivered _ actualBody price =>
      Accounted.trans actualBody.carries_every_original_row_and_claim_without_refilling
        (every_runtime_outcome_carries_its_complete_original_account price)

theorem every_actual_risk_attempt_carries_all_original_rows_and_claims
    (source : C) (mechanism : Trials.Mechanism Party Good Port Technology Instrument)
    (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ) :
    Accounted source (attempt source mechanism nature proposed) := by
  unfold attempt
  cases prepare source mechanism with
  | providerBlocked failures | payerBlocked failures | noForecast schedule empty | riskBlocked schedule failed original issue =>
      exact the_original_actual_next_carries_every_old_row source
  | ready prepared =>
      exact every_risk_protocol_execution_carries_all_original_responsibilities prepared nature proposed
        (execute prepared nature proposed)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
