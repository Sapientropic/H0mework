import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Completion

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  (prepared : Prepared source mechanism) (nature : Request Party Good Port Technology Instrument)
local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

theorem the_returned_root_is_the_literal_complete_price_execution
    {afterBody target : C} (actualBody : Runtime.Trace source (bodyWord prepared nature) afterBody)
    (actualPrice : Runtime.Trace afterBody (priceWord prepared nature none) target) :
    target.raw = ((sourceInput source).law.execute source.raw 0
      (prepared.schedule.requests nature mechanism.investmentPort)).final := by
  have paid := actualPrice.raw_is_the_complete_original_execution 0
  rw [actualBody.keeps_the_original_source_input,
    the_actual_trial_endpoint_is_the_original_price_basis prepared nature actualBody] at paid
  have normalized := Runtime.public_normalisation_keeps_the_complete_original_execution source.native.input.law
    (prepared.schedule.programme.after nature) 0
    ((decision prepared nature none).word prepared.schedule mechanism.investmentPort)
  have actual := paid.trans normalized
  rw [the_default_payment_is_exactly_the_preflighted_source_suffix prepared nature,RawLaw.execute_append]
  exact actual.trans (Settlement.original_raw_final_is_independent_of_the_inventory_index
    (sourceInput source).law _ _ 0 (0 + (prepared.schedule.programme.word nature).length))

theorem both_actual_phases_carry_every_original_row_without_refilling
    {afterBody target : C} (actualBody : Runtime.Trace source (bodyWord prepared nature) afterBody)
    (actualPrice : Runtime.Trace afterBody (priceWord prepared nature none) target) :
    ∃ claimMap : source.native.frame.N.Claim → target.native.frame.N.Claim,
      ∃ carry : OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current) →
        OpenResponsibilityAt target.native.frame.N (target.native.frame.sourceSupport target.native.visit.current),
      Function.Injective claimMap ∧ ∀ row, (carry row).claim = claimMap row.claim ∧
        (carry row).progressBudget ≤ row.progressBudget := by
  obtain ⟨firstMap,firstCarry,firstInjective,first⟩ := actualBody.carries_every_original_row_and_claim_without_refilling
  obtain ⟨secondMap,secondCarry,secondInjective,second⟩ := actualPrice.carries_every_original_row_and_claim_without_refilling
  refine ⟨secondMap ∘ firstMap,secondCarry ∘ firstCarry,secondInjective.comp firstInjective,?_⟩
  intro row
  exact ⟨(second (firstCarry row)).1.trans (congrArg secondMap (first row).1),
    (second (firstCarry row)).2.trans (first row).2⟩

theorem actual_risk_completion_keeps_each_original_living_and_maintenance_payment
    (nature : prepared.schedule.programme.QuotedNature) (person : Party) (present : person ∈ source.members) :
    Exit.Necessity.BundlePaid (sourceInput source).law source.raw
        (prepared.schedule.requests nature.val mechanism.investmentPort) person
        ((sourceInput source).law.necessities source.raw person) .necessity ∧
      Exit.Necessity.BundlePaid (sourceInput source).law source.raw
        (prepared.schedule.requests nature.val mechanism.investmentPort) person
        ((sourceInput source).law.mandatoryMaintenance source.raw person) .maintenance :=
  Source.every_approved_branch_pays_the_original_living_and_maintenance _ _ nature
    (prepared.allBranches nature (every_declared_nature_is_in_the_forecast_domain _ nature)) person present

theorem all_original_full_accounts_retain_both_real_outside_benchmarks
    (nature : prepared.schedule.programme.QuotedNature) (person : Party) (good : Good) :
    Outside.value (sourceInput source) source.raw person good prepared.schedule.provider.word ≤
        Arithmetic.completeIncome (sourceInput source).law
          ((sourceInput source).law.rawItems source.raw (prepared.schedule.requests nature.val mechanism.investmentPort)) person good ∧
      Outside.value (sourceInput source) source.raw person good prepared.schedule.payer.word ≤
        Arithmetic.completeIncome (sourceInput source).law
          ((sourceInput source).law.rawItems source.raw (prepared.schedule.requests nature.val mechanism.investmentPort)) person good :=
  Source.every_approved_actual_branch_keeps_all_original_bearers_and_goods _ _ nature
    (prepared.allBranches nature (every_declared_nature_is_in_the_forecast_domain _ nature)) person good

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
