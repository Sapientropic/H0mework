import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Accounts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (mechanism : Trials.Mechanism Party Good Port Technology Instrument)

def attempt (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ) :=
  match prepare source mechanism with
  | .ready prepared => (execute prepared nature proposed).current prepared nature proposed
  | _ => source.advance

def PreparationDisposition : Prop :=
  match prepare source mechanism with
  | .providerBlocked _failures | .payerBlocked _failures =>
      ∀ word ∈ Material.Migration.sourceWords (sourceInput source) source.raw mechanism.code.actionLimit,
        ¬ Outside.Checks (sourceInput source) source.raw source.members word
  | .noForecast schedule _ => natureDomain schedule.programme = []
  | .riskBlocked schedule _ _ _ =>
      ¬ (∀ nature ∈ natureDomain schedule.programme, Source.branchChecks schedule mechanism.investmentPort nature)
  | .ready prepared => ∀ (nature : prepared.schedule.programme.QuotedNature) ready review,
      type_of% (the_prepared_default_payment_generates_its_same_whole_ledger_successor prepared nature ready review)

theorem every_actual_preparation_generates_its_price_execution_or_exact_source_obstruction :
    PreparationDisposition source mechanism := by
  unfold PreparationDisposition
  cases prepare source mechanism with
  | providerBlocked failures | payerBlocked failures =>
      exact Outside.every_obstruction_excludes_every_feasible_original_alternative _ _ _ _ failures
  | noForecast schedule empty => exact empty
  | riskBlocked schedule nature original failed =>
      exact Source.each_failed_preflight_keeps_its_original_branch_and_check schedule _ nature original failed
  | ready prepared => exact the_prepared_default_payment_generates_its_same_whole_ledger_successor prepared

omit [DecidableEq Technology] in
theorem the_failed_preparation_keeps_the_original_root_and_its_whole_ledger_next :
    source.advance.inquiry.erase = (RootInquiryProcessNode.answered source.inquiry PUnit.unit).erase ∧
      Evolving.Epoch.Current.ClosedAt source :=
  ⟨source.advance_is_the_actual_root_successor.1,source.the_source_generates_its_whole_ledger_actual_epoch⟩

theorem the_method_cannot_return_an_unaccounted_failure_current
    (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ)
    (rejected : ∀ prepared, prepare source mechanism ≠ .ready prepared) :
    attempt source mechanism nature proposed = source.advance := by
  unfold attempt
  cases generated : prepare source mechanism <;> try rfl
  exact False.elim (rejected _ generated)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
