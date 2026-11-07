import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {input : Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {current : RawCurrent Party Good Technology Instrument} {members : List Party}
  {budget : Nat} {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  (schedule : Schedule input current members budget mechanism) (purpose : Port)

def completedPayment {law : RawLaw Party Good Port Technology Instrument}
    {before : RawCurrent Party Good Technology Instrument} {payer provider : Party}
    {instrument : Instrument} {port : Port} {net : ℚ} : Settlement.Result law before payer provider instrument port net → Bool
  | .noPayment _ | .paid .. => true
  | _ => false

def retainedAccounts (nature : Request Party Good Port Technology Instrument) : Prop :=
  ∀ person ∈ mechanism.code.parties, ∀ good ∈ mechanism.code.goods,
    max (Outside.value input current person good schedule.provider.word)
        (Outside.value input current person good schedule.payer.word) ≤
      Arithmetic.completeIncome input.law (input.law.rawItems current (schedule.requests nature purpose)) person good

instance (nature : Request Party Good Port Technology Instrument) :
    Decidable (retainedAccounts schedule purpose nature) := by unfold retainedAccounts; infer_instance

def branchChecks (nature : schedule.programme.QuotedNature) : Prop :=
  (match schedule.payment nature.val purpose with
  | none => False
  | some payment => (payment.1 = 0 ∨ mechanism.terms.borrower ≠ mechanism.terms.lender) ∧
      completedPayment payment.2 = true ∧
        (payment.1 ≠ 0 → (schedule.programme.after nature.val).claims mechanism.terms.instrument
          (Settlement.debtor mechanism.terms.borrower mechanism.terms.lender payment.1)
          (Settlement.creditor mechanism.terms.borrower mechanism.terms.lender payment.1) = 0)) ∧
    Material.PeriodChecks input current members (schedule.requests nature.val purpose) ∧
      retainedAccounts schedule purpose nature.val

instance (nature : schedule.programme.QuotedNature) : Decidable (branchChecks schedule purpose nature) := by
  unfold branchChecks
  split <;> infer_instance

def preflight := Material.inspectList (branchChecks schedule purpose) (natureDomain schedule.programme)

theorem all_source_branches_pass_before_the_actual_nature
    (checks : ∀ nature ∈ natureDomain schedule.programme, branchChecks schedule purpose nature)
    (nature : schedule.programme.QuotedNature) : branchChecks schedule purpose nature :=
  checks nature (every_declared_nature_is_in_the_forecast_domain schedule.programme nature)

theorem every_approved_actual_branch_keeps_all_original_bearers_and_goods
    (nature : schedule.programme.QuotedNature) (checked : branchChecks schedule purpose nature)
    (person : Party) (good : Good) :
    Outside.value input current person good schedule.provider.word ≤
        Arithmetic.completeIncome input.law (input.law.rawItems current (schedule.requests nature.val purpose)) person good ∧
      Outside.value input current person good schedule.payer.word ≤
        Arithmetic.completeIncome input.law (input.law.rawItems current (schedule.requests nature.val purpose)) person good := by
  have noLoss := checked.2.2 person (mechanism.code.parties_cover person) good (mechanism.code.goods_cover good)
  exact ⟨(le_max_left _ _).trans noLoss,(le_max_right _ _).trans noLoss⟩

theorem every_approved_branch_pays_the_original_living_and_maintenance
    (nature : schedule.programme.QuotedNature) (checked : branchChecks schedule purpose nature)
    (person : Party) (present : person ∈ members) :
    Exit.Necessity.BundlePaid input.law current (schedule.requests nature.val purpose) person
        (input.law.necessities current person) .necessity ∧
      Exit.Necessity.BundlePaid input.law current (schedule.requests nature.val purpose) person
        (input.law.mandatoryMaintenance current person) .maintenance := checked.2.1.2.1 person present

theorem each_failed_preflight_keeps_its_original_branch_and_check
    (nature : schedule.programme.QuotedNature) (original : nature ∈ natureDomain schedule.programme)
    (failed : ¬ branchChecks schedule purpose nature) :
    ¬ (∀ branch ∈ natureDomain schedule.programme, branchChecks schedule purpose branch) := by
  intro all
  exact failed (all nature original)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
