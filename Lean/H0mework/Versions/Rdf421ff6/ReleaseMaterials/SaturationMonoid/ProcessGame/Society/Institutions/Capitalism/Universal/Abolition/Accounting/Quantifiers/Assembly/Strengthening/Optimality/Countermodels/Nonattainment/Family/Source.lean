import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def upgrade (n : Nat) := request false (.revise false n)
def produce := request false (.produce false)
def repay := request false (.settle () false true 1)
def word (n : Nat) := [upgrade n,produce,repay]
def programme (n : Nat) := (word n).map Compile.RawInput.primitive

def upgraded (n : Nat) := {cutRaw with technology := n}
def produced (n : Nat) := law.paidStep (upgraded n) produce
def paid (n : Nat) := law.paidStep (produced n) repay

theorem source_revision_is_available (current : RawCurrent Bool Bool Nat Unit) (n : Nat) :
    law.Valid current (upgrade n) := by
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,RawLaw.ClaimGuard,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,NonnegativeBundle,upgrade,request,law,locate]

theorem source_revision_has_its_exact_actual_effect (n : Nat) : law.step before.raw (upgrade n) = upgraded n := by
  rw [RawLaw.step,if_pos (source_revision_is_available before.raw n),the_unpaid_cut_is_generated_by_the_original_actual_prefix]
  apply RawCurrent.ext
  · funext actor good
    simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,upgrade,request,flowAt,amount,law,upgraded,locate]
  · rfl
  · rfl
  · rfl
  · rfl

theorem source_production_is_affordable (n : Nat) : law.Valid (upgraded n) produce := by
  have positive := (epsilon_positive n).le
  have bound := epsilon_at_most_half n
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,RawLaw.ClaimGuard,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,NonnegativeBundle,produce,request,law,locate,
    flowAt,amount,upgraded,cutRaw,positive]
  linarith

theorem source_production_is_a_real_step (n : Nat) : law.step (upgraded n) produce = produced n := by
  rw [RawLaw.step,if_pos (source_production_is_affordable n)]
  rfl

theorem original_debt_is_payable_after_production (n : Nat) : law.Valid (produced n) repay := by
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,RawLaw.ClaimGuard,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,NonnegativeBundle,repay,request,law,locate,
    flowAt,amount,produced,upgraded,cutRaw,RawLaw.paidStep,RawLaw.nextClaims,produce]

theorem source_payment_is_a_real_step (n : Nat) : law.step (produced n) repay = paid n := by
  rw [RawLaw.step,if_pos (original_debt_is_payable_after_production n)]
  rfl

theorem every_original_family_request_is_actually_accepted (n : Nat)
    (item : ExecutionItem Bool Bool Unit Nat Unit) (listed : item ∈ (law.execute before.raw 0 (word n)).items) :
    law.Valid item.before item.request := by
  simp only [word,RawLaw.execute] at listed
  rcases List.mem_cons.mp listed with first | later
  · cases first; exact source_revision_is_available _ n
  · rcases List.mem_cons.mp later with second | later
    · cases second
      simpa only [source_revision_has_its_exact_actual_effect] using source_production_is_affordable n
    · rcases List.mem_cons.mp later with third | absent
      · cases third
        simpa only [source_revision_has_its_exact_actual_effect,source_production_is_a_real_step] using original_debt_is_payable_after_production n
      · cases absent

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
