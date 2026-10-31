import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Assessment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit : Nat)

def applyWord (current : RawCurrent Party Good Technology Instrument) (index : Nat) :=
  match (assess input depth count prefixLimit renewalLimit current index).word input depth count prefixLimit renewalLimit with
  | some word => input.law.next current word
  | none => current

/-- Only a finite actual prefix is evaluated at each source occurrence. The
stored continuation is source-selected code, not a completed future. -/
def rawAt : Nat → RawCurrent Party Good Technology Instrument
  | 0 => origin input depth count
  | index + 1 => applyWord input depth count prefixLimit renewalLimit
      (rawAt index) index

def wordAt (index : Nat) :=
  (assess input depth count prefixLimit renewalLimit
    (rawAt input depth count prefixLimit renewalLimit index) index).word input depth count prefixLimit renewalLimit

def actualItems (index : Nat) :=
  match wordAt input depth count prefixLimit renewalLimit index with
  | some word => input.law.rawItems (rawAt input depth count prefixLimit renewalLimit index) word
  | none => []

theorem selected_first_write
    (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
    (selected : selection input depth count prefixLimit renewalLimit = .accepted plan) :
    rawAt input depth count prefixLimit renewalLimit 1 = input.law.next (origin input depth count) plan.pair.1 := by
  simp only [rawAt, applyWord, assessed_prefix_is_paid input depth count prefixLimit renewalLimit plan selected]

theorem selected_continuation_is_the_original_interpreter
    (timing : input.law.TimeIndependent) (policy : input.law.ReserveInsensitive)
    (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
    (selected : selection input depth count prefixLimit renewalLimit = .accepted plan) (index : Nat) :
    rawAt input depth count prefixLimit renewalLimit (index + 1) =
      (Material.Continuation.repeatPeriod input (input.law.next (origin input depth count) plan.pair.1)
        plan.pair.2).currentAt index := by
  induction index with
  | zero => exact selected_first_write input depth count prefixLimit renewalLimit plan selected
  | succ index prior =>
      have paid := plan.every_generated_period input _ _ _ _ _ timing policy index
      have financial := Material.Continuation.Balance.checked_word_is_nonfinancial .accumulating input.law
        (input.law.next (origin input depth count) plan.pair.1) plan.pair.2 plan.checked.2.2.2.1
      change applyWord input depth count prefixLimit renewalLimit
        (rawAt input depth count prefixLimit renewalLimit (index + 1)) (index + 1) = _
      rw [prior]
      simp only [applyWord, assessed_renewal_is_paid input depth count prefixLimit renewalLimit plan selected
        _ index ⟨financial, paid.2.1, paid.1⟩]
      rfl

theorem every_selected_period_keeps_original_life_and_debt
    (timing : input.law.TimeIndependent) (policy : input.law.ReserveInsensitive)
    (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
    (selected : selection input depth count prefixLimit renewalLimit = .accepted plan) (index : Nat) :
    Material.PeriodChecks input (rawAt input depth count prefixLimit renewalLimit (index + 1))
        (cohort input depth count) plan.pair.2 ∧
      Material.OriginalNeedFloor input (origin input depth count)
        (rawAt input depth count prefixLimit renewalLimit (index + 1)) (cohort input depth count) plan.pair.2 ∧
      (rawAt input depth count prefixLimit renewalLimit (index + 1)).claims = (origin input depth count).claims := by
  rw [selected_continuation_is_the_original_interpreter input depth count prefixLimit renewalLimit timing policy plan selected]
  exact plan.every_generated_period input _ _ _ _ _ timing policy index

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration
