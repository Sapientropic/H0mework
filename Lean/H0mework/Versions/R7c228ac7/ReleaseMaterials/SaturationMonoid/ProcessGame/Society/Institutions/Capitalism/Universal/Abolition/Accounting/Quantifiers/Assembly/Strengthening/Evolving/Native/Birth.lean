import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Ordinary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

namespace NativeCurrent

variable (registered : Public.Accounting.Registration current.input current.depth current.count current.prefixLimit
  current.renewalLimit current.oldPast current.start current.actual.actual)

def birthAction := Factory.Direct.debtCore current.frame current.reader current.visit current.actual current.authority registered

def birth : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := current.input
  depth := current.depth
  count := current.count
  prefixLimit := current.prefixLimit
  renewalLimit := current.renewalLimit
  oldPast := current.oldPast
  start := current.start
  frame := Public.Accounting.Born.Action.targetFrame (full current) current.visit current.actual.actual registered
  reader := current.reader
  visit := Public.Accounting.Born.Action.completeNextVisit (full current) current.actual.actual registered
  actual := ⟨registered.next, Public.Accounting.Born.Source.first_visit_is_the_literal_registered_next
    (full current).family current.actual.actual registered⟩
  bodyPaid := rfl
  authority := Public.Accounting.Born.Action.completeNextAuthority (full current) current.visit current.actual.actual
    current.actual.aligned registered current.reader current.authority
  rows := afterBirth (birthAction current registered) current.rows

theorem birth_embeds_both_original_claims :
    (birth current registered).rows.productive.claim = .inl current.rows.productive.claim ∧
      (birth current registered).rows.gross.claim = .inl current.rows.gross.claim :=
  birth_preserves_both_original_claims _ _

theorem birth_cannot_mistake_either_original_claim_for_the_new_loan :
    (birth current registered).rows.productive.claim ≠ .inr (birthAction current registered).target.law.debtClaim ∧
      (birth current registered).rows.gross.claim ≠ .inr (birthAction current registered).target.law.debtClaim :=
  neither_original_claim_is_the_fresh_native_claim _ _

theorem birth_is_the_same_actual_admission_next :
    (birth current registered).erase =
      ⟨(birthAction current registered).target.TargetN,
        (birthAction current registered).target.targetAnswerAndNext.nextCurrent⟩ := by
  exact congrArg (fun x => (⟨(birthAction current registered).target.TargetN,x⟩ : AnyAuthoritativeRootCurrent))
    (birthAction current registered).target.canonical_targetNextVisit_eq.symm

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
