import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Step

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


/-- The next is a restriction of the same source-owned selected write. -/
def advance : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) := (selected current).next

theorem advance_keeps_the_same_public_input : (advance current).input = current.input := by
  unfold advance selected
  split
  · split <;> rfl
  · rfl

theorem advance_has_no_capital_relation : Global.NoCapital (advance current).handlerLaw :=
  (advance current).the_actual_public_handler_excludes_every_capital_relation

theorem advance_keeps_both_original_responsibilities_paid :
    (advance current).rows.productive.progressBudget = 0 ∧ (advance current).rows.gross.progressBudget = 0 :=
  ⟨(advance current).rows.productive_zero,(advance current).rows.gross_zero⟩

theorem advance_eq_raw (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    advance current = raw current complete := by
  unfold advance selected
  rw [dif_neg complete]
  rfl

theorem advance_raw_account_heq (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    HEq (advance current).actual.actual.account current.actual.actual.account := by
  rw [advance_eq_raw current complete]
  exact HEq.rfl

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
