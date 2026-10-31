import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Advance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

/-- Restrictions of the same original whole-ledger writes; this introduces
no rows, claims, allocator or second financial account. -/
def sourceLedger : NativeCurrent.Step current.native :=
  if work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual then
    match Public.Accounting.registration? current.native.input current.native.depth current.native.count current.native.prefixLimit
        current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual with
    | some registered => current.native.birthStep registered
    | none => current.native.ordinaryStep
  else {
    next := Transition.nativeNext current work
    claimMap := id
    claim_injective := fun _ _ same => same
    carry := sequentialRow (Transition.generated current work)
    claim_commutes := sequentialRow_claim (Transition.generated current work)
    no_refill := sequentialRow_budget (Transition.generated current work)
    productive_history := rfl
    gross_history := rfl }

theorem sourceLedger_is_the_actual_next : current.sourceLedger.next = current.advance.native := by
  unfold sourceLedger advance
  split
  · split
    · rename_i registered selected
      rw [selected]
      rfl
    · rename_i selected
      rw [selected]
      rfl
  · rfl

theorem every_original_responsibility_keeps_its_claim_and_never_refills
    (row : OpenResponsibilityAt current.native.frame.N
      (current.native.frame.sourceSupport current.native.visit.current)) :
    (current.sourceLedger.carry row).claim = current.sourceLedger.claimMap row.claim ∧
      (current.sourceLedger.carry row).progressBudget ≤ row.progressBudget :=
  ⟨current.sourceLedger.claim_commutes row,current.sourceLedger.no_refill row⟩

theorem both_original_paid_rows_are_their_actual_carried_histories :
    current.sourceLedger.carry current.native.rows.productive = current.sourceLedger.next.rows.productive ∧
      current.sourceLedger.carry current.native.rows.gross = current.sourceLedger.next.rows.gross :=
  ⟨current.sourceLedger.productive_history,current.sourceLedger.gross_history⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
