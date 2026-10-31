import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Validity

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



def advanceClaim : current.frame.N.Claim → (advance current).frame.N.Claim := (selected current).claimMap

def advanceRow (row : OpenResponsibilityAt current.frame.N (current.frame.sourceSupport current.visit.current)) :
    OpenResponsibilityAt (advance current).frame.N ((advance current).frame.sourceSupport (advance current).visit.current) :=
  (selected current).carry row

theorem advanceRow_keeps_the_original_claim
    (row : OpenResponsibilityAt current.frame.N (current.frame.sourceSupport current.visit.current)) :
    (advanceRow current row).claim = advanceClaim current row.claim := (selected current).claim_commutes row

theorem advanceRow_never_refills_an_old_responsibility
    (row : OpenResponsibilityAt current.frame.N (current.frame.sourceSupport current.visit.current)) :
    (advanceRow current row).progressBudget ≤ row.progressBudget := (selected current).no_refill row

theorem advanceClaim_does_not_merge_original_claims : Function.Injective (advanceClaim current) :=
  (selected current).claim_injective

theorem advanceRow_is_the_same_productive_history :
    advanceRow current current.rows.productive = (advance current).rows.productive :=
  (selected current).productive_history

theorem advanceRow_is_the_same_gross_history :
    advanceRow current current.rows.gross = (advance current).rows.gross :=
  (selected current).gross_history

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
