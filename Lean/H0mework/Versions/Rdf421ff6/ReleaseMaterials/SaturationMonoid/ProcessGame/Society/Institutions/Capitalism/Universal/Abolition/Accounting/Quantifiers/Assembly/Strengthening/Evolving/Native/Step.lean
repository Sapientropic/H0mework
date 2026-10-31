import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Raw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Birth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Whole

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



/-- The next carrier and every old-row restriction of the same actual write.
This packages transport data; it is not another ledger or row registry. -/
structure Step where
  next : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  claimMap : current.frame.N.Claim → next.frame.N.Claim
  claim_injective : Function.Injective claimMap
  carry : OpenResponsibilityAt current.frame.N (current.frame.sourceSupport current.visit.current) →
    OpenResponsibilityAt next.frame.N (next.frame.sourceSupport next.visit.current)
  claim_commutes : ∀ row, (carry row).claim = claimMap row.claim
  no_refill : ∀ row, (carry row).progressBudget ≤ row.progressBudget
  productive_history : carry current.rows.productive = next.rows.productive
  gross_history : carry current.rows.gross = next.rows.gross

def ordinaryStep : Step current where
  next := ordinary current
  claimMap := id
  claim_injective := fun _ _ same => same
  carry := nextRow (full current).root current.visit ((full current).successor current.visit.current)
  claim_commutes := fun row => (nextRow_keeps_claim_and_never_refills _ _ _ row).1
  no_refill := fun row => (nextRow_keeps_claim_and_never_refills _ _ _ row).2
  productive_history := rfl
  gross_history := rfl

def rawStep (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) : Step current where
  next := raw current complete
  claimMap := id
  claim_injective := fun _ _ same => same
  carry := sequentialRow (rawAction current complete)
  claim_commutes := sequentialRow_claim (rawAction current complete)
  no_refill := sequentialRow_budget (rawAction current complete)
  productive_history := rfl
  gross_history := rfl

def birthStep (registered : Public.Accounting.Registration current.input current.depth current.count current.prefixLimit
    current.renewalLimit current.oldPast current.start current.actual.actual) : Step current where
  next := birth current registered
  claimMap := Sum.inl
  claim_injective := Sum.inl_injective
  carry := bornRow (birthAction current registered)
  claim_commutes := bornRow_claim (birthAction current registered)
  no_refill := bornRow_budget (birthAction current registered)
  productive_history := rfl
  gross_history := rfl

/-- Selection happens in the original installed source before the next is
read. No target, per-step invariant, or completed history is supplied. -/
def selected : Step current :=
  if complete : Public.Inquiry.HasWork current.frame current.actual.actual then
    match Public.Accounting.registration? current.input current.depth current.count current.prefixLimit
      current.renewalLimit current.oldPast current.start current.actual.actual with
    | some registered => birthStep current registered
    | none => ordinaryStep current
  else rawStep current complete

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
