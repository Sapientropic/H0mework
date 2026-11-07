import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Current" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Native" => Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

private def claimAfter {origin : Native} (step : Evolving.NativeCurrent.Step origin)
    (target : Native) (same : step.next = target) : origin.frame.N.Claim → target.frame.N.Claim :=
  same ▸ step.claimMap

private def rowAfter {origin : Native} (step : Evolving.NativeCurrent.Step origin)
    (target : Native) (same : step.next = target)
    (row : OpenResponsibilityAt origin.frame.N (origin.frame.sourceSupport origin.visit.current)) :
    OpenResponsibilityAt target.frame.N (target.frame.sourceSupport target.visit.current) :=
  same ▸ step.carry row

private theorem rowAfter_claim {origin : Native} (step : Evolving.NativeCurrent.Step origin)
    (target : Native) (same : step.next = target)
    (row : OpenResponsibilityAt origin.frame.N (origin.frame.sourceSupport origin.visit.current)) :
    (rowAfter step target same row).claim = claimAfter step target same row.claim := by
  subst target
  exact step.claim_commutes row

private theorem rowAfter_budget {origin : Native} (step : Evolving.NativeCurrent.Step origin)
    (target : Native) (same : step.next = target)
    (row : OpenResponsibilityAt origin.frame.N (origin.frame.sourceSupport origin.visit.current)) :
    (rowAfter step target same row).progressBudget ≤ row.progressBudget := by
  subst target
  exact step.no_refill row

private theorem claimAfter_injective {origin : Native} (step : Evolving.NativeCurrent.Step origin)
    (target : Native) (same : step.next = target) : Function.Injective (claimAfter step target same) := by
  subst target
  exact step.claim_injective

/-- These are restrictions of the actual sourceLedger and its exact next;
no new row, allocation or responsibility registry is introduced. -/
def nextClaim (current : Current) : current.native.frame.N.Claim → current.advance.native.frame.N.Claim :=
  claimAfter current.sourceLedger current.advance.native current.sourceLedger_is_the_actual_next

def nextRow (current : Current)
    (row : OpenResponsibilityAt current.native.frame.N (current.native.frame.sourceSupport current.native.visit.current)) :
    OpenResponsibilityAt current.advance.native.frame.N
      (current.advance.native.frame.sourceSupport current.advance.native.visit.current) :=
  rowAfter current.sourceLedger current.advance.native current.sourceLedger_is_the_actual_next row

theorem nextRow_keeps_the_same_source_claim (current : Current)
    (row : OpenResponsibilityAt current.native.frame.N (current.native.frame.sourceSupport current.native.visit.current)) :
    (nextRow current row).claim = nextClaim current row.claim :=
  rowAfter_claim _ _ _ row

theorem nextRow_never_refills_an_original_residual (current : Current)
    (row : OpenResponsibilityAt current.native.frame.N (current.native.frame.sourceSupport current.native.visit.current)) :
    (nextRow current row).progressBudget ≤ row.progressBudget :=
  rowAfter_budget _ _ _ row

theorem nextClaim_does_not_merge_original_claims (current : Current) : Function.Injective (nextClaim current) :=
  claimAfter_injective _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
