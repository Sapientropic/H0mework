import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Execution
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.InventoryExact

/-! The original lifecycle shares, read as the raw source's claim matrix.
No account or obligation is added by this readout. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot Source.Program
open scoped BigOperators

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem oneVisit_claims_source_next
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (state : (process input).GeneratedState)
    (matched : ledgerClaims input state.current = (ProgrammeSource.rawCurrent input visit.current).claims) :
    ledgerClaims input (oneVisit input visit state).current =
      (ProgrammeSource.rawCurrent input (ProgrammeSource.next input visit.current)).claims := by
  rw [ProgrammeSource.actual_raw_next]
  exact consumeOrigins_execute input (inventoryAt input visit) state
    (ProgrammeSource.rawCurrent input visit.current) 0 (ProgrammeSource.rawEvent input visit.current)
    (inventoryAt_instructions_exact input visit) matched

theorem generated_prefix_claims
    (initialZero : input.initial.claims = fun _ _ _ => 0) (index : Nat) :
    ledgerClaims input (accountAt input index).current =
      (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input index).current).claims := by
  induction index with
  | zero =>
      funext instrument debtor creditor
      change 0 = input.initial.claims instrument debtor creditor
      rw [initialZero]
  | succ index prior =>
      exact oneVisit_claims_source_next input (ProgrammeHistory.visitAt input index)
        (accountAt input index) prior

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
