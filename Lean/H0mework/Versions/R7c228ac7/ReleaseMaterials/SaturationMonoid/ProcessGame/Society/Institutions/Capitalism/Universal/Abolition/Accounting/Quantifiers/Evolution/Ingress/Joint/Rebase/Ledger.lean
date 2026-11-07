import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def baseMapped := (Background.shape seed).mappedSupport seed.input seed.depth seed.count (Background.visit seed).current

theorem mapped_support_is_the_same_actual_background_and_original_productive_row :
    mappedSupport seed grossClaim = (baseMapped seed,some (.legacy (productiveState seed))) := by
  apply Prod.ext
  · exact congrArg (Background.translation seed).support.forward
      (Background.the_productive_row_and_the_actual_background_visit_have_the_same_support seed)
  · exact congrArg (Option.map Productive.State.legacy)
      (congrArg Prod.snd (Abolition.Accounting.Root.Reentry.Frame.support_eq seed.claim seed.current))

def baseOwner : OpenResponsibilityAt (Background.world seed) (baseMapped seed) :=
  Abolition.Root.Epoch.Finance.Future.Foundation.actualEntry seed.input seed.depth seed.count (Background.shape seed) _

def enteredEvolution : LedgerWriteEvolutionAt (NewN seed grossClaim)
    ⟨(baseMapped seed,some (.legacy (productiveState seed)))⟩ ⟨enteredSupport seed grossClaim⟩ :=
  Financial.Installation.wholeTransport (Background.enterEvolution seed) (baseOwner seed)
    (Productive.enter seed grossClaim)

/-- The representation write updates the complete original financial shape
and the same productive row together; it does not pay either material debt. -/
def evolution : LedgerWriteEvolutionAt (NewN seed grossClaim)
    ⟨mappedSupport seed grossClaim⟩ ⟨enteredSupport seed grossClaim⟩ :=
  (mapped_support_is_the_same_actual_background_and_original_productive_row seed grossClaim).symm ▸
    enteredEvolution seed grossClaim

theorem every_original_claim_survives_the_joint_representation_write
    (row : OpenResponsibilityAt (NewN seed grossClaim) (mappedSupport seed grossClaim)) :
    ((evolution seed grossClaim).destination row).1.claim = row.claim :=
  ((evolution seed grossClaim).destination row).2.toDebtLineage.claim_eq.symm

theorem no_original_progress_budget_is_refilled
    (row : OpenResponsibilityAt (NewN seed grossClaim) (mappedSupport seed grossClaim)) :
    ((evolution seed grossClaim).destination row).1.progressBudget ≤ row.progressBudget :=
  ((evolution seed grossClaim).destination row).2.progressBudget_not_refilled

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
