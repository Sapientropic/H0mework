import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Evolution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Transport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  {OldBase NewBase : WorldRelationNetwork}
  (baseMap : TypedSemanticWorldNetworkTranslationAt OldBase NewBase)
  (oldSupport : OldBase.Support) (newSupport : NewBase.Support)

def enteredSupport {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) :
    (folded input depth count NewBase run).Support :=
  currentSupport input depth count NewBase newSupport run (Legacy.generated input depth count account)
    (tail.map (LegacyLaw.runImage input depth count (first := OldAccount input run)))

/-- Enter the shared account representation along the already generated old
run. No financial instruction or extra native edge is executed. -/
def enterEvolution
    (baseEvolution : LedgerWriteEvolutionAt NewBase ⟨baseMap.support.forward oldSupport⟩ ⟨newSupport⟩)
    (baseOwner : OpenResponsibilityAt OldBase oldSupport) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (Financial.process input).GeneratedState) →
    (tail : Nonempty ((Financial.process input).Run current account.current)) →
    LedgerWriteEvolutionAt (folded input depth count NewBase run)
      ⟨mappedSupport input depth count baseMap oldSupport run account tail⟩
      ⟨enteredSupport input depth count newSupport run account tail⟩
  | _, .nil, _, _ => baseEvolution
  | _, .step prior (.admit claim), account, tail =>
      Financial.Installation.wholeTransport
        (enterEvolution baseEvolution baseOwner prior account
          (Financial.Installation.prependNative input (.admit claim) rfl tail))
        ((foldTranslation input depth count baseMap prior).oldOpenLedger _ |>.forward
          (Financial.Installation.liftOwner input OldBase oldSupport baseOwner prior account
            (Financial.Installation.prependNative input (.admit claim) rfl tail)))
        (LegacyLaw.Transport.enter (input := input) (depth := depth) (count := count)
          (before := OldAccount input prior) (claim := claim) account tail)
  | _, .step prior (.cross index obligation present boundary), account, tail =>
      enterEvolution baseEvolution baseOwner prior account
        (Financial.Installation.prependNative input (.cross index obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

theorem entry_reads_the_unchanged_account
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) :
    AllReadAccount input depth count NewBase (Legacy.generated input depth count account) run
      (enteredSupport input depth count newSupport run account tail) :=
  every_old_debt_reads_the_same_account input depth count NewBase newSupport run _ _

theorem enterEvolution_preserves_budget
    (baseEvolution : LedgerWriteEvolutionAt NewBase ⟨baseMap.support.forward oldSupport⟩ ⟨newSupport⟩)
    (baseOwner : OpenResponsibilityAt OldBase oldSupport)
    (baseBudget : ∀ entry, (baseEvolution.destination entry).1.progressBudget = entry.progressBudget)
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current))
    (entry : OpenResponsibilityAt (folded input depth count NewBase run)
      (mappedSupport input depth count baseMap oldSupport run account tail)) :
    ((enterEvolution input depth count baseMap oldSupport newSupport baseEvolution baseOwner run account tail).destination
      entry).1.progressBudget = entry.progressBudget := by
  induction run with
  | nil => exact baseBudget entry
  | step prior edge inherited =>
      cases edge with
      | admit claim =>
          rcases entry with ⟨responsibility, opened⟩
          cases responsibility with
          | inl original =>
              exact inherited (Financial.Installation.prependNative input (.admit claim) rfl tail) ⟨original, opened⟩
          | inr debt =>
              rcases opened with ⟨⟨same⟩⟩
              subst debt
              rfl
      | cross index obligation present boundary =>
          exact inherited (Financial.Installation.prependNative input (.cross index obligation present boundary) rfl tail) entry
      | reopen _ _ _ impossible => exact impossible.elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.enterEvolution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.entry_reads_the_unchanged_account
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.enterEvolution_preserves_budget
