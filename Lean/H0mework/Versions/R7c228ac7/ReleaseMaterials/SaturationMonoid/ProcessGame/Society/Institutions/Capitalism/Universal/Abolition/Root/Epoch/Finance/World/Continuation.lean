import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Evolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (base : WorldRelationNetwork)

theorem earlierTail {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (edge : (Financial.process input).Edge current) (account : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input (.step run edge))).current account.current)) :
    Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current account.current) :=
  tail.map fun later => (LegacyLaw.runImage input depth count (first := OldAccount input run)
    (last := OldAccount input (.step run edge)) (.step .nil edge)).concatRuns (process input depth count) later

private theorem laterTail {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current account.current))
    (item : ActualItem input depth count) :
    Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current
      ((consume input depth count item account).next input depth count).current) :=
  tail.map fun prior => prior.concatRuns (process input depth count)
    ((consume input depth count item account).transition input depth count)

def currentOwner (baseSupport : base.Support) (owner : OpenResponsibilityAt base baseSupport) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (process input depth count).GeneratedState) →
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current account.current)) →
    OpenResponsibilityAt (folded input depth count base run)
      (currentSupport input depth count base baseSupport run account tail)
  | _, .nil, _, _ => owner
  | _, .step prior (.admit claim), account, tail => oldEntry
      (currentOwner baseSupport owner prior account (earlierTail input depth count prior (.admit claim) account tail))
  | _, .step prior (.cross index obligation present boundary), account, tail =>
      currentOwner baseSupport owner prior account
        (earlierTail input depth count prior (.cross index obligation present boundary) account tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

variable {beforeSupport afterSupport : base.Support}

def continueItemEvolution
    (baseEvolution : LedgerWriteEvolutionAt base ⟨beforeSupport⟩ ⟨afterSupport⟩)
    (baseOwner : OpenResponsibilityAt base beforeSupport) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (process input depth count).GeneratedState) →
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current account.current)) →
    (item : ActualItem input depth count) →
    LedgerWriteEvolutionAt (folded input depth count base run)
      ⟨currentSupport input depth count base beforeSupport run account tail⟩
      ⟨currentSupport input depth count base afterSupport run
        ((consume input depth count item account).next input depth count) (laterTail input depth count run account tail item)⟩
  | _, .nil, _, _, _ => baseEvolution
  | _, .step prior (.admit claim), account, tail, item =>
      Financial.Installation.wholeTransport
        (continueItemEvolution baseEvolution baseOwner prior account
          (earlierTail input depth count prior (.admit claim) account tail) item)
        (currentOwner input depth count base beforeSupport baseOwner prior account
          (earlierTail input depth count prior (.admit claim) account tail))
        (LegacyLaw.Transport.actualItem (input := input) (depth := depth) (count := count)
          (before := OldAccount input prior) (claim := claim) account tail item)
  | _, .step prior (.cross index obligation present boundary), account, tail, item =>
      continueItemEvolution baseEvolution baseOwner prior account
        (earlierTail input depth count prior (.cross index obligation present boundary) account tail) item
  | _, .step _ (.reopen _ _ _ impossible), _, _, _ => impossible.elim

theorem continuing_item_keeps_all_old_rows_on_one_account
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current account.current))
    (item : ActualItem input depth count) :
    AllReadAccount input depth count base ((consume input depth count item account).next input depth count) run
      (currentSupport input depth count base afterSupport run
        ((consume input depth count item account).next input depth count) (laterTail input depth count run account tail item)) :=
  every_old_debt_reads_the_same_account input depth count base afterSupport run _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.continueItemEvolution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.continuing_item_keeps_all_old_rows_on_one_account
