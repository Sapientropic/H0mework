import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private def originalOwner (base : WorldRelationNetwork) (baseSupport : base.Support)
    (owner : OpenResponsibilityAt base baseSupport) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (Financial.process input).GeneratedState) →
    (tail : Nonempty ((Financial.process input).Run current account.current)) →
    OpenResponsibilityAt (Financial.Installation.world input base run)
      (Financial.Installation.support input base baseSupport run account tail)
  | _, .nil, _, _ => owner
  | _, .step prior (.admit claim), account, tail => oldEntry
      (originalOwner base baseSupport owner prior account
        (Financial.Installation.prependNative input (.admit claim) rfl tail))
  | _, .step prior (.cross index obligation present boundary), account, tail =>
      originalOwner base baseSupport owner prior account
        (Financial.Installation.prependNative input (.cross index obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def itemTarget (account : (Financial.process input).GeneratedState) (item : ActualItem input depth count) :
    (process input depth count).GeneratedState :=
  (consume input depth count item (Legacy.generated input depth count account)).next input depth count

private theorem itemTail {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) (item : ActualItem input depth count) :
    Nonempty ((process input depth count).Run (Legacy.generated input depth count (OldAccount input run)).current
      (itemTarget input depth count account item).current) :=
  tail.map fun prior => (LegacyLaw.runImage input depth count (first := OldAccount input run) prior).concatRuns
    (process input depth count) ((consume input depth count item (Legacy.generated input depth count account)).transition input depth count)

variable {OldBase NewBase : WorldRelationNetwork}
  (baseMap : TypedSemanticWorldNetworkTranslationAt OldBase NewBase)
  (oldSupport : OldBase.Support) (newSupport : NewBase.Support)

def mappedSupport {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) : (folded input depth count NewBase run).Support :=
  (foldTranslation input depth count baseMap run).support.forward
    (Financial.Installation.support input OldBase oldSupport run account tail)

def updatedSupport {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) (item : ActualItem input depth count) :
    (folded input depth count NewBase run).Support :=
  currentSupport input depth count NewBase newSupport run (itemTarget input depth count account item)
    (itemTail input depth count run account tail item)

/-- One actual item supplies every old debt-row update. The whole-ledger
consumer is the existing source-neutral `wholeTransport`. -/
def itemEvolution
    (baseEvolution : LedgerWriteEvolutionAt NewBase ⟨baseMap.support.forward oldSupport⟩ ⟨newSupport⟩)
    (baseOwner : OpenResponsibilityAt OldBase oldSupport) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (Financial.process input).GeneratedState) →
    (tail : Nonempty ((Financial.process input).Run current account.current)) →
    (item : ActualItem input depth count) →
    LedgerWriteEvolutionAt (folded input depth count NewBase run)
      ⟨mappedSupport input depth count baseMap oldSupport run account tail⟩
      ⟨updatedSupport input depth count newSupport run account tail item⟩
  | _, .nil, _, _, _ => baseEvolution
  | _, .step prior (.admit claim), account, tail, item =>
      Financial.Installation.wholeTransport
        (itemEvolution baseEvolution baseOwner prior account
          (Financial.Installation.prependNative input (.admit claim) rfl tail) item)
        ((foldTranslation input depth count baseMap prior).oldOpenLedger _ |>.forward
          (originalOwner input OldBase oldSupport baseOwner prior account
            (Financial.Installation.prependNative input (.admit claim) rfl tail)))
        (LegacyLaw.Transport.enterAndItem (input := input) (depth := depth) (count := count)
          (before := OldAccount input prior) (claim := claim) account tail item)
  | _, .step prior (.cross index obligation present boundary), account, tail, item =>
      itemEvolution baseEvolution baseOwner prior account
        (Financial.Installation.prependNative input (.cross index obligation present boundary) rfl tail) item
  | _, .step _ (.reopen _ _ _ impossible), _, _, _ => impossible.elim

theorem updated_support_reads_one_computed_account
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) (item : ActualItem input depth count) :
    AllReadAccount input depth count NewBase (itemTarget input depth count account item) run
      (updatedSupport input depth count newSupport run account tail item) :=
  every_old_debt_reads_the_same_account input depth count NewBase newSupport run _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.itemEvolution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.updated_support_reads_one_computed_account
