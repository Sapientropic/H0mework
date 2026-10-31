import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Translation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.World

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

abbrev OldAccount {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) :=
  Financial.Installation.generatedAccount input run

variable (base : WorldRelationNetwork)

/-- The original admission tree is folded once; only its debt-state
representation is extended. No admission is replayed and no row is added. -/
def folded : {current : ResponsibilityState (Financial.vocabulary input)} →
    (Financial.process input).Run (.empty (Financial.vocabulary input)) current → WorldRelationNetwork
  | _, .nil => base
  | _, .step prior (.admit claim) =>
      ExtendedNetwork (folded prior) (LegacyLaw.law input depth count (OldAccount input prior) claim)
  | _, .step prior (.cross _ _ _ _) => folded prior
  | _, .step _ (.reopen _ _ _ impossible) => impossible.elim

variable {OldBase NewBase : WorldRelationNetwork}

def foldTranslation (baseMap : TypedSemanticWorldNetworkTranslationAt OldBase NewBase) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    TypedSemanticWorldNetworkTranslationAt (Financial.Installation.world input OldBase run)
      (folded input depth count NewBase run)
  | _, .nil => baseMap
  | _, .step prior (.admit claim) =>
      translation input depth count (OldAccount input prior) claim (foldTranslation baseMap prior)
  | _, .step prior (.cross _ _ _ _) => foldTranslation baseMap prior
  | _, .step _ (.reopen _ _ _ impossible) => impossible.elim

private theorem prependEdge {current : ResponsibilityState (Financial.vocabulary input)}
    (prior : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (edge : (Financial.process input).Edge current) (target : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input (.step prior edge))).current target.current)) :
    Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input prior)).current target.current) :=
  tail.map fun run => (LegacyLaw.runImage input depth count
    (first := OldAccount input prior) (last := OldAccount input (.step prior edge))
    (.step .nil edge)).concatRuns (process input depth count) run

/-- Every old debt support reads one and the same native continuation. -/
def currentSupport (baseSupport : base.Support) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (target : (process input depth count).GeneratedState) →
    Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current target.current) →
    (folded input depth count base run).Support
  | _, .nil, _, _ => baseSupport
  | _, .step prior (.admit claim), target, tail =>
      (currentSupport baseSupport prior target (prependEdge input depth count prior (.admit claim) target tail),
        some (.current target tail))
  | _, .step prior (.cross index obligation present boundary), target, tail =>
      currentSupport baseSupport prior target
        (prependEdge input depth count prior (.cross index obligation present boundary) target tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def AllReadAccount (target : (process input depth count).GeneratedState) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (folded input depth count base run).Support → Prop
  | _, .nil, _ => True
  | _, .step prior (.admit _), support => AllReadAccount target prior support.1 ∧
      match support.2 with
      | some (.current account _) => account = target
      | _ => False
  | _, .step prior (.cross _ _ _ _), support => AllReadAccount target prior support
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

theorem every_old_debt_reads_the_same_account (baseSupport : base.Support)
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (target : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (OldAccount input run)).current target.current)) :
    AllReadAccount input depth count base target run
      (currentSupport input depth count base baseSupport run target tail) := by
  induction run with
  | nil => trivial
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact ⟨inherited (prependEdge input depth count prior (.admit claim) target tail), rfl⟩
      | cross index obligation present boundary =>
          exact inherited (prependEdge input depth count prior (.cross index obligation present boundary) target tail)
      | reopen _ _ _ impossible => exact impossible.elim

/-- The target account is computed by the unique actual-item consumer. -/
def afterItemSupport (baseSupport : base.Support) (original : (Financial.process input).GeneratedState)
    (item : ActualItem input depth count) : (folded input depth count base original.generated).Support :=
  currentSupport input depth count base baseSupport original.generated
    ((consume input depth count item (Legacy.generated input depth count original)).next input depth count)
    ⟨(consume input depth count item (Legacy.generated input depth count original)).transition input depth count⟩

theorem actual_item_updates_every_old_debt_support (baseSupport : base.Support)
    (original : (Financial.process input).GeneratedState) (item : ActualItem input depth count) :
    AllReadAccount input depth count base
      ((consume input depth count item (Legacy.generated input depth count original)).next input depth count)
      original.generated (afterItemSupport input depth count base baseSupport original item) :=
  every_old_debt_reads_the_same_account input depth count base baseSupport original.generated _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.foldTranslation
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.actual_item_updates_every_old_debt_support
