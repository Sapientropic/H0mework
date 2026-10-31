import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (base : WorldRelationNetwork) (initial : (process input depth count).GeneratedState)

def entry (baseEntry : ∀ support, OpenResponsibilityAt base support) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (support : (Future.world input depth count base initial run).Support) →
    OpenResponsibilityAt (Future.world input depth count base initial run) support
  | _, .nil, support => baseEntry support
  | _, .step prior (.admit _), support => oldEntry (state? := support.2) (entry baseEntry prior support.1)
  | _, .step prior (.cross _ _ _ _), support => entry baseEntry prior support
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

def disposition (baseDisposition : ∀ support kind, base.DispositionAt support kind) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (support : (Future.world input depth count base initial run).Support) →
    (kind : WorldDispositionKind) → (Future.world input depth count base initial run).DispositionAt support kind
  | _, .nil, support, kind => baseDisposition support kind
  | _, .step prior (.admit _), support, .supportSettlement => disposition baseDisposition prior support.1 .supportSettlement
  | _, .step prior (.admit _), support, .transfer => .inl (disposition baseDisposition prior support.1 .transfer)
  | _, .step prior (.admit _), support, .lawSurfaceExtension => .inl (disposition baseDisposition prior support.1 .lawSurfaceExtension)
  | _, .step prior (.cross _ _ _ _), support, kind => disposition baseDisposition prior support kind
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count sourceDepth sourceCount : Nat)
  {current : ResponsibilityState (vocabulary input depth count)}
  (run : (process input depth count).Run (initial input depth count sourceDepth sourceCount).current current)

def canonicalEntry := Foundation.entry input depth count (base input depth count sourceDepth sourceCount)
  (initial input depth count sourceDepth sourceCount)
  (Foundation.actualEntry input depth count (shape input sourceDepth sourceCount)) run

def canonicalDisposition := Foundation.disposition input depth count (base input depth count sourceDepth sourceCount)
  (initial input depth count sourceDepth sourceCount)
  (Foundation.actualDisposition input depth count (shape input sourceDepth sourceCount)) run

#print axioms canonicalEntry
#print axioms canonicalDisposition

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
