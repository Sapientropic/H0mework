import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.InstalledKeys
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Inquiry.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def inheritedEntry : {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (support : (World.folded input depth count (ProgrammeSource.N input) run).Support) →
    OpenResponsibilityAt (World.folded input depth count (ProgrammeSource.N input) run) support
  | _, .nil, support => ProgrammeLiving.inquiryEntrySupport input support
  | _, .step prior (.admit _), support => oldEntry (state? := support.2) (inheritedEntry prior support.1)
  | _, .step prior (.cross _ _ _ _), support => inheritedEntry prior support
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

def inheritedDisposition : {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (support : (World.folded input depth count (ProgrammeSource.N input) run).Support) →
    (kind : WorldDispositionKind) → (World.folded input depth count (ProgrammeSource.N input) run).DispositionAt support kind
  | _, .nil, _, .supportSettlement => ()
  | _, .nil, support, .transfer => ProgrammeWorld.transferReceipt (ProgrammeSource.observation? input) support
  | _, .nil, _, .lawSurfaceExtension => ()
  | _, .step prior (.admit _), support, .supportSettlement => inheritedDisposition prior support.1 .supportSettlement
  | _, .step prior (.admit _), support, .transfer => .inl (inheritedDisposition prior support.1 .transfer)
  | _, .step prior (.admit _), support, .lawSurfaceExtension => .inl (inheritedDisposition prior support.1 .lawSurfaceExtension)
  | _, .step prior (.cross _ _ _ _), support, kind => inheritedDisposition prior support kind
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def actualEntry : {native : Financial.Installation.NativeFrame input} → (shape : Installation.Shape input native) →
    (support : (shape.world input depth count).Support) → OpenResponsibilityAt (shape.world input depth count) support
  | _, .base start _, support => inheritedEntry input depth count start.account.generated support
  | _, .born prior _, support => oldEntry (state? := support.2) (actualEntry prior support.1)

def actualDisposition : {native : Financial.Installation.NativeFrame input} → (shape : Installation.Shape input native) →
    (support : (shape.world input depth count).Support) → (kind : WorldDispositionKind) →
    (shape.world input depth count).DispositionAt support kind
  | _, .base start _, support, kind => inheritedDisposition input depth count start.account.generated support kind
  | _, .born prior _, support, .supportSettlement => actualDisposition prior support.1 .supportSettlement
  | _, .born prior _, support, .transfer => .inl (actualDisposition prior support.1 .transfer)
  | _, .born prior _, support, .lawSurfaceExtension => .inl (actualDisposition prior support.1 .lawSurfaceExtension)

#print axioms actualEntry
#print axioms actualDisposition

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation
