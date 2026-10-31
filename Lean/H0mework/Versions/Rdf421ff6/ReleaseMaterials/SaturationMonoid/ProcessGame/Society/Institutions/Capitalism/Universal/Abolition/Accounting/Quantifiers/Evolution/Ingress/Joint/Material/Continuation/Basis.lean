import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def baseEntry (support : (base seed claim).Support) : OpenResponsibilityAt (base seed claim) support :=
  ⟨.inl ((Background.family seed).entry support.1.1).1,((Background.family seed).entry support.1.1).2⟩

def entry : (support : (NewN seed claim).Support) → OpenResponsibilityAt (NewN seed claim) support
  | ⟨old,none⟩ => oldEntry (state? := none) (baseEntry seed claim old)
  | ⟨old,some state⟩ => debtEntry old state

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis (NewN seed claim) where
  entry := entry seed claim
  disposition := fun support kind => match kind with
    | .supportSettlement => (Runtime.Inquiry.basis seed claim).disposition support.1 .supportSettlement
    | .transfer => .inl ((Runtime.Inquiry.basis seed claim).disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl ((Runtime.Inquiry.basis seed claim).disposition support.1 .lawSurfaceExtension)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
