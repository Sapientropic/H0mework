import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry

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

def entry : (atSupport : (Admission.N seed claim).Support) → OpenResponsibilityAt (Admission.N seed claim) atSupport
  | ⟨old,none⟩ => oldEntry (state? := none) ((Rebase.basis seed claim).entry old)
  | ⟨old,some current⟩ => debtEntry old current

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis (Admission.N seed claim) where
  entry := entry seed claim
  disposition := fun atSupport kind => match kind with
    | .supportSettlement => (Rebase.basis seed claim).disposition atSupport.1 .supportSettlement
    | .transfer => .inl ((Rebase.basis seed claim).disposition atSupport.1 .transfer)
    | .lawSurfaceExtension => .inl ((Rebase.basis seed claim).disposition atSupport.1 .lawSurfaceExtension)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry
