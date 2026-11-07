import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Origin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

inductive Projection
  | query | compilation

def component : SourceNativeProjectionLaw (Admission.root seed claim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .query => PUnit
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := (Admission.basis seed claim).U7) (calculus := (Admission.basis seed claim).calculus)
      (oldTheory := (Admission.root seed claim).toAuthoritativeRoot.source.lawSurface)
      (Admission.nextRow seed claim) PUnit.unit (ULift.up.{1,0} occurrence) .answered (FinancialCurrent seed)
  project := fun projection {_} _ _ => match projection with
    | .query => PUnit.unit
    | .compilation => .canonical (next seed claim (initial seed))

def root := (Admission.root seed claim).withProjectionCoface (component seed claim)
def authority := (Admission.nextAuthority seed claim).withProjectionCoface (component seed claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Origin
