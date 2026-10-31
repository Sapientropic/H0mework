import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Origin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
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

inductive Projection
  | query | compilation

def component : SourceNativeProjectionLaw (sourceRoot seed grossClaim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .query => PUnit
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := (Rebase.basis seed grossClaim).U7) (calculus := (Rebase.basis seed grossClaim).calculus)
      (oldTheory := (sourceRoot seed grossClaim).toAuthoritativeRoot.source.lawSurface)
      (sourceRow seed grossClaim) PUnit.unit (ULift.up.{1,0} occurrence) .answered (Current seed grossClaim)
  project := fun projection {_} _ _ => match projection with
    | .query => PUnit.unit
    | .compilation => .canonical (declaredShared seed grossClaim)

def root := (sourceRoot seed grossClaim).withProjectionCoface (component seed grossClaim)
def authority := (sourceAuthority seed grossClaim).withProjectionCoface (component seed grossClaim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Origin
