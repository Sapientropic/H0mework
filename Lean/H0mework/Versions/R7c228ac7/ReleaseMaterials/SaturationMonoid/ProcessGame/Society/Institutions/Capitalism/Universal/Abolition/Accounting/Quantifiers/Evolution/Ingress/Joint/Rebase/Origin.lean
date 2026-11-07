import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Origin

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

def component : SourceNativeProjectionLaw seed.current.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .query => PUnit
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := seed.current.basis.U7) (calculus := seed.current.basis.calculus)
      (oldTheory := seed.current.root.toAuthoritativeRoot.source.lawSurface)
      seed.current.row PUnit.unit (ULift.up.{1,0} occurrence) .answered (Current seed grossClaim)
  project := fun projection {_} _ _ => match projection with
    | .query => PUnit.unit
    | .compilation => .canonical (Current.initial seed grossClaim)

def root := seed.current.root.withProjectionCoface (component seed grossClaim)
def visit := seed.current.visit
def row := seed.current.row
def authority := seed.current.authority.withProjectionCoface (component seed grossClaim)

def input : SourceNativeRootInquiryInputAt (root seed grossClaim) (visit seed) PUnit where
  projection := .component Projection.query
  active := PUnit.unit
  classifier_eq := rfl
  queryType_eq := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Origin
