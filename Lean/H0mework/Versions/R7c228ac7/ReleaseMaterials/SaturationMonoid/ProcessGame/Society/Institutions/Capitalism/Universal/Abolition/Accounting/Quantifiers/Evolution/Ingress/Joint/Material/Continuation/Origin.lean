import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Basis

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Origin

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
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)

def row := Runtime.Inquiry.entry seed claim (sourceSupport seed claim visit)

inductive Projection
  | query | compilation

def component : SourceNativeProjectionLaw (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .query => PUnit
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := (Runtime.Inquiry.basis seed claim).U7) (calculus := (Runtime.Inquiry.basis seed claim).calculus)
      (oldTheory := (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.source.lawSurface)
      (row seed claim visit) PUnit.unit (ULift.up.{1,0} occurrence) .answered (Responsibility.Family.State seed.claim)
  project := fun projection {_} _ _ => match projection with
    | .query => PUnit.unit
    | .compilation => .canonical (familyState seed claim (Runtime.sharedAt seed claim visit.current))

def root := (Runtime.Inquiry.root seed claim).withProjectionCoface (component seed claim visit)

def authority (source : SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
    visit (row seed claim visit)) := source.withProjectionCoface (component seed claim visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Origin
