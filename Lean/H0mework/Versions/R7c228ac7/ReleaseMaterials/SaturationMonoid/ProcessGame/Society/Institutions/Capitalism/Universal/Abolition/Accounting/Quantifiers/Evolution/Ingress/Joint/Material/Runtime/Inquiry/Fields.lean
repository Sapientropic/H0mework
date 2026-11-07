import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry.Basis
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Reply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def previous := QueryHistory.freeze (Origin.root seed claim).source.base.projectionLaw
  ((Origin.root seed claim).emitted (Admission.nextVisit seed claim).current)
  (baseRoot seed claim).toAuthoritativeRoot.toLedgerRoot.source

def priorRoot := (baseRoot seed claim).withProjectionCoface (previous seed claim)

inductive Projection
  | answer | shared | raw | context | financial | report | boundary | bodyCause | consumer | compilation

def component : SourceNativeProjectionLaw (priorRoot seed claim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .answer => FinancialCurrent seed
    | .shared => Current seed claim
    | .raw => RawCurrent Party Good Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
    | .financial => (Abolition.Root.Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState
    | .report => Planning.Report seed claim (Material.shared seed claim)
    | .boundary => Boundary.Reply seed claim (Material.shared seed claim)
        (Planning.chosen seed claim (Material.shared seed claim))
    | .bodyCause => type_of% ((Abolition.Root.Epoch.Interface.ledgerRoot seed.input seed.depth seed.count
        (Execution.Selected.tag seed claim)).emitted (Execution.Selected.visit seed claim).current)
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{1,0} occurrence)
        (entry seed claim occurrence.1) (next seed claim current)
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (U7 := (basis seed claim).U7) (calculus := (basis seed claim).calculus)
        (oldTheory := (priorRoot seed claim).toAuthoritativeRoot.source.lawSurface)
        (entry seed claim occurrence.1) PUnit.unit (ULift.up.{1,0} occurrence) .answered (FinancialCurrent seed)
  project := fun projection {current} _ _ => match projection with
    | .answer => next seed claim current
    | .shared => sharedAt seed claim current
    | .raw => (sharedAt seed claim current).raw
    | .context => (actualLaw seed,seed.current.members)
    | .financial => current.account
    | .report => Material.report seed claim
    | .boundary => Boundary.reply seed claim (Material.shared seed claim)
        (Planning.chosen seed claim (Material.shared seed claim))
    | .bodyCause => (Abolition.Root.Epoch.Interface.ledgerRoot seed.input seed.depth seed.count
        (Execution.Selected.tag seed claim)).emitted (Execution.Selected.visit seed claim).current
    | .consumer => .canonical
    | .compilation => .canonical (next seed claim current)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry
