import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Gate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection.Verdict

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

def renewalDecision := Selection.renewalVerdict claim
  (Abolition.Accounting.Root.Reentry.Frame.state claim (Input.native claim frame proposal))
  (readLaw claim (Input.native claim frame proposal))
  (readMembers claim (Input.native claim frame proposal))
  (Input.readProposal claim frame proposal)

namespace Renewal

def component : SourceNativeProjectionLaw
    (Gate.native claim frame proposal).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => type_of% (Root.renewalDecision claim frame proposal)
  project := fun _ {_} _ _ => Root.renewalDecision claim frame proposal

/-- Permission is a separate source face from execution: a real partial
payment never silently becomes a capital-renewal certificate. -/
def native : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim where
  V := frame.V
  root := (Gate.native claim frame proposal).root.withProjectionCoface (component claim frame proposal)
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := (Gate.native claim frame proposal).authority.withProjectionCoface (component claim frame proposal)
  finite := frame.finite
  occurrence_eq := frame.occurrence_eq
  open_fibres := frame.open_fibres
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := { projection := .inherited (Gate.native claim frame proposal).contextFace.projection
                   active := (Gate.native claim frame proposal).contextFace.active
                   classifier_eq := (Gate.native claim frame proposal).contextFace.classifier_eq }
  context_heq := (Gate.native claim frame proposal).context_heq

end Renewal

namespace Gate

def renewalFace : SourceNativeRootSemanticFaceAt (Renewal.native claim frame proposal).root frame.visit :=
  { projection := .component PUnit.unit,active := PUnit.unit,classifier_eq := rfl }

def readRenewal : type_of% (Root.renewalDecision claim frame proposal) :=
  (renewalFace claim frame proposal).rootRead

theorem readRenewal_eq : readRenewal claim frame proposal = Root.renewalDecision claim frame proposal := rfl

end Gate
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
