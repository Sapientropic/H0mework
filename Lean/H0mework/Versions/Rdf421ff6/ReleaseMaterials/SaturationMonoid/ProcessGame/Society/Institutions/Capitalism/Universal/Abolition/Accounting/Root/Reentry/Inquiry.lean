import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry

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
  (frame : Frame (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

inductive Report
  | state | input | verdict | needs

def currentState : Bool → Responsibility.Family.State claim
  | false => Frame.state claim frame
  | true => Frame.updated claim frame word

def report : SourceNativeProjectionLaw (root claim frame word).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Report
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .state => Responsibility.Family.State claim
    | .input => RawEvent Party Good Port Technology Instrument
    | .verdict => Responsibility.Family.MaterialVerdict claim (Frame.state claim frame) frame.actualLaw word
    | .needs => Responsibility.Family.NeedDisposition frame.actualLaw (Frame.state claim frame).raw
        (Responsibility.Family.State.attempt claim (Frame.state claim frame) frame.actualLaw word).actualWord frame.members
  project := fun projection {phase} _ _ => match projection with
    | .state => currentState claim frame word phase
    | .input => word
    | .verdict => Responsibility.Family.adjudicate claim (Frame.state claim frame) frame.actualLaw word
    | .needs => Responsibility.Family.inspectActualNeeds claim (Frame.state claim frame) frame.actualLaw word frame.members

def inquiryRoot := (root claim frame word).withProjectionCoface (report claim frame word)

def inquiryOldProjection (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (inquiryRoot claim frame word).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (oldProjection claim frame word projection)

theorem inquiry_old_outcome (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((inquiryRoot claim frame word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (inquiryOldProjection claim frame word projection) ((inquiryRoot claim frame word).emitted false))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted frame.visit.current)) := by
  dsimp only [inquiryRoot,root,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,inquiryOldProjection,oldProjection,previousInquiry]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted frame.visit.current) <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry
