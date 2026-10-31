import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Input

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

inductive Projection
  | proposal | context

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .proposal => RawEvent Party Good Port Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
  project := fun projection {_} _ _ => match projection with
    | .proposal => proposal
    | .context => Root.readContext claim frame

/-- Installing a proposal retains the actual row, authority and every old
source projection; the context is a read of that source's existing face. -/
def native : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim where
  V := frame.V
  root := frame.root.withProjectionCoface (component claim frame proposal)
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := frame.authority.withProjectionCoface (component claim frame proposal)
  finite := frame.finite
  occurrence_eq := frame.occurrence_eq
  open_fibres := frame.open_fibres
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := { projection := .component Projection.context
                   active := PUnit.unit
                   classifier_eq := rfl }
  context_heq := heq_of_eq (Root.readContext_eq claim frame)

def proposalFace : SourceNativeRootSemanticFaceAt (native claim frame proposal).root frame.visit :=
  { projection := .component Projection.proposal,active := PUnit.unit,classifier_eq := rfl }

def readProposal : RawEvent Party Good Port Technology Instrument :=
  (proposalFace claim frame proposal).rootRead

theorem readProposal_eq : readProposal claim frame proposal = proposal := rfl

theorem old_state_is_literal :
    Abolition.Accounting.Root.Reentry.Frame.state claim (native claim frame proposal) =
      Abolition.Accounting.Root.Reentry.Frame.state claim frame := rfl

theorem context_read_is_the_original_source_context :
    Root.readContext claim (native claim frame proposal) = (frame.actualLaw,frame.members) :=
  Root.readContext_eq claim (native claim frame proposal)

theorem all_old_projections_remain_active_or_inactive_as_before
    (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((native claim frame proposal).root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (.inherited projection) ((native claim frame proposal).root.emitted frame.visit.current))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection
        (frame.root.emitted frame.visit.current)) := by
  dsimp only [native,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted frame.visit.current) <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Input
