import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)

inductive Projection
  | raw | context

def rawAt {current : frame.V.Current} (actual : Public.Inquiry.ActualAt frame current) :=
  (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast actual.snapshot.past).raw

def membersAt {current : frame.V.Current} (actual : Public.Inquiry.ActualAt frame current) :=
  Epoch.Interface.Actors.PublicCensus.parties input depth count prefixLimit renewalLimit oldPast actual.snapshot

/-- These fields are restrictions of the existing native occurrence factory;
no ledger, physical interpreter or account is reconstructed. -/
def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Public.Inquiry.ActualAt frame _
  InactiveAt := fun _ {_} occurrence => Public.Inquiry.InactiveAt frame .snapshot occurrence
  classify := fun _ {_} occurrence => Public.Inquiry.classify frame .snapshot occurrence
  PayloadAt := fun projection {_} _ _ => match projection with
    | .raw => RawCurrent Party Good Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
  project := fun projection {_} _ actual => match projection with
    | .raw => rawAt frame actual
    | .context => (Physical.Public.interpreter input,membersAt frame actual)

def source := frame.withProjectionCoface (component frame)

variable (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Public.Inquiry.ActualAt frame visit.current)
  (row : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit row)

def context : Factory.Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) frame.N where
  V := frame.V
  root := (source frame).root
  visit := visit
  row := row
  authority := authority.withProjectionCoface (component frame)
  basis := frame.basis
  raw := rawAt frame actual
  rawFace := {
    projection := .component Projection.raw
    active := actual
    classifier_eq := Public.Inquiry.the_unique_source_active_is_selected frame .snapshot _ actual }
  raw_heq := HEq.rfl
  actualLaw := Physical.Public.interpreter input
  members := membersAt frame actual
  contextFace := {
    projection := .component Projection.context
    active := actual
    classifier_eq := Public.Inquiry.the_unique_source_active_is_selected frame .snapshot _ actual }
  context_heq := HEq.rfl

theorem the_live_raw_is_the_existing_native_occurrence :
    Factory.Context.readRaw (context frame visit actual row authority) = rawAt frame actual :=
  Factory.Context.readRaw_eq _

theorem all_source_members_come_from_the_existing_actor_fold :
    Factory.Context.readMembers (context frame visit actual row authority) = membersAt frame actual :=
  Factory.Context.readMembers_eq _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Native
