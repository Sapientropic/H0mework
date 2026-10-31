import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Frame.Ordinary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Component
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  {visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot}
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

abbrev family := frame.family.after atCurrent.actual.account atCurrent.actual.native
abbrev selectedStart := atCurrent.selectedCursor reader

def ordinary : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast (selectedStart frame atCurrent reader) :=
  Public.Frame.ordinary input depth count prefixLimit renewalLimit oldPast (selectedStart frame atCurrent reader) (family frame atCurrent)

def history := Ingress.Joint.QueryHistory.freeze frame.root.source.base.projectionLaw (frame.root.emitted visit.current)
  (ordinary frame atCurrent reader).root.toAuthoritativeRoot.toLedgerRoot.source

def bareFrame := (ordinary frame atCurrent reader).withProjectionCoface (history frame atCurrent reader)

abbrev bodyInitial := Public.Accounting.initial input depth count atCurrent.actual.account
abbrev bodyNext := Public.Accounting.bodyTarget input depth count atCurrent.actual.account

theorem initial_support_is_the_actual_current :
    (bareFrame frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent) = frame.sourceSupport visit.current :=
  (frame.support_exact visit.current atCurrent.actual atCurrent.aligned).symm

theorem the_new_body_keeps_the_original_native_account :
    (bodyNext frame atCurrent).account = atCurrent.actual.account ∧
      (bodyNext frame atCurrent).position = 0 ∧ (bodyNext frame atCurrent).bodyPaid = true := ⟨rfl,rfl,rfl⟩

theorem the_new_body_is_the_current_readers_actual_public_result :
    Public.Accounting.physical input depth count prefixLimit renewalLimit oldPast
        (selectedStart frame atCurrent reader) (bodyNext frame atCurrent) =
      (Public.Scope.actualResult input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader)).next :=
  Physical.Public.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader)

theorem every_old_query_keeps_its_original_outcome {current : (ordinary frame atCurrent reader).V.Current}
    (occurrence : (ordinary frame atCurrent reader).root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current)
    (projection : frame.root.source.base.projectionLaw.Projection) :
    HEq ((history frame atCurrent reader).outcomeAt projection occurrence)
      (frame.root.source.base.projectionLaw.outcomeAt projection (frame.root.emitted visit.current)) :=
  Ingress.Joint.QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome _ _ _ occurrence projection

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
