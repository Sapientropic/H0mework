import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Flow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation
import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Inspection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Needs

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (word : RawEvent Party Good Port Technology Instrument)

local notation "oldRoot" => Source.root input frame visit claim word

def entry : (support : (Source.N input frame claim).Support) → OpenResponsibilityAt (Source.N input frame claim) support
  | ⟨old,none⟩ => oldEntry (state? := none) (frame.entrySupport old)
  | ⟨old,some state⟩ => debtEntry old state

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis (Source.N input frame claim) where
  entry := entry input frame claim
  disposition := by
    intro support kind
    cases kind with
    | supportSettlement => exact frame.disposition support.1 .supportSettlement
    | transfer => exact .inl (frame.disposition support.1 .transfer)
    | lawSurfaceExtension => exact .inl (frame.disposition support.1 .lawSurfaceExtension)

inductive Projection
  | answer | input | assessment | verdict | needs | consumer | compilation

def component : SourceNativeProjectionLaw (oldRoot).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {phase} occurrence _ => match projection with
    | .answer => Responsibility.Family.State claim
    | .input => RawEvent Party Good Port Technology Instrument
    | .assessment => Responsibility.Family.Claim mechanism past nature response
    | .verdict => Responsibility.Family.MaterialVerdict claim (Source.declared input frame visit claim)
        (Source.actualLaw input) word
    | .needs => Responsibility.Family.NeedDisposition (Source.actualLaw input)
        (Source.declared input frame visit claim).raw
        (Responsibility.Family.State.attempt claim (Source.declared input frame visit claim)
          (Source.actualLaw input) word).actualWord
        (Financial.Installation.observe input (frame.cursor visit.current)).members
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{1,0} occurrence)
        (entry input frame claim occurrence.1) (Source.debtState input frame visit claim word phase)
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (U7 := (basis input frame claim).U7) (calculus := (basis input frame claim).calculus)
        (oldTheory := (oldRoot).toAuthoritativeRoot.source.lawSurface)
        (entry input frame claim occurrence.1) PUnit.unit (ULift.up.{1,0} occurrence) .answered
        (Responsibility.Family.State claim)
  project := fun projection {phase} _ _ => match projection with
    | .answer => Source.debtState input frame visit claim word phase
    | .input => word
    | .assessment => claim
    | .verdict => Responsibility.Family.adjudicate claim (Source.declared input frame visit claim)
        (Source.actualLaw input) word
    | .needs => Responsibility.Family.inspectActualNeeds claim (Source.declared input frame visit claim)
        (Source.actualLaw input) word (Financial.Installation.observe input (frame.cursor visit.current)).members
    | .consumer => .canonical
    | .compilation => .canonical (Source.debtState input frame visit claim word phase)

def root := (oldRoot).withProjectionCoface (component input frame visit claim word)

def installation := SourceNativeProjectionLaw.InstallationAt.componentCoface (oldRoot).source.base
  (component input frame visit claim word)

def oldProjection (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (root input frame visit claim word).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (Source.oldProjection input frame visit claim word projection)

theorem oldProjection_injective : Function.Injective (oldProjection input frame visit claim word) := by
  intro left right same
  apply Source.oldProjection_injective input frame visit claim word
  injection same

theorem oldOutcome (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((root input frame visit claim word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection input frame visit claim word projection) ((root input frame visit claim word).emitted .pending))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted visit.current)) := by
  dsimp only [root,Source.root,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,oldProjection,Source.oldProjection,Source.previousInquiry]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted visit.current) <;> rfl

variable (currentVisit : SourceNativeTemporalVisitAt (root input frame visit claim word).toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (root input frame visit claim word) currentVisit
    (entry input frame claim (Source.support input frame visit claim word currentVisit.current)))

def answerFace : SourceNativeRootSemanticFaceAt (root input frame visit claim word) currentVisit where
  projection := (installation input frame visit claim word).embed .answer
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{1,0} ((root input frame visit claim word).emitted currentVisit.current))
    (entry input frame claim (Source.support input frame visit claim word currentVisit.current))
    (answerFace input frame visit claim word currentVisit) where
  projection := (installation input frame visit claim word).embed .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def program : SourceNativeInquiryCompilationProgramAt (root input frame visit claim word) currentVisit
    (basis input frame claim).U7 (basis input frame claim).calculus
    (root input frame visit claim word).toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((root input frame visit claim word).emitted currentVisit.current))
    (entry input frame claim (Source.support input frame visit claim word currentVisit.current)) authority where
  compile := fun _ => .answered (answerFace input frame visit claim word currentVisit)
    (consumer input frame visit claim word currentVisit)

def state : RootInquiryStateAt (Source.N input frame claim) (Source.V input frame visit claim word) where
  root := root input frame visit claim word
  visit := currentVisit
  U7 := (basis input frame claim).U7
  calculus := (basis input frame claim).calculus
  Query := PUnit
  entryAt := fun _ => entry input frame claim (Source.support input frame visit claim word currentVisit.current)
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => by cases query; exact program input frame visit claim word currentVisit authority
  compilationFaceAt := fun query => by
    cases query
    exact { projection := (installation input frame visit claim word).embed .compilation
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state input frame visit claim word currentVisit authority)⟩

#print axioms state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry
