import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

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

def originalSharedFace : SourceNativeRootSemanticFaceAt (Runtime.Inquiry.root seed claim) visit :=
  { projection := .component Runtime.Inquiry.Projection.shared,active := PUnit.unit,classifier_eq := rfl }

def originalContextFace : SourceNativeRootSemanticFaceAt (Runtime.Inquiry.root seed claim) visit :=
  { projection := .component Runtime.Inquiry.Projection.context,active := PUnit.unit,classifier_eq := rfl }

def originalFinancialFace : SourceNativeRootSemanticFaceAt (Runtime.Inquiry.root seed claim) visit :=
  { projection := .component Runtime.Inquiry.Projection.financial,active := PUnit.unit,classifier_eq := rfl }

def originalShared : Current seed claim := (originalSharedFace seed claim visit).rootRead

def originalContext : RawLaw Party Good Port Technology Instrument × List Party :=
  (originalContextFace seed claim visit).rootRead

def originalFinancial := (originalFinancialFace seed claim visit).rootRead

def previous := QueryHistory.freeze (Origin.root seed claim visit).source.base.projectionLaw
  ((Origin.root seed claim visit).emitted visit.current)
  (baseRoot seed claim visit).toAuthoritativeRoot.toLedgerRoot.source

def priorRoot := (baseRoot seed claim visit).withProjectionCoface (previous seed claim visit)

inductive Projection
  | raw | context | native | temporalPast

def fields : SourceNativeProjectionLaw (priorRoot seed claim visit).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .raw => RawCurrent Party Good Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
    | .native => (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState
    | .temporalPast => Sparse.TemporalMemory.View (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot
  project := fun projection {_} _ _ => match projection with
    | .raw => (originalShared seed claim visit).raw
    | .context => originalContext seed claim visit
    | .native => originalFinancial seed claim visit
    | .temporalPast => Sparse.TemporalMemory.read (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot visit

def root := (priorRoot seed claim visit).withProjectionCoface (fields seed claim visit)

def rawFace (atVisit : SourceNativeTemporalVisitAt (root seed claim visit).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (root seed claim visit) atVisit :=
  { projection := .component Projection.raw,active := PUnit.unit,classifier_eq := rfl }

def contextFace (atVisit : SourceNativeTemporalVisitAt (root seed claim visit).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (root seed claim visit) atVisit :=
  { projection := .component Projection.context,active := PUnit.unit,classifier_eq := rfl }

def nativeFace (atVisit : SourceNativeTemporalVisitAt (root seed claim visit).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (root seed claim visit) atVisit :=
  { projection := .component Projection.native,active := PUnit.unit,classifier_eq := rfl }

theorem the_native_face_retains_the_same_entire_actual_financial_account
    (atVisit : SourceNativeTemporalVisitAt (root seed claim visit).toAuthoritativeRoot.toLedgerRoot) :
    (nativeFace seed claim visit atVisit).rootRead = visit.current.account := rfl

theorem the_raw_and_native_faces_are_the_same_actual_source_values
    (atVisit : SourceNativeTemporalVisitAt (root seed claim visit).toAuthoritativeRoot.toLedgerRoot) :
    (rawFace seed claim visit atVisit).rootRead = (Runtime.sharedAt seed claim visit.current).raw ∧
      originalFinancial seed claim visit = visit.current.account := ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
