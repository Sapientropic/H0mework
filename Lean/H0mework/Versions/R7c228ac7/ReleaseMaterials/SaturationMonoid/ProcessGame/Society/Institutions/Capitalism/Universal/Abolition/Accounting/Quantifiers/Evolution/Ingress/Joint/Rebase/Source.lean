import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Origin
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

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

def previousInquiry : SourceNativeProjectionLaw
    (baseRoot seed grossClaim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := (Origin.root seed grossClaim).source.base.projectionLaw.Projection
  ActiveAt := fun projection {_} _ => (Origin.root seed grossClaim).source.base.projectionLaw.ActiveAt projection
    (seed.current.root.emitted seed.current.visit.current)
  InactiveAt := fun projection {_} _ => (Origin.root seed grossClaim).source.base.projectionLaw.InactiveAt projection
    (seed.current.root.emitted seed.current.visit.current)
  classify := fun projection {_} _ => (Origin.root seed grossClaim).source.base.projectionLaw.classify projection
    (seed.current.root.emitted seed.current.visit.current)
  PayloadAt := fun projection {_} _ active => (Origin.root seed grossClaim).source.base.projectionLaw.PayloadAt projection
    (seed.current.root.emitted seed.current.visit.current) active
  project := fun projection {_} _ active => (Origin.root seed grossClaim).source.base.projectionLaw.project projection
    (seed.current.root.emitted seed.current.visit.current) active

def historicalRoot := (baseRoot seed grossClaim).withProjectionCoface (previousInquiry seed grossClaim)

inductive Projection
  | raw | context | temporalPast | nativeAccount | nativePending

def fields : SourceNativeProjectionLaw
    (historicalRoot seed grossClaim).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .raw => RawCurrent Party Good Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
    | .temporalPast => Sparse.TemporalMemory.View seed.current.root.toAuthoritativeRoot.toLedgerRoot
    | .nativeAccount => (Abolition.Root.Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState
    | .nativePending => type_of% (Background.pending seed)
  project := fun projection {_} _ _ => match projection with
    | .raw => (Current.initial seed grossClaim).raw
    | .context => (seed.current.actualLaw,seed.current.members)
    | .temporalPast => Sparse.TemporalMemory.read seed.current.root.toAuthoritativeRoot.toLedgerRoot seed.current.visit
    | .nativeAccount => Background.nativeAccount seed
    | .nativePending => Background.pending seed

def root := (historicalRoot seed grossClaim).withProjectionCoface (fields seed grossClaim)

def rawFace (visit : SourceNativeTemporalVisitAt (root seed grossClaim).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (root seed grossClaim) visit :=
  { projection := .component Projection.raw,active := PUnit.unit,classifier_eq := rfl }

def contextFace (visit : SourceNativeTemporalVisitAt (root seed grossClaim).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (root seed grossClaim) visit :=
  { projection := .component Projection.context,active := PUnit.unit,classifier_eq := rfl }

theorem the_live_raw_face_reads_the_one_original_current
    (visit : SourceNativeTemporalVisitAt (root seed grossClaim).toAuthoritativeRoot.toLedgerRoot) :
    (rawFace seed grossClaim visit).rootRead = (Current.initial seed grossClaim).raw := rfl

theorem the_live_interpreter_and_roster_are_the_original_source_context
    (visit : SourceNativeTemporalVisitAt (root seed grossClaim).toAuthoritativeRoot.toLedgerRoot) :
    (contextFace seed grossClaim visit).rootRead = (seed.current.actualLaw,seed.current.members) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
