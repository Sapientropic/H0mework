import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Visits

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

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
  (visit : SourceNativeTemporalVisitAt (Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Inquiry.root seed claim) visit
    (Inquiry.entry seed claim (support seed claim visit.current)))

def answerFace : SourceNativeRootSemanticFaceAt (Inquiry.root seed claim) visit :=
  { projection := .component Inquiry.Projection.answer,active := PUnit.unit,classifier_eq := rfl }

def consumer : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{1,0} ((Inquiry.root seed claim).emitted visit.current))
    (Inquiry.entry seed claim (support seed claim visit.current)) (answerFace seed claim visit) :=
  { projection := .component Inquiry.Projection.consumer,active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }

def answerProgram : SourceNativeInquiryCompilationProgramAt (Inquiry.root seed claim) visit
    (Inquiry.basis seed claim).U7 (Inquiry.basis seed claim).calculus
    (Inquiry.root seed claim).toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((Inquiry.root seed claim).emitted visit.current))
    (Inquiry.entry seed claim (support seed claim visit.current)) authority where
  compile := fun _ => .answered (answerFace seed claim visit) (consumer seed claim visit)

def answerState : RootInquiryStateAt (Admission.N seed claim) (V seed claim) where
  root := Inquiry.root seed claim
  visit := visit
  U7 := (Inquiry.basis seed claim).U7
  calculus := (Inquiry.basis seed claim).calculus
  Query := PUnit
  entryAt := fun _ => Inquiry.entry seed claim (support seed claim visit.current)
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => by cases query; exact answerProgram seed claim visit authority
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Inquiry.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def answerPresentation (n : Nat) : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (answerState seed claim (temporalAt seed claim n) (authorityAt seed claim n))⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
