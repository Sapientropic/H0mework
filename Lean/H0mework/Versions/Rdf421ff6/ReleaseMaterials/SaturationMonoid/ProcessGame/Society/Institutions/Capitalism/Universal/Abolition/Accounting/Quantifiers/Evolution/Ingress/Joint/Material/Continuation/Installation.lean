import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

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
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)
  (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
    visit (Origin.row seed claim visit))

def compilation : SourceNativeInquiryCompilationProgramAt (Origin.root seed claim visit) visit
    (Runtime.Inquiry.basis seed claim).U7 (Runtime.Inquiry.basis seed claim).calculus
    (Origin.root seed claim visit).toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((Origin.root seed claim visit).emitted visit.current))
    (Origin.row seed claim visit) (Origin.authority seed claim visit sourceAuthority) where
  compile := fun _ => .actualAction (generated seed claim visit sourceAuthority)

def state : RootInquiryStateAt (OldN seed claim) (Runtime.V seed claim) where
  root := Origin.root seed claim visit
  visit := visit
  U7 := (Runtime.Inquiry.basis seed claim).U7
  calculus := (Runtime.Inquiry.basis seed claim).calculus
  Query := PUnit
  entryAt := fun _ => Origin.row seed claim visit
  authorityAt := fun _ => Origin.authority seed claim visit sourceAuthority
  compilationProgramAt := fun query => by cases query; exact compilation seed claim visit sourceAuthority
  compilationFaceAt := fun query => by
    cases query
    exact {
      projection := .component Origin.Projection.compilation
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state seed claim visit sourceAuthority)⟩

def nextVisit := (generated seed claim visit sourceAuthority).target.targetVisit

theorem the_actual_root_executes_the_same_row_normalization :
    (state seed claim visit sourceAuthority).compileInquiry PUnit.unit =
      .actualAction (generated seed claim visit sourceAuthority) := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation seed claim visit sourceAuthority) PUnit.unit (generated seed claim visit sourceAuthority) rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation seed claim visit sourceAuthority) PUnit.unit (generated seed claim visit sourceAuthority) rfl

theorem the_actual_process_resumes_at_the_same_normalized_root :
    (RootInquiryProcessNode.answered (presentation seed claim visit sourceAuthority) PUnit.unit).erase =
      (⟨NewN seed claim,⟨V seed claim visit,(root seed claim visit).toAuthoritativeRoot,
        nextVisit seed claim visit sourceAuthority⟩⟩ : AnyAuthoritativeRootCurrent) := by
  change (⟨NewN seed claim,(generated seed claim visit sourceAuthority).target.targetAnswerAndNext.nextCurrent⟩ :
    AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun next => (⟨NewN seed claim,next⟩ : AnyAuthoritativeRootCurrent))
    (generated seed claim visit sourceAuthority).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
