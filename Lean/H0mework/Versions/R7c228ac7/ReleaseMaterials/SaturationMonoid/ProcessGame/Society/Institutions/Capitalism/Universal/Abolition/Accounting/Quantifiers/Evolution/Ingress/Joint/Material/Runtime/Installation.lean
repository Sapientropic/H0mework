import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Target

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

def compilation : SourceNativeInquiryCompilationProgramAt (Origin.root seed claim) (Admission.nextVisit seed claim)
    (Admission.basis seed claim).U7 (Admission.basis seed claim).calculus
    (Origin.root seed claim).toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((Origin.root seed claim).emitted (Admission.nextVisit seed claim).current))
    (Admission.nextRow seed claim) (Origin.authority seed claim) where
  compile := fun _ => .actualAction (generated seed claim)

def state : RootInquiryStateAt (Admission.N seed claim) (Admission.V seed claim) where
  root := Origin.root seed claim
  visit := Admission.nextVisit seed claim
  U7 := (Admission.basis seed claim).U7
  calculus := (Admission.basis seed claim).calculus
  Query := PUnit
  entryAt := fun _ => Admission.nextRow seed claim
  authorityAt := fun _ => Origin.authority seed claim
  compilationProgramAt := fun query => by cases query; exact compilation seed claim
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Origin.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation := ⟨_,_,RootInquiryEngineStateAt.create (state seed claim)⟩
def nextVisit := (generated seed claim).target.targetVisit
def nextRow := (generated seed claim).target.targetEntry
def nextAuthority := (generated seed claim).target.targetAuthority

theorem the_original_root_actually_executes_the_shared_material_programme :
    (state seed claim).compileInquiry PUnit.unit = .actualAction (generated seed claim) := rfl

theorem the_actual_process_resumes_at_its_joint_material_root :
    (RootInquiryProcessNode.answered (presentation seed claim) PUnit.unit).erase =
      (⟨Admission.N seed claim,⟨V seed claim,(Inquiry.root seed claim).toAuthoritativeRoot,nextVisit seed claim⟩⟩ :
        AnyAuthoritativeRootCurrent) := by
  change (⟨Admission.N seed claim,(generated seed claim).target.targetAnswerAndNext.nextCurrent⟩ :
    AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun next => (⟨Admission.N seed claim,next⟩ : AnyAuthoritativeRootCurrent))
    (generated seed claim).target.targetAnswerAndNext_next_eq

theorem the_actual_next_has_the_source_executed_shared_state :
    (Inquiry.root seed claim).toAuthoritativeRoot.toRoot.supportAt (nextVisit seed claim).current =
      support seed claim (next seed claim (initial seed)) :=
  congrArg (support seed claim)
    (Abolition.Accounting.Root.Compiler.successor_current (flow seed claim) (initial seed))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
