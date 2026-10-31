import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

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

def compilation : SourceNativeInquiryCompilationProgramAt (Origin.root seed grossClaim)
    (sourceVisit seed grossClaim) (Rebase.basis seed grossClaim).U7 (Rebase.basis seed grossClaim).calculus
    (Origin.root seed grossClaim).toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((Origin.root seed grossClaim).emitted (sourceVisit seed grossClaim).current))
    (sourceRow seed grossClaim) (Origin.authority seed grossClaim) where
  compile := fun _ => .debtAdmission (generated seed grossClaim)

def state : RootInquiryStateAt (oldN seed grossClaim) (Rebase.V seed grossClaim) where
  root := Origin.root seed grossClaim
  visit := sourceVisit seed grossClaim
  U7 := (Rebase.basis seed grossClaim).U7
  calculus := (Rebase.basis seed grossClaim).calculus
  Query := PUnit
  entryAt := fun _ => sourceRow seed grossClaim
  authorityAt := fun _ => Origin.authority seed grossClaim
  compilationProgramAt := fun query => by cases query; exact compilation seed grossClaim
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Origin.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation := ⟨_,_,RootInquiryEngineStateAt.create (state seed grossClaim)⟩

def nextVisit := (generated seed grossClaim).target.targetVisit
def nextRow := (root seed grossClaim).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (generated seed grossClaim).target.firstSuccessor.next_eq (generated seed grossClaim).target.translatedSourceEntry
def nextAuthority := (generated seed grossClaim).target.initialAuthority.next
  (generated seed grossClaim).target.firstSuccessor.next_eq

theorem the_original_root_actually_admits_the_shared_gross_row :
    (state seed grossClaim).compileInquiry PUnit.unit = .debtAdmission (generated seed grossClaim) := rfl

theorem the_actual_process_resumes_at_the_same_joint_root :
    (RootInquiryProcessNode.answered (presentation seed grossClaim) PUnit.unit).erase =
      (⟨N seed grossClaim,⟨V seed grossClaim,(root seed grossClaim).toAuthoritativeRoot,nextVisit seed grossClaim⟩⟩ :
        AnyAuthoritativeRootCurrent) := by
  change (⟨N seed grossClaim,(generated seed grossClaim).target.targetAnswerAndNext.nextCurrent⟩ :
    AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun next => (⟨N seed grossClaim,next⟩ : AnyAuthoritativeRootCurrent))
    (generated seed grossClaim).target.targetAnswerAndNext_next_eq

theorem the_actual_next_has_one_shared_declared_current :
    (root seed grossClaim).toAuthoritativeRoot.toRoot.supportAt (nextVisit seed grossClaim).current =
      support seed grossClaim true :=
  congrArg (support seed grossClaim)
    (Abolition.Accounting.Root.Compiler.successor_current (flow seed grossClaim) false)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
