import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Target

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

def compilation : SourceNativeInquiryCompilationProgramAt (Origin.root seed grossClaim) seed.current.visit
    seed.current.basis.U7 seed.current.basis.calculus
    (Origin.root seed grossClaim).toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((Origin.root seed grossClaim).emitted seed.current.visit.current))
    seed.current.row (Origin.authority seed grossClaim) where
  compile := fun _ => .actualAction (generated seed grossClaim)

def state : RootInquiryStateAt (OldN seed) seed.current.V where
  root := Origin.root seed grossClaim
  visit := seed.current.visit
  U7 := seed.current.basis.U7
  calculus := seed.current.basis.calculus
  Query := PUnit
  entryAt := fun _ => seed.current.row
  authorityAt := fun _ => Origin.authority seed grossClaim
  compilationProgramAt := fun query => by cases query; exact compilation seed grossClaim
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Origin.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation := ⟨_,_,RootInquiryEngineStateAt.create (state seed grossClaim)⟩

def nextVisit := (generated seed grossClaim).target.targetVisit
def nextRow := (generated seed grossClaim).target.targetEntry
def nextAuthority := (generated seed grossClaim).target.targetAuthority

theorem the_original_root_actually_consumes_the_joint_representation :
    (state seed grossClaim).compileInquiry PUnit.unit = .actualAction (generated seed grossClaim) := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation seed grossClaim) PUnit.unit (generated seed grossClaim) rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation seed grossClaim) PUnit.unit (generated seed grossClaim) rfl

theorem the_actual_process_resumes_at_the_same_joint_root :
    (RootInquiryProcessNode.answered (presentation seed grossClaim) PUnit.unit).erase =
      (⟨NewN seed grossClaim,⟨V seed grossClaim,(root seed grossClaim).toAuthoritativeRoot,nextVisit seed grossClaim⟩⟩ :
        AnyAuthoritativeRootCurrent) := by
  change (⟨NewN seed grossClaim,(generated seed grossClaim).target.targetAnswerAndNext.nextCurrent⟩ :
    AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun next => (⟨NewN seed grossClaim,next⟩ : AnyAuthoritativeRootCurrent))
    (generated seed grossClaim).target.targetAnswerAndNext_next_eq

theorem the_actual_next_is_the_common_current_with_all_original_finance_rows :
    (root seed grossClaim).toAuthoritativeRoot.toRoot.supportAt (nextVisit seed grossClaim).current =
      enteredSupport seed grossClaim :=
  congrArg (stageSupport seed grossClaim)
    (Abolition.Accounting.Root.Compiler.successor_current (flow seed grossClaim) Stage.pending)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
