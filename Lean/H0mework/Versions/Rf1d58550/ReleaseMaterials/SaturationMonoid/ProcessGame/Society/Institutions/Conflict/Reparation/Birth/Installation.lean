import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

def compilation :
    SourceNativeInquiryCompilationProgramAt (old claim).root (originalVisit claim)
      (old claim).basis.U7 (old claim).basis.calculus
      (old claim).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
      (ULift.up.{1,0} ((old claim).root.emitted (originalVisit claim).current))
      (originalOwner claim) (originalAuthority claim) where
  compile := fun _ => .debtAdmission (generated claim)

def filingState : RootInquiryStateAt (old claim).N (old claim).V where
  root := (old claim).root
  visit := originalVisit claim
  U7 := (old claim).basis.U7
  calculus := (old claim).basis.calculus
  Query := PUnit
  entryAt := fun _ => originalOwner claim
  authorityAt := fun _ => originalAuthority claim
  compilationProgramAt := fun query => by cases query; exact compilation claim
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component PUnit.unit
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def filingPresentation : RootInquiryStatePresentation :=
  ⟨_, _, RootInquiryEngineStateAt.create (filingState claim)⟩

theorem the_exact_aggression_visit_generates_the_admission :
    (filingState claim).compileInquiry PUnit.unit = .debtAdmission (generated claim) := rfl

theorem the_admission_keeps_the_original_ledger_root :
    (filingState claim).root.toAuthoritativeRoot.toLedgerRoot =
      (baseFrame claim).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem filing_answers_with_the_born_whole_ledger_next :
    (RootInquiryProcessNode.answered (filingPresentation claim) PUnit.unit).erase =
      (⟨N claim, (generated claim).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) :=
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth
