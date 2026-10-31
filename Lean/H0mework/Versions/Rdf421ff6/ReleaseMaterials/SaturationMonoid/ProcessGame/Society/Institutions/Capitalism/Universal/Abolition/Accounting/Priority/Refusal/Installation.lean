import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

local notation "current" => Source.native claim frame proposal
local notation "action" => Action.generated claim frame proposal

def program : SourceNativeInquiryCompilationProgramAt (current).root (current).visit
    (current).basis.U7 (current).basis.calculus (current).root.toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((current).root.emitted (current).visit.current)) (current).row (current).authority where
  compile := fun _ => .actualAction action

def state : RootInquiryStateAt
    (DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)) (current).V where
  root := (current).root
  visit := (current).visit
  U7 := (current).basis.U7
  calculus := (current).basis.calculus
  Query := PUnit
  entryAt := fun _ => (current).row
  authorityAt := fun _ => (current).authority
  compilationProgramAt := fun query => by cases query; exact program claim frame proposal
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Source.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state claim frame proposal)⟩

theorem the_named_installer_compiles_the_actual_structured_reply :
    (state claim frame proposal).compileInquiry PUnit.unit = .actualAction action := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation claim frame proposal) PUnit.unit action rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation claim frame proposal) PUnit.unit action rfl

theorem the_reply_and_its_next_are_the_same_actual_root_transition :
    (RootInquiryProcessNode.answered (presentation claim frame proposal) PUnit.unit).erase =
      (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
        ⟨(Action.nextFrame claim frame proposal).V,(Action.nextFrame claim frame proposal).root.toAuthoritativeRoot,
          (Action.nextFrame claim frame proposal).visit⟩⟩ : AnyAuthoritativeRootCurrent) := by
  change (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    (action).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun next =>
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),next⟩ :
      AnyAuthoritativeRootCurrent)) (action).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Installation
