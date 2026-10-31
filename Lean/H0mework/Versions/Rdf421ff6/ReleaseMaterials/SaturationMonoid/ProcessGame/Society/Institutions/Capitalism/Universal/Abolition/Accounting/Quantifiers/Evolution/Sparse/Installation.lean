import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "source" => Source.native claim current word
local notation "action" => generated claim current word

def program : SourceNativeInquiryCompilationProgramAt (source).root current.visit
    current.basis.U7 current.basis.calculus (source).root.toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((source).root.emitted current.visit.current)) current.row (source).authority where
  compile := fun _ => .actualAction action

def state : RootInquiryStateAt
    (DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)) current.V where
  root := (source).root
  visit := current.visit
  U7 := current.basis.U7
  calculus := current.basis.calculus
  Query := PUnit
  entryAt := fun _ => current.row
  authorityAt := fun _ => (source).authority
  compilationProgramAt := fun query => by cases query; exact program claim current word
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Source.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state claim current word)⟩

theorem the_source_compiles_its_actual_reply :
    (state claim current word).compileInquiry PUnit.unit = .actualAction action := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation claim current word) PUnit.unit action rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation claim current word) PUnit.unit action rfl

theorem the_source_resumes_at_its_exact_updated_current :
    (RootInquiryProcessNode.answered (presentation claim current word) PUnit.unit).erase =
      Current.erase claim (nextCurrent claim current word) := by
  change (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    (action).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = _
  exact next_is_the_actual_canonical_root_next claim current word

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Installation
