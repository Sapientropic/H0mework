import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

def enact := generated (Source.native current)

def next := nextBasic (Source.native current)

def compilation : SourceNativeInquiryCompilationProgramAt (Source.native current).root current.visit
    current.basis.U7 current.basis.calculus (Source.native current).root.toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((Source.native current).root.emitted current.visit.current))
    current.row (Source.native current).authority where
  compile := fun _ => .actualAction (enact current)

def state : RootInquiryStateAt N current.V where
  root := (Source.native current).root
  visit := current.visit
  U7 := current.basis.U7
  calculus := current.basis.calculus
  Query := PUnit
  entryAt := fun _ => current.row
  authorityAt := fun _ => (Source.native current).authority
  compilationProgramAt := fun query => by cases query; exact compilation current
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Source.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation := ⟨_,_,RootInquiryEngineStateAt.create (state current)⟩

theorem the_source_installs_its_actual_public_context_action :
    (state current).compileInquiry PUnit.unit = .actualAction (enact current) := rfl

theorem the_actual_answer_is_the_source_preparation_face :
    (enact current).target.answer = Source.readAnswer current := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq (presentation current) PUnit.unit (enact current) rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq (presentation current) PUnit.unit (enact current) rfl

theorem the_actual_process_resumes_at_its_public_current :
    (RootInquiryProcessNode.answered (presentation current) PUnit.unit).erase = Context.erase (next current) := by
  change (⟨N,(enact current).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = _
  exact nextBasic_is_the_actual_canonical_root_next (Source.native current)

theorem next_reads_the_new_active_interpreter : Context.readLaw (next current) = law current :=
  nextBasic_reads_the_enacted_public_law (Source.native current)

theorem next_retains_the_actual_source_raw : Context.readRaw (next current) = Context.readRaw current :=
  nextBasic_retains_the_original_actual_raw (Source.native current)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
