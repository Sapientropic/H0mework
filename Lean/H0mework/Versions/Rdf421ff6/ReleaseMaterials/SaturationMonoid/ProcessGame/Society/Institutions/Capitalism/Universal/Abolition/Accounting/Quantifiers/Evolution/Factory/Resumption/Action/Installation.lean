import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))
  (reader : Macro.Raw.Reader input depth count)

local notation "C" => preparedContext frame visit actual authority
local notation "action" => generated frame visit actual authority reader

def compilation : SourceNativeInquiryCompilationProgramAt (C).root (C).visit
    (C).basis.U7 (C).basis.calculus (C).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
      (ULift.up.{1,0} ((C).root.emitted (C).visit.current)) (C).row (C).authority where
  compile := fun _ => .actualAction action

def state : RootInquiryStateAt frame.N (C).V where
  root := (C).root
  visit := (C).visit
  U7 := (C).basis.U7
  calculus := (C).basis.calculus
  Query := PUnit
  entryAt := fun _ => (C).row
  authorityAt := fun _ => (C).authority
  compilationProgramAt := fun query => by cases query; exact compilation frame visit actual authority reader
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Factory.Public.Source.Projection.compilation
            active := PUnit.unit,classifier_eq := rfl,project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state frame visit actual authority reader)⟩

theorem the_source_installs_its_actual_native_resumption :
    (state frame visit actual authority reader).compileInquiry PUnit.unit = .actualAction action := rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation frame visit actual authority reader) PUnit.unit action rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation frame visit actual authority reader) PUnit.unit action rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action
