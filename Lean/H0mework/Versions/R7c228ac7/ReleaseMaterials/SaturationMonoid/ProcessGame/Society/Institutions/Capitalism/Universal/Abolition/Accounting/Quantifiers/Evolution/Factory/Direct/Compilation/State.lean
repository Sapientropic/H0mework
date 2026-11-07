import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Compilation.Faces

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (reader : Macro.Raw.Reader input depth count)
  (visit : SourceNativeTemporalVisitAt (Public.Inquiry.installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Public.Inquiry.installedFrame frame reader).root visit
    ((Public.Inquiry.installedFrame frame reader).entry visit.current))

local notation "full" => Public.Inquiry.installedFrame frame reader

def unitProgram : SourceNativeInquiryCompilationProgramAt (full).root visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1, 0} ((full).root.emitted visit.current)) ((full).entry visit.current) authority where
  compile := fun _ => compileUnit frame reader visit atCurrent authority

def state : RootInquiryStateAt (full).N (full).V where
  root := (full).root
  visit := visit
  U7 := (full).basis.U7
  calculus := (full).basis.calculus
  Query := PUnit
  entryAt := fun _ => (full).entry visit.current
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => by
    cases query
    exact unitProgram frame reader visit atCurrent authority
  compilationFaceAt := fun query => by
    cases query
    exact compilationFace frame reader visit atCurrent authority
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    cases query
    change (compileUnit frame reader visit atCurrent authority).audit = _ at audited
    rw [compileUnit_audit] at audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨(full).N, (full).V, RootInquiryEngineStateAt.create (state frame reader visit atCurrent authority)⟩

theorem the_query_is_a_unique_seal (query : (presentation frame reader visit atCurrent authority).Query) :
    query = PUnit.unit := by cases query; rfl

theorem the_installed_compiler_is_the_literal_source_selection :
    (state frame reader visit atCurrent authority).compileInquiry PUnit.unit =
      compileUnit frame reader visit atCurrent authority := rfl

#print axioms state
#print axioms the_installed_compiler_is_the_literal_source_selection

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
