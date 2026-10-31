import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation.Faces

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

local notation "full" => current.native.full

def unitProgram : SourceNativeInquiryCompilationProgramAt (full).root current.native.visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((full).root.emitted current.native.visit.current)) ((full).entry current.native.visit.current) current.native.authority where
  compile := fun _ => compileUnit current

def state : RootInquiryStateAt (full).N (full).V where
  root := (full).root
  visit := current.native.visit
  U7 := (full).basis.U7
  calculus := (full).basis.calculus
  Query := PUnit
  entryAt := fun _ => (full).entry current.native.visit.current
  authorityAt := fun _ => current.native.authority
  compilationProgramAt := fun query => by cases query;exact unitProgram current
  compilationFaceAt := fun query => by cases query;exact compilationFace current
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    cases query
    change (compileUnit current).audit = _ at audited
    rw [compileUnit_audit] at audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨(full).N,(full).V,RootInquiryEngineStateAt.create (state current)⟩

theorem the_installed_programme_is_the_original_source_compiler :
    (state current).compileInquiry PUnit.unit = compileUnit current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation
