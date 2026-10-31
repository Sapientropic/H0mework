import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation.Source

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

private theorem token_heq {N : WorldRelationNetwork} {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7} {theory : TheoryState N} {support : N.Support}
    (entry : OpenResponsibilityAt N support) {Query : Type} (query : Query) {Event : Type 1} (event : Event)
    (audit : SourceNativeInquiryFrontAuditAt U7 calculus theory support)
    {A B : Type} (left : A) (right : B) (same : HEq left right) :
    HEq (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) left)
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) right) := by
  cases same
  rfl

def compilationFace : SourceNativeRootInquiryCompilationFaceCoreAt (full).root current.native.visit PUnit.unit
    (ULift.up.{1, 0} ((full).root.emitted current.native.visit.current)) ((full).entry current.native.visit.current) current.native.authority
      (compileUnit current) where
  projection := (Public.Inquiry.installation current.native.frame current.native.reader).embed .compilation
  active := current.native.actual
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected current.native.frame .compilation _ current.native.actual
  project_heq := by
    rw [compileUnit_audit]
    exact token_heq ((full).entry current.native.visit.current) PUnit.unit
      (ULift.up.{1, 0} ((full).root.emitted current.native.visit.current)) .answered _ _
      (compileUnit_answer current).symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation
