import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Compilation.Source

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

private theorem token_heq {N : WorldRelationNetwork} {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7} {theory : TheoryState N} {support : N.Support}
    (entry : OpenResponsibilityAt N support) {Query : Type} (query : Query) {Event : Type 1} (event : Event)
    (audit : SourceNativeInquiryFrontAuditAt U7 calculus theory support)
    {A B : Type} (left : A) (right : B) (same : HEq left right) :
    HEq (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) left)
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) right) := by
  cases same
  rfl

def compilationFace : SourceNativeRootInquiryCompilationFaceCoreAt (full).root visit PUnit.unit
    (ULift.up.{1, 0} ((full).root.emitted visit.current)) ((full).entry visit.current) authority
      (compileUnit frame reader visit atCurrent authority) where
  projection := (Public.Inquiry.installation frame reader).embed .compilation
  active := atCurrent
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected frame .compilation _ atCurrent
  project_heq := by
    rw [compileUnit_audit]
    exact token_heq ((full).entry visit.current) PUnit.unit
      (ULift.up.{1, 0} ((full).root.emitted visit.current)) .answered _ _
      (compileUnit_answer frame reader visit atCurrent authority).symm

#print axioms compilationFace

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
