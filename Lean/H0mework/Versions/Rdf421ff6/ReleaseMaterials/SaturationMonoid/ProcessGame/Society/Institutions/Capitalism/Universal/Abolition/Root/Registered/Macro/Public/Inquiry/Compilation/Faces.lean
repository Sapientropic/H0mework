import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Compilation.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (reader : Macro.Raw.Reader input depth count)
  (visit : SourceNativeTemporalVisitAt (installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (installedFrame frame reader).root visit
    ((installedFrame frame reader).entry visit.current))

local notation "full" => installedFrame frame reader

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
      (compileUnit origin admission frame reader visit atCurrent authority) where
  projection := (installation frame reader).embed .compilation
  active := atCurrent
  classifier_eq := the_unique_source_active_is_selected frame .compilation _ atCurrent
  project_heq := by
    rw [compileUnit_audit]
    exact token_heq ((full).entry visit.current) PUnit.unit
      (ULift.up.{1, 0} ((full).root.emitted visit.current)) .answered _ _
      (compileUnit_answer origin admission frame reader visit atCurrent authority).symm

#print axioms compilationFace

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
