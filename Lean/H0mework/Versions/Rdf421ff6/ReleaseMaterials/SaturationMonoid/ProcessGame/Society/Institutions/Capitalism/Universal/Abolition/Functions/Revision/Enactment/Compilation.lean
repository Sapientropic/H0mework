import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (ready : Trigger.ReadyAt context)

def inquiryProgram : SourceNativeInquiryCompilationProgramAt
    (sourceRoot context) context.visit context.basis.U7 context.basis.calculus
      (sourceRoot context).toAuthoritativeRoot.source.lawSurface (Macro.Raw.QueryAt.raw context.germ)
      (ULift.up.{1, 0} ((sourceRoot context).emitted context.visit.current))
      (sourceEntry context) (sourceAuthority context) where
  compile := fun _ => .actualAction (generated context ready)

private theorem original_raw_token_heq
    (left right : Macro.Raw.GermAt context.native context.data context.reader context.visit.current) (same : left = right) :
    HEq
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := sourceEntry context) (query := Macro.Raw.QueryAt.raw left)
        (event := ULift.up.{1, 0} ((sourceRoot context).emitted context.visit.current))
        (audit := (.answered : SourceNativeInquiryFrontAuditAt context.basis.U7 context.basis.calculus
          (sourceRoot context).toAuthoritativeRoot.source.lawSurface (context.native.sourceSupport context.visit.current)))
        (Macro.Raw.reportAt context.native context.data context.reader left))
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := sourceEntry context) (query := Macro.Raw.QueryAt.raw right)
        (event := ULift.up.{1, 0} ((sourceRoot context).emitted context.visit.current))
        (audit := (.answered : SourceNativeInquiryFrontAuditAt context.basis.U7 context.basis.calculus
          (sourceRoot context).toAuthoritativeRoot.source.lawSurface (context.native.sourceSupport context.visit.current)))
        (Macro.Raw.reportAt context.native context.data context.reader right)) := by
  cases same
  rfl

def installedFace : SourceNativeRootInquiryCompilationFaceCoreAt
    (sourceRoot context) (sourceVisit context) (Macro.Raw.QueryAt.raw context.germ)
      (ULift.up.{1, 0} ((sourceRoot context).emitted context.visit.current))
      (sourceEntry context) (sourceAuthority context) (inquiryProgram context ready).generate.output := by
  let available : Macro.Raw.Available context.native context.data context.visit.current :=
    ⟨context.germ.ready, context.germ.sourceFold, context.germ.complete⟩
  exact {
    projection := (Macro.Raw.installation context.native context.data context.reader context.basis).embed .rawCompilation
    active := ⟨available⟩
    classifier_eq := by
      change Macro.Raw.classify context.native context.data .rawCompilation _ = _
      exact dif_pos available
    project_heq := by
      have same := Macro.Raw.germ_unique context.native context.data context.reader context.visit.current available context.germ
      exact original_raw_token_heq context _ _ same.symm }

#print axioms inquiryProgram
#print axioms installedFace

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment
