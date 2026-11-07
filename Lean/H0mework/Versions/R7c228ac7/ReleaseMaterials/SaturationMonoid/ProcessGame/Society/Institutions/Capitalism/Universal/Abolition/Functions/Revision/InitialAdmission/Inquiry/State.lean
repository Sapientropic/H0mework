import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Inquiry.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (package : Macro.Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit (package.frame.entry visit.current))

def compilationFace (query : Query package visit) : SourceNativeRootInquiryCompilationFaceCoreAt
    package.frame.root visit query (ULift.up.{1, 0} (package.frame.root.emitted visit.current))
      (package.frame.entry visit.current) authority
      ({ compile := fun _ => compilation package visit authority query } : SourceNativeInquiryCompilationProgramAt
        package.frame.root visit package.basis.U7 package.basis.calculus
        package.frame.root.toAuthoritativeRoot.source.lawSurface query
        (ULift.up.{1, 0} (package.frame.root.emitted visit.current))
        (package.frame.entry visit.current) authority).generate.output := by
  change SourceNativeRootInquiryCompilationFaceCoreAt package.frame.root visit query
    (ULift.up.{1, 0} (package.frame.root.emitted visit.current)) (package.frame.entry visit.current) authority
    (compilation package visit authority query)
  cases query with
  | internal work => exact Macro.Inquiry.compilationFace package visit authority (.internal work)
  | raw germ =>
      dsimp only [compilation]
      cases selected : InitialAdmission.select (contextAt package visit authority germ) with
      | admitted admission =>
          let original := Macro.Inquiry.compilationFace package visit authority (.raw germ)
          exact {
            projection := original.projection
            active := original.active
            classifier_eq := original.classifier_eq
            project_heq := original.project_heq }
      | obstructed failed =>
          let original := Macro.Inquiry.compilationFace package visit authority (.raw germ)
          exact {
            projection := original.projection
            active := original.active
            classifier_eq := original.classifier_eq
            project_heq := original.project_heq }

def state : RootInquiryStateAt package.frame.N package.frame.V where
  root := package.frame.root
  visit := visit
  U7 := package.basis.U7
  calculus := package.basis.calculus
  Query := Query package visit
  entryAt := fun _ => package.frame.entry visit.current
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => { compile := fun _ => compilation package visit authority query }
  compilationFaceAt := compilationFace package visit authority
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    change (compilation package visit authority query).audit = _ at audited
    rw [compilation_audit] at audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨package.frame.N, package.frame.V, RootInquiryEngineStateAt.create (state package visit authority)⟩

theorem the_installed_current_is_the_literal_original_root :
    (presentation package visit authority).erase = (Macro.Inquiry.presentation package visit authority).erase := rfl

theorem the_source_selected_enactment_is_the_actual_compiler_image
    (germ : Macro.Raw.GermAt package.source package.sourceData package.reader visit.current)
    (admission : InitialAdmissionAt (contextAt package visit authority germ))
    (selected : InitialAdmission.select (contextAt package visit authority germ) = .admitted admission) :
    (state package visit authority).compileInquiry (.raw germ) =
      .actualAction (Enactment.Admitted.generated (contextAt package visit authority germ) admission) := by
  change compilation package visit authority (.raw germ) = _
  simp only [compilation, selected]
  rfl

#print axioms state
#print axioms the_source_selected_enactment_is_the_actual_compiler_image

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Inquiry
