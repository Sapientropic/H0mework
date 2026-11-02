import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Projection.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission)

/-- This reads the existing installed snapshot face. The caller supplies
neither an audit result nor a substitute accounting state. -/
def installedAssessment : Financial.Decision input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot := frame.snapshotRead.fullAccount

theorem the_existing_root_classifies_the_full_account_face_as_active :
    frame.full.root.toAuthoritativeRoot.source.projectionLaw.classify frame.snapshotFace.projection
      (frame.full.root.emitted frame.visit.current) = .inl frame.snapshotFace.active :=
  frame.snapshotFace.classifier_eq

theorem the_root_read_keeps_its_exact_current_window_and_full_native_account :
    frame.snapshotRead.planningWindow = (prefixLimit, renewalLimit) ∧
      frame.snapshotRead.oldPast = origin.germ.snapshot.past ∧
      frame.snapshotRead.physical = frame.snapshot ∧ frame.snapshotRead.account = frame.account ∧
      installedAssessment frame = Financial.assess frame := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem the_installed_root_assessment_generates_strict_full_gain_or_its_original_issue :
    match installedAssessment frame with
    | .accepted _ =>
        (publicCurrent input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).raw.clock =
          (oldEndpoint input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).clock ∧
        (∀ person good, 0 ≤ Financial.delta input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot person good) ∧
        (∃ person good, 0 < Financial.delta input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot person good)
    | .rejected _ => ¬ Financial.Checks input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot :=
  Financial.every_actual_assessment_returns_strict_full_account_gain_or_its_original_issue frame

#print axioms installedAssessment
#print axioms the_existing_root_classifies_the_full_account_face_as_active
#print axioms the_root_read_keeps_its_exact_current_window_and_full_native_account
#print axioms the_installed_root_assessment_generates_strict_full_gain_or_its_original_issue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Root
