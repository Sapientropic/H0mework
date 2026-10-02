import H0mework.Versions.R2.Physics.Revision.CartanAction
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! Fixed inquiry programs consume the primitive slots of the old physical
source and the new material source. The action program is selected at the
exact first-assembly visit; all ordinary reads retain their native next. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext

noncomputable section

def oldConfigurationFace (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    SourceNativeRootSemanticFaceAt livingRoot visit where
  projection := .configuration
  active := PUnit.unit
  classifier_eq := rfl

def oldConfigurationConsumer (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} (livingRoot.emitted visit.current))
      (rootLedgerEntry visit.current) (oldConfigurationFace visit) where
  projection := .inquiryConsumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def oldReadProgram (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    SourceNativeInquiryCompilationProgramAt livingRoot visit rootU7
      InquirySource.calculus (TheoryState.rootSemantic OldN) PUnit.unit
      (ULift.up.{1, 0} (livingRoot.emitted visit.current))
      (rootLedgerEntry visit.current) (rootCausalEntryAuthorityAt visit) where
  compile := fun _ => .answered (oldConfigurationFace visit) (oldConfigurationConsumer visit)

def oldReadInquiryState (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    RootInquiryStateAt OldN V where
  root := livingRoot
  visit := visit
  U7 := rootU7
  calculus := InquirySource.calculus
  Query := PUnit
  entryAt := fun _ => rootLedgerEntry visit.current
  authorityAt := fun _ => rootCausalEntryAuthorityAt visit
  compilationProgramAt := fun query => by cases query; exact oldReadProgram visit
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.inquiryCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def cartanActionInquiryProgram :
    SourceNativeInquiryCompilationProgramAt livingRoot afterGravityTemporalVisit rootU7
      InquirySource.calculus (TheoryState.rootSemantic OldN) PUnit.unit
      (ULift.up.{1, 0} (livingRoot.emitted afterGravityTemporalVisit.current))
      (rootLedgerEntry firstAssemblyCurrent) afterGravityCausalEntryAuthority where
  compile := fun occurrence => .actualAction (firstAssemblyActionProgram.generate occurrence)

def cartanActionInquiryState : RootInquiryStateAt OldN V where
  root := livingRoot
  visit := afterGravityTemporalVisit
  U7 := rootU7
  calculus := InquirySource.calculus
  Query := PUnit
  entryAt := fun _ => rootLedgerEntry firstAssemblyCurrent
  authorityAt := fun _ => afterGravityCausalEntryAuthority
  compilationProgramAt := fun query => by cases query; exact cartanActionInquiryProgram
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.cartanAction, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def materialVisit : Nat → SourceNativeTemporalVisitAt
    materialLivingRoot.toAuthoritativeRoot.toLedgerRoot
  | 0 => materialInitialVisit
  | n + 1 => (materialVisit n).next rfl

def materialAuthorityAt : (n : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt materialLivingRoot (materialVisit n)
      (materialEntry (materialCurrentSupport (materialVisit n).current))
  | 0 => .generatedFromInitialRow materialLivingRoot materialInitialEntry materialInitialEntryRow
  | n + 1 => (materialAuthorityAt n).next rfl

def materialConfigurationFace (n : Nat) :
    SourceNativeRootSemanticFaceAt materialLivingRoot (materialVisit n) where
  projection := .configuration
  active := PUnit.unit
  classifier_eq := rfl

def materialConfigurationConsumer (n : Nat) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} (materialLivingRoot.emitted (materialVisit n).current))
      (materialEntry (materialCurrentSupport (materialVisit n).current))
      (materialConfigurationFace n) where
  projection := .inquiryConsumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def materialReadProgram (n : Nat) :
    SourceNativeInquiryCompilationProgramAt materialLivingRoot (materialVisit n)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
      (ULift.up.{1, 0} (materialLivingRoot.emitted (materialVisit n).current))
      (materialEntry (materialCurrentSupport (materialVisit n).current))
      (materialAuthorityAt n) where
  compile := fun _ => .answered (materialConfigurationFace n) (materialConfigurationConsumer n)

def materialReadInquiryState (n : Nat) : RootInquiryStateAt MaterialN MaterialV where
  root := materialLivingRoot
  visit := materialVisit n
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => materialEntry (materialCurrentSupport (materialVisit n).current)
  authorityAt := fun _ => materialAuthorityAt n
  compilationProgramAt := fun query => by cases query; exact materialReadProgram n
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.inquiryCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision
