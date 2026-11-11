import H0mework.Checks.Runtime.Inquiry

/-!
# Regression: raw one-shot inquiry models do not acquire named runtime authority

The same lower root, temporal visit, query, failure frontier and completed U8
core may be presented by another raw compilation program.  That model remains
useful for comparison, but its raw `Engine.ask` occurrence cannot be replayed
as the authority occurrence or coface-realization resumption of the already fixed
named runtime.

The regression also records the positive rigidity boundary: repeating the
fixed failure frontier regenerates the same initial coface.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace InquiryOneShotAuthorityRegression

open RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open RootInquiryU8CompletionRegression
open CanonicalInquiryRuntimeRegression

/-- A separately declared raw program over the literal same old-root problem.
Its output deliberately reuses the same completed core; the only difference is
the program identity. -/
def rawSiblingProgram : SourceNativeInquiryCompilationProgramAt
    root visit U7 theoryAuditCalculus oldTheory () inquiryEvent entry authority where
  compile := fun _exactOccurrence => inquiryCompilation

/-- Raw sibling model state.  It shares the lower root, visit, query, live row,
failure and coface frontier, but it is not the state installed in the named
runtime. -/
def rawSiblingState : RootInquiryStateAt N V where
  root := root
  visit := visit
  U7 := U7
  calculus := theoryAuditCalculus
  Query := Unit
  entryAt := fun _ => entry
  authorityAt := fun _ => authority
  compilationProgramAt := fun _ => rawSiblingProgram
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := ()
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact theoryAuditRootDispositionCommutes

def rawSiblingEngineState : RootInquiryEngineStateAt N V :=
  RootInquiryEngineStateAt.create rawSiblingState

def rawSiblingPresentation : RootInquiryStatePresentation where
  N := N
  V := V
  state := rawSiblingEngineState

/-- The comparison model is intentionally only a one-shot process. -/
def rawSiblingProcess : SourceNativeInquiryEngineProcess.{0} :=
  rawSiblingPresentation.oneShotProcess

def rawSiblingEngine : Engine rawSiblingProcess :=
  Engine.initial rawSiblingProcess

def rawSiblingActivation :
    Engine.SourceNativeInquiryActivationAt rawSiblingEngine :=
  rawSiblingEngine.uniqueInquiryActivation () (by
    intro candidate
    cases candidate
    rfl)

/-- The raw sibling compiler/model is constructible. -/
def rawSiblingOccurrence :
    Engine.ExactRootInquiryOccurrenceAt rawSiblingEngine
      rawSiblingActivation.query :=
  rawSiblingEngine.ask rawSiblingActivation

/-- The sibling model cannot even install an autonomous named runtime: after
its one answer the query fibre is empty, so no recursive activation law exists. -/
theorem rawSiblingOneShot_hasNoAutonomousRuntime :
    IsEmpty (SourceNativeInquiryRuntime rawSiblingProcess) :=
  oneShot_has_no_autonomous_runtime rawSiblingPresentation

/-- A raw one-shot occurrence cannot be cast into the fixed named runtime's
authority carrier. -/
def rawSiblingCannotBecomeFixedRuntimeAuthority : PUnit := by
  fail_if_success
    exact (rawSiblingOccurrence :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt
        runtime.initialState)
  exact PUnit.unit

/-- Nor is the raw occurrence itself a certification that the fixed named
runtime consumed the repaired core.  That proposition is generated only by
eliminating the fixed runtime's own tick. -/
def rawSiblingCannotBecomeFixedCofaceResumption : PUnit := by
  fail_if_success
    exact (rawSiblingOccurrence :
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        generatedRevisionCore runtime 0)
  exact PUnit.unit

/-- Every generated minimal coface at the fixed rooted frontier is the
canonical one. -/
theorem fixedFrontier_minimalCoface_unique
    (left right : GeneratedMinimalCofaceAt cofaceFrontier.rooted) :
    left = right := by
  cases left
  cases right
  rfl

#print axioms rawSiblingCannotBecomeFixedRuntimeAuthority
#print axioms rawSiblingCannotBecomeFixedCofaceResumption
#print axioms rawSiblingOneShot_hasNoAutonomousRuntime
#print axioms fixedFrontier_minimalCoface_unique

end InquiryOneShotAuthorityRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
