import H0mework.Physics.SpinRuntime.Action

/-! Native configuration consumers after the spin-pair first write. Every
answer and following current comes from the same source-generated visit. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion

noncomputable section

def visit : Nat → SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot
  | 0 => initialVisit
  | n + 1 => (visit n).next rfl

def authorityAt : (n : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot (visit n)
      (materialEntry (support (visit n).current))
  | 0 => .generatedFromInitialRow livingRoot sourceEntry initialEntryRow
  | n + 1 => (authorityAt n).next rfl

def configurationFace (n : Nat) : SourceNativeRootSemanticFaceAt livingRoot (visit n) where
  projection := .inherited .configuration
  active := PUnit.unit
  classifier_eq := rfl

def configurationConsumer (n : Nat) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} (livingRoot.emitted (visit n).current))
      (materialEntry (support (visit n).current)) (configurationFace n) where
  projection := .inherited .inquiryConsumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def readProgram (n : Nat) :
    SourceNativeInquiryCompilationProgramAt livingRoot (visit n)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
      (ULift.up.{1, 0} (livingRoot.emitted (visit n).current))
      (materialEntry (support (visit n).current)) (authorityAt n) where
  compile := fun _ => .answered (configurationFace n) (configurationConsumer n)

def readInquiryState (n : Nat) : RootInquiryStateAt MaterialN V where
  root := livingRoot
  visit := visit n
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => materialEntry (support (visit n).current)
  authorityAt := fun _ => authorityAt n
  compilationProgramAt := fun query => by cases query; exact readProgram n
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.inherited .inquiryCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def readPresentation (n : Nat) : RootInquiryStatePresentation where
  N := MaterialN
  V := V
  state := .create (readInquiryState (n + 1))

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair
