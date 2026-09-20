import H0mework.Physics.SpinRuntime.InquiryPrograms

/-! A source-owned query reads all weak candidates at the exact native
occurrence. The answer and its next retain the existing material ledger. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

def weakFace (index : ℕ) :
    SourceNativeRootSemanticFaceAt SpinPair.livingRoot (SpinPair.visit index) where
  projection := .weakActual
  active := PUnit.unit
  classifier_eq := rfl

def weakConsumer (index : ℕ) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} (SpinPair.livingRoot.emitted (SpinPair.visit index).current))
      (materialEntry (SpinPair.support (SpinPair.visit index).current)) (weakFace index) where
  projection := .weakConsumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def weakProgram (index : ℕ) :
    SourceNativeInquiryCompilationProgramAt SpinPair.livingRoot (SpinPair.visit index)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
      (ULift.up.{1, 0} (SpinPair.livingRoot.emitted (SpinPair.visit index).current))
      (materialEntry (SpinPair.support (SpinPair.visit index).current))
      (SpinPair.authorityAt index) where
  compile := fun _ => .answered (weakFace index) (weakConsumer index)

def weakInquiryState (index : ℕ) : RootInquiryStateAt MaterialN SpinPair.V where
  root := SpinPair.livingRoot
  visit := SpinPair.visit index
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => materialEntry (SpinPair.support (SpinPair.visit index).current)
  authorityAt := fun _ => SpinPair.authorityAt index
  compilationProgramAt := fun query => by cases query; exact weakProgram index
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.weakCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def weakPresentation (index : ℕ) : RootInquiryStatePresentation where
  N := MaterialN
  V := SpinPair.V
  state := .create (weakInquiryState (index + 1))

theorem weakPresentation_erase (index : ℕ) :
    (weakPresentation index).erase = (SpinPair.readPresentation index).erase := rfl

end
end SaturationMonoid.PhysicsCore.Stage9CU.Runtime
