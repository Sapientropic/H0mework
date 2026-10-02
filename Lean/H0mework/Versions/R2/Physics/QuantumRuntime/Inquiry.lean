import H0mework.Versions.R2.Physics.SpinRuntime.InquiryPrograms

/-! Source-compiled quantum inquiries read the same complete material occurrence.
The query carries no state, outcome, probability or successor selector. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

def quantumFace (index : ℕ) :
    SourceNativeRootSemanticFaceAt SpinPair.livingRoot (SpinPair.visit index) where
  projection := .quantumField
  active := PUnit.unit
  classifier_eq := rfl

def quantumConsumer (index : ℕ) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} (SpinPair.livingRoot.emitted (SpinPair.visit index).current))
      (materialEntry (SpinPair.support (SpinPair.visit index).current))
      (quantumFace index) where
  projection := .quantumConsumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def quantumProgram (index : ℕ) :
    SourceNativeInquiryCompilationProgramAt SpinPair.livingRoot (SpinPair.visit index)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
      (ULift.up.{1, 0} (SpinPair.livingRoot.emitted (SpinPair.visit index).current))
      (materialEntry (SpinPair.support (SpinPair.visit index).current))
      (SpinPair.authorityAt index) where
  compile := fun _ => .answered (quantumFace index) (quantumConsumer index)

def quantumInquiryState (index : ℕ) : RootInquiryStateAt MaterialN SpinPair.V where
  root := SpinPair.livingRoot
  visit := SpinPair.visit index
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => materialEntry (SpinPair.support (SpinPair.visit index).current)
  authorityAt := fun _ => SpinPair.authorityAt index
  compilationProgramAt := fun query => by cases query; exact quantumProgram index
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.quantumCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def quantumPresentation (index : ℕ) : RootInquiryStatePresentation where
  N := MaterialN
  V := SpinPair.V
  state := .create (quantumInquiryState (index + 1))

theorem quantumPresentation_erase (index : ℕ) :
    (quantumPresentation index).erase = (SpinPair.readPresentation index).erase := rfl

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Runtime
