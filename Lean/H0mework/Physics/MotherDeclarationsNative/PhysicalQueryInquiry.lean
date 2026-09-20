import H0mework.Physics.MotherDeclarationsNative.PhysicalQueryRoot

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherFamilyOccurrence MotherJointCarrier

noncomputable section

def answerFace (typeLaw actionLaw : Law) (depth : ℕ) (query : Query) :
    SourceNativeRootSemanticFaceAt (livingRoot typeLaw actionLaw) (visitAt typeLaw actionLaw depth) where
  projection := .component ((anchorAt typeLaw actionLaw depth, query), 0)
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw typeLaw actionLaw).classify ((anchorAt typeLaw actionLaw depth, query), 0)
      (anchorAt typeLaw actionLaw depth).2 = _
    exact dif_pos rfl

def answerConsumer (typeLaw actionLaw : Law) (depth : ℕ) (query : Query) :
    SourceNativeInquiryAnswerConsumerAt query
      (ULift.up.{1, 0} (SpinPair.emitted (visitAt typeLaw actionLaw depth).current))
      (entryAt typeLaw actionLaw depth) (answerFace typeLaw actionLaw depth query) where
  projection := .component ((anchorAt typeLaw actionLaw depth, query), 1)
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw typeLaw actionLaw).classify ((anchorAt typeLaw actionLaw depth, query), 1)
      (anchorAt typeLaw actionLaw depth).2 = _
    exact dif_pos rfl
  project_heq := HEq.rfl

def programAt (typeLaw actionLaw : Law) (depth : ℕ) (query : Query) :
    SourceNativeInquiryCompilationProgramAt (livingRoot typeLaw actionLaw) (visitAt typeLaw actionLaw depth)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) query
      (ULift.up.{1, 0} (SpinPair.emitted (visitAt typeLaw actionLaw depth).current))
      (entryAt typeLaw actionLaw depth) (authorityAt typeLaw actionLaw depth) where
  compile := fun _ => .answered (answerFace typeLaw actionLaw depth query) (answerConsumer typeLaw actionLaw depth query)

def inquiryAt (typeLaw actionLaw : Law) (depth : ℕ) : RootInquiryStateAt MaterialN SpinPair.V where
  root := livingRoot typeLaw actionLaw
  visit := visitAt typeLaw actionLaw depth
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := Query
  entryAt := fun _ => entryAt typeLaw actionLaw depth
  authorityAt := fun _ => authorityAt typeLaw actionLaw depth
  compilationProgramAt := programAt typeLaw actionLaw depth
  compilationFaceAt := fun query =>
    { projection := .component ((anchorAt typeLaw actionLaw depth, query), 2)
      active := ⟨rfl⟩
      classifier_eq := by
        change (projectionLaw typeLaw actionLaw).classify ((anchorAt typeLaw actionLaw depth, query), 2)
          (anchorAt typeLaw actionLaw depth).2 = _
        exact dif_pos rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro _ _ _ equality; cases equality

def nativeInquiry (typeLaw actionLaw : Law) (parent : MotherVisit) : RootInquiryStateAt MaterialN SpinPair.V :=
  inquiryAt typeLaw actionLaw (StageEightDiscreteFormation.codeOf parent)

theorem compile_from_source (typeLaw actionLaw : Law) (depth : ℕ) (query : Query) :
    (inquiryAt typeLaw actionLaw depth).compileInquiry query =
      SourceNativeInquiryCompilationAt.answered
        (answerFace typeLaw actionLaw depth query) (answerConsumer typeLaw actionLaw depth query) := rfl

theorem complete_answer (typeLaw actionLaw : Law) (depth : ℕ) (query : Query) :
    HEq ((inquiryAt typeLaw actionLaw depth).compileInquiry query).answerReadout
      (answer typeLaw actionLaw query) := HEq.rfl

theorem whole_physics_compiled : ∃ typeLaw actionLaw : Law, ∀ parent : MotherVisit, ∀ value : Joint,
    ∃ query : Query, HEq ((nativeInquiry typeLaw actionLaw parent).compileInquiry query).answerReadout
      (query, some value, some (ActualFormation.Transition.nativeLift value)) := by
  obtain ⟨typeLaw, actionLaw, formed⟩ := whole_physics_formed
  refine ⟨typeLaw, actionLaw, fun parent value => ?_⟩
  obtain ⟨query, computed⟩ := formed value
  exact ⟨query, (complete_answer typeLaw actionLaw (StageEightDiscreteFormation.codeOf parent) query).trans
    (heq_of_eq computed)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery
