import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.Root

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherFamilyOccurrence

noncomputable section

def answerFace (law : MotherPhysicalLaws.Law) (depth : ℕ) (query : QueryAt law depth) :
    SourceNativeRootSemanticFaceAt (livingRoot law) (visitAt law depth) where
  projection := .inherited (.inherited (.component (⟨anchorAt law depth, query⟩, 0)))
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw law).classify (⟨anchorAt law depth, query⟩, 0) (anchorAt law depth).2 = _
    exact dif_pos rfl

def answerConsumer (law : MotherPhysicalLaws.Law) (depth : ℕ) (query : QueryAt law depth) :
    SourceNativeInquiryAnswerConsumerAt query
      (ULift.up.{1, 0} ((livingRoot law).emitted (visitAt law depth).current))
      (entryAt law depth) (answerFace law depth query) where
  projection := .inherited (.inherited (.component (⟨anchorAt law depth, query⟩, 1)))
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw law).classify (⟨anchorAt law depth, query⟩, 1) (anchorAt law depth).2 = _
    exact dif_pos rfl
  project_heq := HEq.rfl

def programAt (law : MotherPhysicalLaws.Law) (depth : ℕ) (query : QueryAt law depth) :
    SourceNativeInquiryCompilationProgramAt (livingRoot law) (visitAt law depth) u7 calculus
      (TheoryState.rootSemantic N) query
      (ULift.up.{1, 0} ((livingRoot law).emitted (visitAt law depth).current))
      (entryAt law depth) (authorityAt law depth) where
  compile := fun _ => .answered (answerFace law depth query) (answerConsumer law depth query)

/-- Every declaration field is assembled from the generated source and its actual emitted visit. -/
def inquiryAt (law : MotherPhysicalLaws.Law) (depth : ℕ) : RootInquiryStateAt N V where
  root := livingRoot law
  visit := visitAt law depth
  U7 := u7
  calculus := calculus
  Query := QueryAt law depth
  entryAt := fun _ => entryAt law depth
  authorityAt := fun _ => authorityAt law depth
  compilationProgramAt := programAt law depth
  compilationFaceAt := fun query =>
    { projection := .inherited (.inherited (.component (⟨anchorAt law depth, query⟩, 2)))
      active := ⟨rfl⟩
      classifier_eq := by
        change (projectionLaw law).classify (⟨anchorAt law depth, query⟩, 2) (anchorAt law depth).2 = _
        exact dif_pos rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro _ obstruction; nomatch obstruction

def nativeInquiry (law : MotherPhysicalLaws.Law) (parent : MotherVisit) : RootInquiryStateAt N V :=
  inquiryAt law (StageEightDiscreteFormation.codeOf parent)

theorem compile_from_source (law : MotherPhysicalLaws.Law) (depth : ℕ) (query : QueryAt law depth) :
    (inquiryAt law depth).compileInquiry query =
      SourceNativeInquiryCompilationAt.answered (answerFace law depth query) (answerConsumer law depth query) := rfl

theorem complete_answer (law : MotherPhysicalLaws.Law) (depth : ℕ) (query : QueryAt law depth) :
    HEq ((inquiryAt law depth).compileInquiry query).answerReadout
      (answer law ⟨anchorAt law depth, query⟩) := HEq.rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
