import H0mework.Physics.MotherProgrammesFormation.Declarations.SubquotientInquiry.Root

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherFamilyOccurrence

noncomputable section

def answerFace (ready : Ready) (depth : ℕ) (query : Query ready.val) :
    SourceNativeRootSemanticFaceAt (livingRoot ready) (visitAt ready depth) where
  projection := .component ((anchorAt ready depth, query), 0)
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw ready).classify ((anchorAt ready depth, query), 0)
      (anchorAt ready depth).2 = _
    exact dif_pos rfl

def answerConsumer (ready : Ready) (depth : ℕ) (query : Query ready.val) :
    SourceNativeInquiryAnswerConsumerAt query
      (ULift.up.{1, 0} (SpinPair.emitted (visitAt ready depth).current))
      (entryAt ready depth) (answerFace ready depth query) where
  projection := .component ((anchorAt ready depth, query), 1)
  active := ⟨rfl⟩
  classifier_eq := by
    change (projectionLaw ready).classify ((anchorAt ready depth, query), 1)
      (anchorAt ready depth).2 = _
    exact dif_pos rfl
  project_heq := HEq.rfl

def programAt (ready : Ready) (depth : ℕ) (query : Query ready.val) :
    SourceNativeInquiryCompilationProgramAt (livingRoot ready) (visitAt ready depth)
      materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) query
      (ULift.up.{1, 0} (SpinPair.emitted (visitAt ready depth).current))
      (entryAt ready depth) (authorityAt ready depth) where
  compile := fun _ => .answered (answerFace ready depth query) (answerConsumer ready depth query)

def inquiryAt (ready : Ready) (depth : ℕ) : RootInquiryStateAt MaterialN SpinPair.V where
  root := livingRoot ready
  visit := visitAt ready depth
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := Query ready.val
  entryAt := fun _ => entryAt ready depth
  authorityAt := fun _ => authorityAt ready depth
  compilationProgramAt := programAt ready depth
  compilationFaceAt := fun query =>
    { projection := .component ((anchorAt ready depth, query), 2)
      active := ⟨rfl⟩
      classifier_eq := by
        change (projectionLaw ready).classify ((anchorAt ready depth, query), 2)
          (anchorAt ready depth).2 = _
        exact dif_pos rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro _ _ _ equality; cases equality

def formInquiry (input : Input) (depth : ℕ) : Option (RootInquiryStateAt MaterialN SpinPair.V) :=
  (prepare input).map (fun ready => inquiryAt ready depth)

theorem formInquiry_recovers (ready : Ready) (depth : ℕ) :
    formInquiry ready.val depth = some (inquiryAt ready depth) := by
  unfold formInquiry
  rw [prepare_recovers]
  rfl

theorem formInquiry_rejects (input : Input) (depth : ℕ) (incompatible : ¬ Compatible input) :
    formInquiry input depth = none := by
  unfold formInquiry
  rw [prepare_rejects input incompatible]
  rfl

abbrev NewCompiled (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :=
  type_of% ((inquiryAt ready (StageEightDiscreteFormation.codeOf parent)).compileInquiry query)

def compile (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    NewCompiled ready parent query ×
      MotherSubquotient.OriginalOutput ready.val.typeLaw ready.val.actionLaw parent :=
  ((inquiryAt ready (StageEightDiscreteFormation.codeOf parent)).compileInquiry query,
    oldCompiler ready parent query)

def compileMember (input : Input) (parent : MotherVisit) (value : Base) :
    Option (Σ ready : Ready, Σ query : Query ready.val,
      NewCompiled ready parent query ×
        MotherSubquotient.OriginalOutput ready.val.typeLaw ready.val.actionLaw parent) :=
  match prepare input with
  | none => none
  | some ready =>
      match MotherSubquotient.formMember ready.val.material ready.val.index value with
      | none => none
      | some query => some ⟨ready, query, compile ready parent query⟩

theorem compile_new_exact (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    (compile ready parent query).1 = SourceNativeInquiryCompilationAt.answered
      (answerFace ready (StageEightDiscreteFormation.codeOf parent) query)
      (answerConsumer ready (StageEightDiscreteFormation.codeOf parent) query) := rfl

theorem compile_old_exact (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    (compile ready parent query).2 =
      ⟨decode ready query,
        (MotherNativePhysicalQuery.nativeInquiry ready.val.typeLaw ready.val.actionLaw parent).compileInquiry
          (decode ready query)⟩ := rfl

theorem compile_old_rep (ready : Ready) (parent : MotherVisit) (value : Base)
    (inside : MotherSubquotient.predicate ready.val.material ready.val.index value) :
    (compile ready parent (Quot.mk _ ⟨value, inside⟩)).2 =
      MotherOriginalQueryValue.compileRead ready.val.typeLaw ready.val.actionLaw parent value := rfl

theorem compile_answer_exact (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    HEq (compile ready parent query).1.answerReadout
      (query, MotherNativePhysicalQuery.answer ready.val.typeLaw ready.val.actionLaw (decode ready query)) := HEq.rfl

theorem every_member_compiled (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    ∃ value : Base, compileMember ready.val parent value =
      some ⟨ready, query, compile ready parent query⟩ := by
  obtain ⟨value, formed⟩ := MotherSubquotient.every_member ready.val.material ready.val.index query
  refine ⟨value, ?_⟩
  unfold compileMember
  rw [prepare_recovers]
  dsimp only
  rw [formed]

theorem compileMember_rejects (input : Input) (parent : MotherVisit) (value : Base)
    (incompatible : ¬ Compatible input) : compileMember input parent value = none := by
  unfold compileMember
  rw [prepare_rejects input incompatible]

theorem empty_query_kept (ready : Ready) (empty : IsEmpty (Query ready.val))
    (parent : MotherVisit) (value : Base) : compileMember ready.val parent value = none := by
  have memberNone : MotherSubquotient.formMember ready.val.material ready.val.index value = none := by
    cases formed : MotherSubquotient.formMember ready.val.material ready.val.index value with
    | none => rfl
    | some query => exact (empty.false query).elim
  unfold compileMember
  rw [prepare_recovers]
  dsimp only
  rw [memberNone]

/-- One source selector forms a query carrier faithfully equivalent to the
entire original ordered query type. The two complete compilation objects are
retained at their own roots; the equivalence is used only as an explicit
query transport. -/
theorem every_original_inquiry :
    ∃ material : Material, ∀ (index typeLaw actionLaw : Base),
      ∃ ready : Ready,
        ready.val = (⟨material, index, typeLaw, actionLaw⟩ : Input) ∧
        prepare ready.val = some ready ∧
        ∃ queryEquiv : Query ready.val ≃ MotherOriginalQueryValue.Query,
          queryEquiv.toFun = decode ready ∧
          ∀ parent : MotherVisit,
            formInquiry ready.val (StageEightDiscreteFormation.codeOf parent) =
              some (inquiryAt ready (StageEightDiscreteFormation.codeOf parent)) ∧
            ∀ original : MotherOriginalQueryValue.Query,
              ∃ value : Base, ∃ query : Query ready.val,
                queryEquiv query = original ∧
                compileMember ready.val parent value = some ⟨ready, query, compile ready parent query⟩ ∧
                (compile ready parent query).2 =
                  ⟨original,
                    (MotherNativePhysicalQuery.nativeInquiry ready.val.typeLaw ready.val.actionLaw parent).compileInquiry
                      original⟩ := by
  obtain ⟨material, keepExact, relateExact, _⟩ := MotherSubquotient.every_family
    (fun _ _ => True)
    (fun _ left right => MotherOriginalQueryValue.readQuery left = MotherOriginalQueryValue.readQuery right)
  refine ⟨material, fun index typeLaw actionLaw => ?_⟩
  let input : Input := ⟨material, index, typeLaw, actionLaw⟩
  have allInside (value : Base) : MotherSubquotient.predicate material index value :=
    Eq.mpr (congrFun (congrFun keepExact index) value) trivial
  have compatible : Compatible input := by
    intro left right related
    exact Eq.mp (congrFun (congrFun (congrFun relateExact index) left.val) right.val) related
  let ready : Ready := ⟨input, compatible⟩
  have decodeInjective : Function.Injective (decode ready) := by
    intro left right
    induction left using Quot.inductionOn with
    | h left =>
      induction right using Quot.inductionOn with
      | h right =>
        intro same
        apply Quot.sound
        exact Eq.mpr (congrFun (congrFun (congrFun relateExact index) left.val) right.val) same
  have decodeSurjective : Function.Surjective (decode ready) := by
    intro original
    obtain ⟨value, recovered⟩ := MotherOriginalQueryValue.readQuery_surjective original
    exact ⟨Quot.mk _ ⟨value, allInside value⟩, recovered⟩
  let queryEquiv := Equiv.ofBijective (decode ready) ⟨decodeInjective, decodeSurjective⟩
  refine ⟨ready, rfl, prepare_recovers ready, queryEquiv, rfl, fun parent =>
    ⟨formInquiry_recovers ready _, fun original => ?_⟩⟩
  obtain ⟨query, recovered⟩ := queryEquiv.surjective original
  obtain ⟨value, compiled⟩ := every_member_compiled ready parent query
  refine ⟨value, query, recovered, compiled, ?_⟩
  exact congrArg (fun original => (⟨original,
    (MotherNativePhysicalQuery.nativeInquiry ready.val.typeLaw ready.val.actionLaw parent).compileInquiry original⟩ :
      MotherSubquotient.OriginalOutput ready.val.typeLaw ready.val.actionLaw parent)) recovered

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry
