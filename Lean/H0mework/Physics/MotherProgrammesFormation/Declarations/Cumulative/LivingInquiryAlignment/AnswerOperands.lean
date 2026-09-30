import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeProgram.Faces
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryAnswerOperands
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev Support := root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
  (root.emitted visit.current)
abbrev Projection := root.toAuthoritativeRoot.source.projectionLaw.Projection
abbrev Theory := root.toAuthoritativeRoot.source.lawSurface

/-- Actual small operands for the three answering constructors. Face and
consumer values are formed by the original projection compiler. -/
inductive Operand : Type
  | answered (answer consumer : Projection root)
  | u7Answered (obstruction : N.ObstructionAt (Support root visit)) (answer consumer : Projection root)
  | oldLanguageAnswered (obstruction : N.ObstructionAt (Support root visit))
      (expression : (Theory root).ExpressionAt (Support root visit))
      (realization : (Theory root).inventory.RealizationAt obstruction)
      (answer consumer : Projection root)

variable {root visit} {Query : Type} (query : Query)
    (entry : OpenResponsibilityAt N (Support root visit))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry)
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)

abbrev InquiryEvent := ULift.up.{1, 0} (root.emitted visit.current)

abbrev AnswerPair := Σ face : SourceNativeRootSemanticFaceAt root visit,
  SourceNativeInquiryAnswerConsumerAt query (InquiryEvent (root := root) (visit := visit)) entry face

def formAnswerPair (answer consumer : Projection root) : Option (AnswerPair query entry) :=
  (MotherNativeFaces.semanticFace root visit answer).bind (fun face =>
    (MotherNativeFaces.answerConsumer query (InquiryEvent (root := root) (visit := visit)) entry face consumer).map
      (fun receipt => ⟨face, receipt⟩))

theorem answerPair_recovers (pair : AnswerPair query entry) :
    formAnswerPair query entry pair.1.projection pair.2.projection = some pair := by
  rcases pair with ⟨face, receipt⟩
  simp only [formAnswerPair, MotherNativeFaces.semanticFace_recovers, Option.bind_some,
    MotherNativeFaces.answerConsumer_recovers, Option.map_some]

def formOldAnswer (obstruction : N.ObstructionAt (Support root visit))
    (expression : (Theory root).ExpressionAt (Support root visit))
    (realization : (Theory root).inventory.RealizationAt obstruction) :
    Option (OldLanguageAnswerAt (Theory root) obstruction) :=
  if same : (Theory root).denotes expression = N.obstructionClaim obstruction then
    some ⟨⟨expression, same⟩, realization⟩
  else none

theorem oldAnswer_recovers {obstruction : N.ObstructionAt (Support root visit)}
    (answer : OldLanguageAnswerAt (Theory root) obstruction) :
    formOldAnswer obstruction answer.expression.val answer.realization = some answer := by
  rcases answer with ⟨⟨expression, same⟩, realization⟩
  exact dif_pos same

private theorem u7_subsingleton (obstruction : N.ObstructionAt (Support root visit)) :
    Subsingleton (SourceNativeU7AnswersAt calculus obstruction) := by
  dsimp only [SourceNativeU7AnswersAt]
  split <;> infer_instance

private def uniqueMember {A : Type} [Subsingleton A] : Option A :=
  if exists_ : Nonempty A then some exists_.some else none

private theorem uniqueMember_recovers {A : Type} [Subsingleton A] (value : A) :
    uniqueMember = some value := by
  unfold uniqueMember
  rw [dif_pos ⟨value⟩]
  exact congrArg some (Subsingleton.elim _ _)

abbrev Compilation := SourceNativeInquiryCompilationAt root visit U7 calculus (Theory root) query
  (InquiryEvent (root := root) (visit := visit)) entry authority

/-- The original U7 calculus and root faces supply their own complete
receipts. Input operands contain no completed inquiry compilation. -/
def form (operand : Operand root visit) : Option (Compilation query entry authority calculus) :=
  match operand with
  | .answered answer consumer =>
      (formAnswerPair query entry answer consumer).map (fun pair => .answered pair.1 pair.2)
  | .u7Answered obstruction answer consumer =>
      letI := u7_subsingleton (root := root) (visit := visit) calculus obstruction
      (uniqueMember (A := SourceNativeU7AnswersAt calculus obstruction)).bind (fun disposition =>
        (formAnswerPair query entry answer consumer).map (fun pair => .u7Answered obstruction disposition pair.1 pair.2))
  | .oldLanguageAnswered obstruction expression realization answer consumer =>
      (uniqueMember (A := SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)).bind (fun gate =>
        (formOldAnswer obstruction expression realization).bind (fun oldAnswer =>
          (formAnswerPair query entry answer consumer).map
            (fun pair => .oldLanguageAnswered obstruction gate oldAnswer pair.1 pair.2)))

theorem answered_recovers (pair : AnswerPair query entry) :
    form query entry authority calculus (.answered pair.1.projection pair.2.projection) =
      some (.answered pair.1 pair.2) := by
  simp only [form, answerPair_recovers, Option.map_some]

theorem u7Answered_recovers (obstruction : N.ObstructionAt (Support root visit))
    (disposition : SourceNativeU7AnswersAt calculus obstruction) (pair : AnswerPair query entry) :
    form query entry authority calculus (.u7Answered obstruction pair.1.projection pair.2.projection) =
      some (.u7Answered obstruction disposition pair.1 pair.2) := by
  let := u7_subsingleton (root := root) (visit := visit) calculus obstruction
  simp only [form, uniqueMember_recovers disposition, Option.bind_some, answerPair_recovers, Option.map_some]

theorem oldLanguageAnswered_recovers (obstruction : N.ObstructionAt (Support root visit))
    (gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)
    (oldAnswer : OldLanguageAnswerAt (Theory root) obstruction) (pair : AnswerPair query entry) :
    form query entry authority calculus (.oldLanguageAnswered obstruction oldAnswer.expression.val oldAnswer.realization
      pair.1.projection pair.2.projection) = some (.oldLanguageAnswered obstruction gate oldAnswer pair.1 pair.2) := by
  simp only [form, uniqueMember_recovers gate, Option.bind_some, oldAnswer_recovers, answerPair_recovers, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryAnswerOperands
