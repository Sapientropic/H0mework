import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeProgram.Clause

/-! The original projection compiler forms the active face and both original
consumer receipts. Full-root and compilation indices are fixed throughout;
this eliminates stored face fields, without changing their source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeFaces

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical

universe u

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}

noncomputable section

def semanticFace (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (projection : root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    Option (SourceNativeRootSemanticFaceAt root visit) :=
  match classified : root.toAuthoritativeRoot.source.projectionLaw.classify
      projection (root.emitted visit.current) with
  | .inl active => some ⟨projection, active, classified⟩
  | .inr _ => none

theorem semanticFace_recovers (face : SourceNativeRootSemanticFaceAt root visit) :
    semanticFace root visit face.projection = some face := by
  cases face with
  | mk projection active classified =>
      unfold semanticFace
      split
      · rename_i formed same
        have equal := Sum.inl.inj (same.symm.trans classified)
        cases equal
        rfl
      · rename_i _ same
        cases same.symm.trans classified

theorem semanticFace_inactive
    (projection : root.toAuthoritativeRoot.source.projectionLaw.Projection)
    (inactive : root.toAuthoritativeRoot.source.projectionLaw.InactiveAt
      projection (root.emitted visit.current))
    (classified : root.toAuthoritativeRoot.source.projectionLaw.classify
      projection (root.emitted visit.current) = .inr inactive) :
    semanticFace root visit projection = none := by
  unfold semanticFace
  split
  · rename_i _ same
    cases same.symm.trans classified
  · rfl

variable {Query : Type u} {query : Query}
  {InquiryEvent : Type (u + 1)} {event : InquiryEvent}
  {entry : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}

private def answerAt (query : Query) (event : InquiryEvent)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (answer : SourceNativeRootSemanticFaceAt root visit)
    (face : SourceNativeRootSemanticFaceAt root visit) :
    Option (SourceNativeInquiryAnswerConsumerAt query event entry answer) :=
  if installed : HEq face.rootRead
      (SourceNativeInquiryAnswerConsumerTokenAt.canonical :
        SourceNativeInquiryAnswerConsumerTokenAt query event entry answer.rootRead) then
    some ⟨face.projection, face.active, face.classifier_eq, installed⟩
  else none

def answerConsumer (query : Query) (event : InquiryEvent)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (answer : SourceNativeRootSemanticFaceAt root visit)
    (projection : root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    Option (SourceNativeInquiryAnswerConsumerAt query event entry answer) :=
  (semanticFace root visit projection).bind (answerAt query event entry answer)

theorem answerConsumer_recovers {answer : SourceNativeRootSemanticFaceAt root visit}
    (consumer : SourceNativeInquiryAnswerConsumerAt query event entry answer) :
    answerConsumer query event entry answer consumer.projection = some consumer := by
  cases consumer with
  | mk projection active classified installed =>
      exact (congrArg (fun candidate => candidate.bind (answerAt query event entry answer))
        (semanticFace_recovers ⟨projection, active, classified⟩)).trans (dif_pos installed)

theorem answerConsumer_rejects (answer face : SourceNativeRootSemanticFaceAt root visit)
    (different : ¬ HEq face.rootRead
      (SourceNativeInquiryAnswerConsumerTokenAt.canonical :
        SourceNativeInquiryAnswerConsumerTokenAt query event entry answer.rootRead)) :
    answerConsumer query event entry answer face.projection = none :=
  (congrArg (fun candidate => candidate.bind (answerAt query event entry answer))
    (semanticFace_recovers face)).trans (dif_neg different)

variable {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
  {oldTheory : TheoryState N}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

private def compilationAt
    (compiled : SourceNativeInquiryCompilationAt
      root visit U7 calculus oldTheory query event entry authority)
    (face : SourceNativeRootSemanticFaceAt root visit) :
    Option (SourceNativeRootInquiryCompilationFaceCoreAt root visit query event entry authority compiled) :=
  if installed : HEq face.rootRead
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := entry) (query := query) (event := event)
        (audit := compiled.audit) compiled.answerReadout) then
    some ⟨face.projection, face.active, face.classifier_eq, installed⟩
  else none

def compilationFace
    (compiled : SourceNativeInquiryCompilationAt
      root visit U7 calculus oldTheory query event entry authority)
    (projection : root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    Option (SourceNativeRootInquiryCompilationFaceCoreAt root visit query event entry authority compiled) :=
  (semanticFace root visit projection).bind (compilationAt compiled)

theorem compilationFace_recovers
    {compiled : SourceNativeInquiryCompilationAt
      root visit U7 calculus oldTheory query event entry authority}
    (face : SourceNativeRootInquiryCompilationFaceCoreAt root visit query event entry authority compiled) :
    compilationFace compiled face.projection = some face := by
  cases face with
  | mk projection active classified installed =>
      exact (congrArg (fun candidate => candidate.bind (compilationAt compiled))
        (semanticFace_recovers ⟨projection, active, classified⟩)).trans (dif_pos installed)

theorem compilationFace_rejects
    (compiled : SourceNativeInquiryCompilationAt
      root visit U7 calculus oldTheory query event entry authority)
    (face : SourceNativeRootSemanticFaceAt root visit)
    (different : ¬ HEq face.rootRead
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := entry) (query := query) (event := event)
        (audit := compiled.audit) compiled.answerReadout)) :
    compilationFace compiled face.projection = none :=
  (congrArg (fun candidate => candidate.bind (compilationAt compiled))
    (semanticFace_recovers face)).trans (dif_neg different)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeFaces
