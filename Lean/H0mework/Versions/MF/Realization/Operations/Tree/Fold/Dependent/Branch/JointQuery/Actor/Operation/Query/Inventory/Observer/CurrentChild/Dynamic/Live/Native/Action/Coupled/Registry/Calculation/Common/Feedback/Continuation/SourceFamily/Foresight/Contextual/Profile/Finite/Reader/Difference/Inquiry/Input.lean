import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
variable {S:Type u} {s:S}
namespace Sealed
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (resultFace)
end C
open RootGeneratedDebtActivationJointSource.OwnerFree
open RootGeneratedDebtActivationJointSource.OwnerFree.Installation
variable {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable (old:RootInquiryStateAt N V)
variable {Y Z:S→Type u} [∀t,AddCommGroup (Y t)]
variable (rawReader : {current : V.Current} →
 old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
 Raw (Value := Y) (Var := Z) (sort := s)) (incidence : old.Query)
abbrev own:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.state old rawReader
abbrev candidate:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.query old rawReader incidence
abbrev guard:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumerLaw old rawReader

def queryLaw:SourceNativeProjectionLaw (own old rawReader).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit
 ActiveAt:=fun _ {_current} occurrence=>(guard old rawReader).ActiveAt (candidate old rawReader incidence) occurrence
 InactiveAt:=fun _ {_current} occurrence=>(guard old rawReader).InactiveAt (candidate old rawReader incidence) occurrence
 classify:=fun _ {_current} occurrence=>(guard old rawReader).classify (candidate old rawReader incidence) occurrence
 PayloadAt:=fun _ {_current} _ _=>(own old rawReader).Query
 project:=fun _ {_current} _ _=>candidate old rawReader incidence

def root:=(own old rawReader).root.withProjectionCoface (queryLaw old rawReader incidence)
def installation:=SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (own old rawReader).root.source.base (queryLaw old rawReader incidence)

def resultFace:SourceNativeRootSemanticFaceAt (root old rawReader incidence) (own old rawReader).visit where
 projection:=(installation old rawReader incidence).embed (C.resultFace old rawReader).projection
 active:=(C.resultFace old rawReader).active
 classifier_eq:=(C.resultFace old rawReader).classifier_eq

def consumer (question:(own old rawReader).Query):SourceNativeInquiryAnswerConsumerAt
 (root:=root old rawReader incidence) (visit:=(own old rawReader).visit) question
 (ULift.up.{u+1,u} ((root old rawReader incidence).emitted (own old rawReader).visit.current))
 ((own old rawReader).entryAt question) (resultFace old rawReader incidence) where
 projection:=(installation old rawReader incidence).embed
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer old rawReader question).projection
 active:=(RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer old rawReader question).active
 classifier_eq:=(RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer old rawReader question).classifier_eq
 project_heq:=(RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer old rawReader question).project_heq

def authority (question:(own old rawReader).Query):=
 ((own old rawReader).authorityAt question).withProjectionCoface (queryLaw old rawReader incidence)

def compilation (question:(own old rawReader).Query):SourceNativeInquiryCompilationProgramAt
 (root old rawReader incidence) (own old rawReader).visit old.U7 old.calculus old.root.source.base.lawSurface
 question (ULift.up.{u+1,u} ((root old rawReader incidence).emitted (own old rawReader).visit.current))
 ((own old rawReader).entryAt question) (authority old rawReader incidence question) where
 compile:=fun _=>.answered (resultFace old rawReader incidence) (consumer old rawReader incidence question)

def state:RootInquiryStateAt N V where
 root:=root old rawReader incidence
 visit:=(own old rawReader).visit
 U7:=old.U7
 calculus:=old.calculus
 Query:=(own old rawReader).Query
 entryAt:=(own old rawReader).entryAt
 authorityAt:=authority old rawReader incidence
 compilationProgramAt:=compilation old rawReader incidence
 compilationFaceAt:=fun question=>{
  projection:=(installation old rawReader incidence).embed ((own old rawReader).compilationFaceAt question).projection
  active:=((own old rawReader).compilationFaceAt question).active
  classifier_eq:=((own old rawReader).compilationFaceAt question).classifier_eq
  project_heq:=((own old rawReader).compilationFaceAt question).project_heq }
 u7RootDisposition_commutes:=by intro _ _ _ impossible;exact nomatch impossible

def input:SourceNativeRootInquiryInputAt (state old rawReader incidence).root
 (state old rawReader incidence).visit (state old rawReader incidence).Query where
 projection:=.component PUnit.unit
 active:=⟨⟨rfl⟩⟩
 classifier_eq:=by
  change (guard old rawReader).classify (candidate old rawReader incidence) (old.root.emitted old.visit.current)=.inl ⟨⟨rfl⟩⟩
  unfold guard RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumerLaw
  exact dif_pos rfl
 queryType_eq:=rfl

theorem input_generated:(input old rawReader incidence).query=candidate old rawReader incidence:=rfl

theorem compiles:(state old rawReader incidence).compileInquiry (input old rawReader incidence).query=
 .answered (resultFace old rawReader incidence) (consumer old rawReader incidence (input old rawReader incidence).query):=rfl
end Sealed
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
