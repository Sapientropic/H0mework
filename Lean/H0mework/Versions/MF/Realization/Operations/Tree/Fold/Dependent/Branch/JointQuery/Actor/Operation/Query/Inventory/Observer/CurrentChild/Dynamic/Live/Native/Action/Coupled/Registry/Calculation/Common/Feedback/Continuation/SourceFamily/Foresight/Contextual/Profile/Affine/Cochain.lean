import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Affine.Consumer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Consumer
import H0mework.Versions.MF.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel
set_option autoImplicit false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Affine.Cochain
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (writerBoundary rawWord raw_boundary_in_next rawBoundaryVector raw_boundary_relation actual_next_relation_value
 rebase actor beforeq currentBeta substitutedBeta)
end T
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (nextPacket afterSource AfterTarget afterJointModule)
end A
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (jointHistory)
end Wr
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (afterFace afterDisposition)
end K
namespace C
export CofinalRelationGeneratedComplex (natComplex natComplex_d_zero_one relationInclusion completion_kills_generated_differential)
end C
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
variable (native:packet.1.depth=0)
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
abbrev history:=Wr.jointHistory binding n packet
abbrev face:=K.afterFace binding n packet
def actualRelation:(history binding n packet).relationClosure:=
 ⟨T.writerBoundary binding n packet (T.rawWord binding n packet), T.raw_boundary_in_next binding n packet⟩
def complex:=C.natComplex (history binding n packet)
include native in
def effect:=T.rebase binding n packet (T.actor binding n packet native
 (T.beforeq binding n packet (T.currentBeta binding n packet)+
  T.beforeq binding n packet (T.substitutedBeta binding n packet)))
theorem generated_differential:
 ((complex binding n packet).d 0 1).hom (actualRelation binding n packet)=T.rawBoundaryVector binding n packet:=by
 dsimp only [complex]
 rw [C.natComplex_d_zero_one]
 apply Subtype.ext
 rfl
include native in
theorem generated_effect:
 (face binding n packet).closureEvaluation (((complex binding n packet).d 0 1).hom (actualRelation binding n packet))=
 effect binding n packet native:=
 (congrArg (face binding n packet).closureEvaluation (generated_differential binding n packet)).trans
 (T.actual_next_relation_value binding n packet native)
theorem source_completion_zero:
 (history binding n packet).completionProjection (((complex binding n packet).d 0 1).hom (actualRelation binding n packet))=0:=
 C.completion_kills_generated_differential (history binding n packet) (actualRelation binding n packet)
include native in
theorem sound_effect_zero (sound:GeneratedRelationSoundnessAt (face binding n packet)):
 effect binding n packet native=0:=by
 have source:=(face binding n packet).relationInGeneratorClosure_le_kernel sound (T.raw_boundary_relation binding n packet)
 exact (T.actual_next_relation_value binding n packet native).symm.trans (LinearMap.mem_ker.mp source)
include native in
def DispositionRead (outcome:ResidualDispositionOutcome (face binding n packet)):Prop:=
 match outcome with
 | .faithful _ _ _ => effect binding n packet native=0
 | .unsound _ _ => ∃ relation, relation∈(history binding n packet).relationClosure ∧
    (face binding n packet).freeEvaluation relation≠0
 | .kernelResidual _ _ _ => effect binding n packet native=0
 | .coverageResidual _ _ _ => effect binding n packet native=0
include native in
theorem actual_disposition_effect:
 DispositionRead binding n packet native (K.afterDisposition binding n packet):=by
 generalize selected:K.afterDisposition binding n packet=outcome
 cases outcome with
 | faithful sound _ _ => exact sound_effect_zero binding n packet native sound
 | unsound obstruction _ => exact (face binding n packet).unsoundRelationWitness obstruction
 | kernelResidual sound _ _ => exact sound_effect_zero binding n packet native sound
 | coverageResidual sound _ _ => exact sound_effect_zero binding n packet native sound

namespace Actual
open RootLawDependentJointStateController
namespace Run
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.Run (binding data actual_depth)
end Run
variable {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable {H:Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root:SourceNativeLivingRootClosure N V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec:RecognitionAt H root)
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.physicalGroups
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.currentGroups
variable (U7:U7ProducerCalculus N) (calculus:U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count n:Nat)
theorem consume:type_of% (And.intro
 (generated_effect (Run.binding root visit rec) (n+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
  (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n))
 (And.intro
  (source_completion_zero (Run.binding root visit rec) (n+1)
   (Run.data root visit rec U7 calculus anchor sourceStage stage count n))
  (actual_disposition_effect (Run.binding root visit rec) (n+1)
   (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
   (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n)))):=
 And.intro
  (generated_effect (Run.binding root visit rec) (n+1)
   (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
   (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n))
  (And.intro
   (source_completion_zero (Run.binding root visit rec) (n+1)
    (Run.data root visit rec U7 calculus anchor sourceStage stage count n))
   (actual_disposition_effect (Run.binding root visit rec) (n+1)
    (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
    (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n)))
end Actual

end Lower.SourceFamily.Foresight.Contextual.Profile.Affine.Cochain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
