import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Affine.Cochain
import H0mework.Versions.PR.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Realization.Integral.CharacterExact
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Character
namespace E
export SourceGeneratedScalarCharacterExact (DoubleDual evaluation evaluation_injective doubleDualMap doubleDualMap_evaluation)
end E
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (BeforeTarget AfterTarget beforeSource afterSource beforeJointModule afterJointModule)
end A
namespace G
export Lower.SourceFamily.Foresight.Contextual.Profile.Generated (sourceMorphism source_scope_action)
end G
namespace F
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (BeforeScope AfterScope actor beforeq afterq currentBeta substitutedBeta rebase)
end F
namespace C
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine.Cochain (complex actualRelation face effect generated_effect)
end C
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeModule:Module ℤ (A.BeforeTarget binding n packet):=A.beforeJointModule binding n packet
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
attribute [local instance 2000] CharacterModule.instModule

def beforeCharacters:= (E.evaluation ℤ (A.BeforeTarget binding n packet)).comp (A.beforeSource binding n packet)
def afterCharacters:= (E.evaluation ℤ (A.AfterTarget binding n packet)).comp (A.afterSource binding n packet)
theorem source_fibre (left right:Formal ℤ (PairValue (Lower.Value W n)) X s):
 beforeCharacters binding n packet left=beforeCharacters binding n packet right ↔
 A.beforeSource binding n packet left=A.beforeSource binding n packet right:=by
 constructor
 · intro same
   exact E.evaluation_injective ℤ (A.BeforeTarget binding n packet) same
 · intro same
   exact congrArg (E.evaluation ℤ (A.BeforeTarget binding n packet)) same
theorem source_kernel:
 LinearMap.ker (beforeCharacters binding n packet)=LinearMap.ker (A.beforeSource binding n packet):=by
 ext word
 simp only [LinearMap.mem_ker]
 constructor
 · intro invisible
   apply E.evaluation_injective ℤ (A.BeforeTarget binding n packet)
   exact invisible.trans (map_zero (E.evaluation ℤ (A.BeforeTarget binding n packet))).symm
 · intro invisible
   change E.evaluation ℤ (A.BeforeTarget binding n packet) (A.beforeSource binding n packet word)=0
   rw [invisible,map_zero]
variable (native:packet.1.depth=0)
include native in
def characterAction:=E.doubleDualMap (G.sourceMorphism binding n packet native).targetMap
include native in
theorem generated_square (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 characterAction binding n packet native (beforeCharacters binding n packet word)=
 afterCharacters binding n packet (liftMap word):=by
 apply (E.doubleDualMap_evaluation (G.sourceMorphism binding n packet native).targetMap
  (A.beforeSource binding n packet word)).trans
 exact congrArg (E.evaluation ℤ (A.AfterTarget binding n packet))
  (LinearMap.congr_fun (G.sourceMorphism binding n packet native).commutes word)
include native in
def characterMorphism:Morphism (beforeCharacters binding n packet) (afterCharacters binding n packet) where
 sourceMap:=liftMap
 targetMap:=characterAction binding n packet native
 commutes:=by
  apply LinearMap.ext
  exact generated_square binding n packet native
include native in
def residualCharacters:=E.doubleDualMap ((F.rebase binding n packet).comp (F.actor binding n packet native))
include native in
theorem actual_paid_characters:
 E.evaluation ℤ (F.AfterScope binding n packet)
  ((C.face binding n packet).closureEvaluation
   (((C.complex binding n packet).d 0 1).hom (C.actualRelation binding n packet)))=
 residualCharacters binding n packet native
  (E.evaluation ℤ (F.BeforeScope binding n packet)
   (F.beforeq binding n packet (F.currentBeta binding n packet)+
    F.beforeq binding n packet (F.substitutedBeta binding n packet))):=
 (congrArg (E.evaluation ℤ (F.AfterScope binding n packet)) (C.generated_effect binding n packet native)).trans
  (E.doubleDualMap_evaluation ((F.rebase binding n packet).comp (F.actor binding n packet native)) _).symm
include native in
theorem complete_effect_zero_iff:
 residualCharacters binding n packet native
  (E.evaluation ℤ (F.BeforeScope binding n packet)
   (F.beforeq binding n packet (F.currentBeta binding n packet)+
    F.beforeq binding n packet (F.substitutedBeta binding n packet)))=0 ↔
 C.effect binding n packet native=0:=by
 have actual:=E.doubleDualMap_evaluation ((F.rebase binding n packet).comp (F.actor binding n packet native))
  (F.beforeq binding n packet (F.currentBeta binding n packet)+F.beforeq binding n packet (F.substitutedBeta binding n packet))
 constructor
 · intro zero
   apply E.evaluation_injective ℤ (F.AfterScope binding n packet)
   exact actual.symm.trans (zero.trans (map_zero (E.evaluation ℤ (F.AfterScope binding n packet))).symm)
 · intro zero
   exact actual.trans ((congrArg (E.evaluation ℤ (F.AfterScope binding n packet)) zero).trans (map_zero _))

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
def action:type_of% (characterMorphism (Run.binding root visit rec) (n+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n)):=
 characterMorphism (Run.binding root visit rec) (n+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n)
theorem consume:type_of% (And.intro
 (source_kernel (Run.binding root visit rec) (n+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count n))
 (actual_paid_characters (Run.binding root visit rec) (n+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
  (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n))):=
 And.intro
 (source_kernel (Run.binding root visit rec) (n+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count n))
 (actual_paid_characters (Run.binding root visit rec) (n+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count n)
  (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count n))
end Actual

end Lower.SourceFamily.Foresight.Contextual.Profile.Character
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
