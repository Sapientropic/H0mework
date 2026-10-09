import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Source
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Environment.Generated
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment
namespace C
export Lower.SourceFamily.Foresight.Contextual (factory)
end C
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
 (cfg material activeEnv activeExpression activeWord actionWord input_environment input_expression paidSource payment actual_claim_equation)
end Claim
namespace E
export Lower.SourceFamily.Foresight.Contextual.Effect
 (actualDecoder actualEnvironment actualIncrement packet_decoder_read actual_environment actual_word source_environment)
end E
namespace Af
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine
 (AfterScope afterq head head_source afterEnv after_environment writerBoundary rawWord constant)
end Af
namespace Pmt
export Lower.SourceFamily.Effect.PaidSource (Paid)
end Pmt
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance afterModule : Module ℤ (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.AfterTarget binding n packet) :=
 Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.afterJointModule binding n packet

def activeIncrement : Env (Lower.Value W (n+1)) X :=
 let environment : Env (Lower.Value W (n+1)) X := Claim.activeEnv binding n packet
 SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1)) environment-environment

variable (paid : Pmt.Paid packet.1)
include paid in
theorem decoder_active : E.actualDecoder binding n packet=Claim.activeEnv binding n packet := by
 rcases paid with ⟨step,actual⟩
 exact (Lower.SourceFamily.Effect.Environment.Generated.packet_decoder_paid
  (C.factory (s:=s) binding) n packet step actual).trans
  (Claim.input_environment binding n packet).symm

include paid in
theorem actual_environment : E.actualEnvironment binding n packet=
 pairEnvironment (Claim.activeEnv binding n packet) (activeIncrement binding n packet) :=
 (E.actual_environment binding n packet).trans
 (congrArg (fun env : Env (Lower.Value W (n+1)) X =>
  pairEnvironment env (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1)) env-env))
  (decoder_active binding n packet paid))

include paid in
theorem head_active :
 Af.head binding n packet (Af.afterq binding n packet (liftMap (Claim.activeWord binding n packet)))=
 updateInventory (R:=ℤ) (Claim.activeEnv binding n packet) (activeIncrement binding n packet)
  (Claim.activeWord binding n packet) := by
 have head:=Af.head_source binding n packet (liftMap (Claim.activeWord binding n packet))
 have env:Af.afterEnv binding n packet=E.actualEnvironment binding n packet:=
  (Af.after_environment binding n packet).trans (E.source_environment binding n packet)
 apply head.trans
 apply (congrArg (fun env=>evaluation (R:=ℤ) env (liftMap (Claim.activeWord binding n packet))) env).trans
 rw [actual_environment binding n packet paid]
 exact LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s)
  (Claim.activeEnv binding n packet) (activeIncrement binding n packet)) (Claim.activeWord binding n packet)

include paid in
theorem head_channels : type_of% ((head_active binding n packet paid).trans
 (show updateInventory (R:=ℤ) (Claim.activeEnv binding n packet) (activeIncrement binding n packet)
  (Claim.activeWord binding n packet)=
 ((Claim.activeExpression binding n packet).eval (Claim.activeEnv binding n packet),
  (Claim.activeExpression binding n packet).effect (Claim.activeEnv binding n packet) (activeIncrement binding n packet)) by
  simp only [Claim.activeWord,Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.activeWord,
   updateInventory,LinearMap.prod_apply,Function.prod,evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul])) :=
 (head_active binding n packet paid).trans (by
  simp only [Claim.activeWord,Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.activeWord,
   updateInventory,LinearMap.prod_apply,Function.prod,evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
  rfl)

variable (native : packet.1.depth=0)
include paid native in
theorem head_corrected_claim :
 Af.head binding n packet
  (Af.afterq binding n packet (Af.writerBoundary binding n packet (Claim.actionWord binding n packet))+
   Af.constant binding n packet (Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.endpointCorrection binding n packet))=
 updateInventory (R:=ℤ) (Claim.activeEnv binding n packet) (activeIncrement binding n packet)
  (Claim.activeWord binding n packet) :=
 (congrArg (Af.head binding n packet) (Claim.actual_claim_equation binding n packet native)).symm.trans
  (head_active binding n packet paid)

namespace Actual
open RootLawDependentJointStateController
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.physicalGroups
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.currentGroups
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage count : Nat)
namespace Run
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.Run (binding data actual_depth)
end Run
theorem source_paid (k : Nat) : Pmt.Paid (Run.data root visit rec U7 calculus anchor sourceStage stage count k).1 :=
 Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k

theorem actual_decoder (k : Nat) : type_of% (decoder_active (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (source_paid root visit rec U7 calculus anchor sourceStage stage count k)) :=
 decoder_active _ _ _ (source_paid root visit rec U7 calculus anchor sourceStage stage count k)

theorem actual_head (k : Nat) : type_of% (head_active (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (source_paid root visit rec U7 calculus anchor sourceStage stage count k)) :=
 head_active _ _ _ (source_paid root visit rec U7 calculus anchor sourceStage stage count k)
theorem actual_corrected_head (k : Nat) : type_of% (head_corrected_claim (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (source_paid root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)) :=
 head_corrected_claim _ _ _ (source_paid root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
end Actual
end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
