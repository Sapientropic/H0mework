import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Action.Equation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Psi.EffectConsumption
namespace Af
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (afterq constant head head_constant)
end Af
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (afterFace afterDisposition)
end K
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (nextPacket afterFrame afterIndex afterSource AfterTarget afterJointModule BeforeTarget beforeJointModule)
end A
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation)
end D
namespace E
export Lower.SourceFamily.Foresight.Contextual.Psi.Equation
 (gamma difference difference_after difference_effect)
end E
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim (activeEnv)
end Claim
namespace Four
export Lower.SourceFamily.Foresight.Contextual.Profile.FourFace (afterFaces afterInput scopeRead)
end Four
namespace Env
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment (activeIncrement)
end Env
namespace DispositionProjection
variable {Root Generator Carrier:Type u} [AddCommGroup Carrier]
variable {root:RootedAccountedUnfolding Root}
variable {seed:RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
variable {continuation:RootedAccountedUnfolding
 (PresentedRelationEventAt Generator→RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history:RootGeneratedCofinalHistoryAt root seed continuation}
variable {evaluator:RootedAccountedUnfolding (Generator→Carrier)}
variable (face:CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt history evaluator)
variable (conclusion:Prop)
def At (outcome:ResidualDispositionOutcome face):Prop:=
 match outcome with
 | .faithful _ _ _ =>conclusion
 | .unsound _ coordinate =>face.freeEvaluation coordinate.relation≠0
 | .kernelResidual _ _ _ =>conclusion
 | .coverageResidual _ _ _ =>conclusion
theorem read (fromSound:GeneratedRelationSoundnessAt face→conclusion) (outcome:ResidualDispositionOutcome face):
 At face conclusion outcome:=by
 cases outcome with
 | faithful sound _ _ =>exact fromSound sound
 | unsound _ coordinate =>exact fun zero=>coordinate.coordinate_ne_zero (coordinate.coordinate_eq.trans zero)
 | kernelResidual sound _ _ =>exact fromSound sound
 | coverageResidual sound _ _ =>exact fromSound sound
end DispositionProjection
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
attribute [local instance 2000] CharacterModule.instModule
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance afterModule : Module ℤ (A.AfterTarget binding n packet) := A.afterJointModule binding n packet
local instance nextBeforeModule : Module ℤ (A.BeforeTarget binding (n+1) (A.nextPacket binding n packet)) :=
 A.beforeJointModule binding (n+1) (A.nextPacket binding n packet)
abbrev effect := (E.gamma binding n packet).effect (Claim.activeEnv binding n packet) (Env.activeIncrement binding n packet)
variable (native : packet.1.depth=0) (paid : Lower.SourceFamily.Effect.PaidSource.Paid packet.1)

private theorem constant_zero (value : PairValue (Lower.Value W (n+1)) s)
 (zeroValue : Af.constant binding n packet value=0) : value=0 :=
 (Af.head_constant binding n packet value).symm.trans
 ((congrArg (Af.head binding n packet) zeroValue).trans (map_zero _))

include native paid in
private theorem sound_effect (sound : GeneratedRelationSoundnessAt (K.afterFace binding n packet)) : effect binding n packet=0 := by
 have zero:=LinearMap.mem_ker.mp (sound.sound (E.difference_after binding n packet))
 have scopeZero:Af.afterq binding n packet (E.difference binding n packet)=0 :=
  (D.free_evaluation (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2
   (A.afterSource binding n packet) (E.difference binding n packet)).symm.trans zero
 have generated:=E.difference_effect binding n packet native paid
 have complete:=constant_zero binding n packet (0,effect binding n packet) (generated.symm.trans scopeZero)
 exact congrArg Prod.snd complete

include native paid in
theorem scope_zero_iff : Af.afterq binding n packet (E.difference binding n packet)=0 ↔ effect binding n packet=0 := by
 have equation:=E.difference_effect binding n packet native paid
 constructor
 · intro zero
   exact congrArg Prod.snd (constant_zero binding n packet (0,effect binding n packet) (equation.symm.trans zero))
 · intro zero
   change Af.afterq binding n packet (E.difference binding n packet)=Af.constant binding n packet (0,effect binding n packet) at equation
   rw [zero] at equation
   exact equation.trans (map_zero _)

def coordinate := (Four.afterFaces binding n packet).canonical (E.difference binding n packet)

include native paid in
theorem coordinate_read : Four.scopeRead binding n packet (coordinate binding n packet)=
 Af.constant binding n packet (0,effect binding n packet) := by
 change Af.afterq binding n packet (E.difference binding n packet)=_
 exact E.difference_effect binding n packet native paid

include native paid in
theorem coordinate_zero_iff : coordinate binding n packet=0 ↔ effect binding n packet=0 := by
 have scope:=scope_zero_iff binding n packet native paid
 change canonicalResidual (UnifiedFourFace.Evaluation.RootEvaluation (Four.afterInput binding n packet))
  (E.difference binding n packet)=0 ↔ _
 rw [canonicalResidual_eq_zero_iff,←LinearMap.mem_ker]
 change E.difference binding n packet∈LinearMap.ker (Lower.SourceFamily.Foresight.Contextual.Profile.Character.beforeCharacters binding (n+1) (A.nextPacket binding n packet)) ↔ _
 rw [Lower.SourceFamily.Foresight.Contextual.Profile.Character.source_kernel binding (n+1) (A.nextPacket binding n packet),LinearMap.mem_ker]
 exact ((canonicalResidual_eq_zero_iff (A.afterSource binding n packet) (E.difference binding n packet)).symm).trans scope

def dispositionRead : Prop :=
 DispositionProjection.At (K.afterFace binding n packet) (effect binding n packet=0)
  (K.afterDisposition binding n packet)

include native paid in
theorem generated_disposition : dispositionRead binding n packet :=
 DispositionProjection.read (K.afterFace binding n packet) (effect binding n packet=0)
  (sound_effect binding n packet native paid) (K.afterDisposition binding n packet)

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

theorem actual_disposition (k : Nat) : type_of% (generated_disposition (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)) := by
 exact generated_disposition _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
  (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)
theorem actual_coordinate (k : Nat) : type_of% (coordinate_read (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)) :=
 coordinate_read _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)

theorem actual_coordinate_zero_iff (k : Nat) : type_of% (coordinate_zero_iff (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)) :=
 coordinate_zero_iff _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Effect.Installed.actual_native_paid root visit rec U7 calculus anchor sourceStage stage count k)

theorem consume (k : Nat) : type_of% (And.intro
 (Lower.SourceFamily.Foresight.Contextual.Psi.Equation.Actual.source_effect root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_coordinate root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_coordinate_zero_iff root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_disposition root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (Lower.SourceFamily.Foresight.Contextual.Psi.Closure.next_query_consumes
  (Run.binding root visit rec) (k+1) (Run.data root visit rec U7 calculus anchor sourceStage stage count k))
 (Lower.SourceFamily.Replay.Activated.actual_whole_next root visit rec U7 calculus anchor sourceStage stage count (k+1))))))) :=
 ⟨Lower.SourceFamily.Foresight.Contextual.Psi.Equation.Actual.source_effect _ _ _ _ _ _ _ _ _ _,actual_coordinate _ _ _ _ _ _ _ _ _ _,
 actual_coordinate_zero_iff _ _ _ _ _ _ _ _ _ _,actual_disposition _ _ _ _ _ _ _ _ _ _,
 Lower.SourceFamily.Foresight.Contextual.Psi.Closure.next_query_consumes _ _ _,
 Lower.SourceFamily.Replay.Activated.actual_whole_next _ _ _ _ _ _ _ _ _ _⟩
end Actual
end Lower.SourceFamily.Foresight.Contextual.Psi.EffectConsumption
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
