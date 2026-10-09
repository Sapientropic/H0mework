import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Transport
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Action.Assembly
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual SourceGeneratedScalarCofinalNaturality
open SourceGeneratedScalarCofinalKernelCompletion
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Generated
namespace F
export Lower.SourceFamily.Foresight (data)
end F
namespace L
export Lower.SourceFamily.Foresight.Tail (State advance)
end L
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (ReadMorphisms beforeState afterState profileData beforeFrame actual_scope_action actual_kernel_preserved)
end A
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Transport (actualTransport actual_generator)
end T
namespace N
export Lower.SourceFamily.Foresight.Contextual.Profile.Naturality (morphism)
end N
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState)
end I
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
private def compose
 {G1 G2 G3:Type u} [AddCommGroup G1] [Module ℤ G1] [AddCommGroup G2] [Module ℤ G2] [AddCommGroup G3] [Module ℤ G3]
 {C1 C2 C3:Nat→Type u} [∀j,AddCommGroup (C1 j)] [∀j,Module ℤ (C1 j)]
 [∀j,AddCommGroup (C2 j)] [∀j,Module ℤ (C2 j)] [∀j,AddCommGroup (C3 j)] [∀j,Module ℤ (C3 j)]
 {d1:Data (R:=ℤ) (Generator:=G1) (Carrier:=C1)} {d2:Data (R:=ℤ) (Generator:=G2) (Carrier:=C2)}
 {d3:Data (R:=ℤ) (Generator:=G3) (Carrier:=C3)}
 (first:Morphism d1 d2) (second:Morphism d2 d3) :Morphism d1 d3 where
 generatorMap:=second.generatorMap.comp first.generatorMap
 stageMap:=fun j=>(second.stageMap j).comp (first.stageMap j)
 transition_naturality j:=by
  apply LinearMap.ext
  intro value
  exact (congrArg (second.stageMap j) (LinearMap.congr_fun (first.transition_naturality j) value)).trans
   (LinearMap.congr_fun (second.transition_naturality j) (first.stageMap (j+1) value))
 evaluator_naturality j:=by
  apply LinearMap.ext
  intro word
  exact (congrArg (second.stageMap j) (LinearMap.congr_fun (first.evaluator_naturality j) word)).trans
   (LinearMap.congr_fun (second.evaluator_naturality j) (first.generatorMap word))

variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
namespace Epoch
variable {V Y:S→Type u} [∀t,AddCommGroup (V t)] {t:S}
variable (frame:M.Frame (Value:=V) (Var:=Y) (sort:=t))
theorem idempotent : E.epoch (E.epoch frame)=E.epoch frame :=rfl
theorem of_zero (native:frame.depth=0) : E.epoch frame=frame :=by
 unfold E.epoch
 cases frame
 simp_all
end Epoch

variable (native:packet.1.depth=0)
private abbrev Package (before:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
 (after:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) (n+1)) :=
 {move:Morphism (F.data binding (⟨n,before⟩:L.State (W:=W) (X:=X) (s:=s)) s 1)
  (F.data binding (⟨n+1,after⟩:L.State (W:=W) (X:=X) (s:=s)) s 0)//move.generatorMap=LinearMap.id}
private def nativePackage : {move:Morphism (F.data binding (A.beforeState n packet) s 1)
 (F.data binding (A.afterState binding n packet) s 0) //move.generatorMap=LinearMap.id} :=by
 let next:=Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.nextPacket binding n packet
 have beforePacket : (⟨E.epoch (E.epoch packet.1),packet.2⟩:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)=packet :=
  congrArg (fun frame=>(⟨frame,packet.2⟩:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n))
   ((Epoch.idempotent packet.1).trans (Epoch.of_zero packet.1 native))
 have afterPacket : (⟨E.epoch (E.epoch next.1),next.2⟩:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) (n+1))=next :=
  congrArg (fun frame=>(⟨frame,next.2⟩:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) (n+1)))
   ((Epoch.idempotent next.1).trans (Epoch.of_zero next.1 rfl))
 let old:=Lower.SourceFamily.Foresight.Successor.natural binding (⟨n,packet⟩:L.State (W:=W) (X:=X) (s:=s)) s
 let generated:=compose old (T.actualTransport binding n packet s)
 have oldIdentity :old.generatorMap=LinearMap.id :=by
  apply LinearMap.ext
  intro word
  exact Lower.SourceFamily.Foresight.Successor.generator_actual binding (⟨n,packet⟩:L.State (W:=W) (X:=X) (s:=s)) s word
 have genIdentity :generated.generatorMap=LinearMap.id :=
  (congrArg (fun map=>map.comp old.generatorMap) (T.actual_generator binding n packet s)).trans
   ((LinearMap.id_comp old.generatorMap).trans oldIdentity)
 have complete :Package binding n packet next:=⟨generated,genIdentity⟩
 exact Eq.mpr
  ((congrArg (fun first=>Package binding n first (⟨E.epoch (E.epoch next.1),next.2⟩:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) (n+1))) beforePacket).trans
   (congrArg (Package binding n packet) afterPacket)) complete

def nativeMove := (nativePackage binding n packet native).val
theorem native_generator : (nativeMove binding n packet native).generatorMap=LinearMap.id :=
 (nativePackage binding n packet native).property

def readMorphisms :A.ReadMorphisms binding n packet where
 native:=nativeMove binding n packet native
 profile:=compose (nativeMove binding n packet native) (N.morphism binding (A.afterState binding n packet) s)
 native_generator:=native_generator binding n packet native
 profile_generator:=
  (congrArg (fun p=>LinearMap.id.comp p) (native_generator binding n packet native)).trans (LinearMap.id_comp _)
def originalMorphism := Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.originalMorphism binding n packet
 (readMorphisms binding n packet native)
def sourceMorphism := Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.morphism binding n packet
 (readMorphisms binding n packet native)
theorem source_scope_action (word:Formal ℤ (PairValue (Lower.Value W n)) X s) :
 type_of% (A.actual_scope_action binding n packet (readMorphisms binding n packet native) word) :=
 A.actual_scope_action binding n packet (readMorphisms binding n packet native) word

include native in
theorem source_kernel_preserved (word:Formal ℤ (PairValue (Lower.Value W n)) X s) :
 type_of% (A.actual_kernel_preserved binding n packet (readMorphisms binding n packet native) word) :=
 A.actual_kernel_preserved binding n packet (readMorphisms binding n packet native) word
end Lower.SourceFamily.Foresight.Contextual.Profile.Generated
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
