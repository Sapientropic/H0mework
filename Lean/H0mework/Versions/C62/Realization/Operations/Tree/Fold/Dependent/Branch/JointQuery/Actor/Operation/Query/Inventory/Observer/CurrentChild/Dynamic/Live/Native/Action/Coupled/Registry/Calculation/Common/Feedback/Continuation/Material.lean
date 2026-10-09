import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Installed
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open CategoryTheory RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Q
namespace F
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (configuration installation material)
namespace E
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.Elimination
 (fourFaces dual_readback)
end E
end F
namespace FaceTransport
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (first second : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (same : first=second)
abbrev Root := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation.root frame
abbrev Visit := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation.visit frame

def move (face : SourceNativeRootSemanticFaceAt (Root frame first) (Visit frame first)) :
 SourceNativeRootSemanticFaceAt (Root frame second) (Visit frame second) := same ▸ face

theorem read_heq (face : SourceNativeRootSemanticFaceAt (Root frame first) (Visit frame first)) :
 HEq (move frame first second same face).rootRead face.rootRead := by
 cases same
 rfl
end FaceTransport
namespace Lower.Facets
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
local instance facetsGroup (n : Nat) (t : S) : AddCommGroup (Value W n t) := groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (nativeFirstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : nativeFirstCfg.LowVar=X)
abbrev firstCfg := F.configuration nativeFirstCfg
abbrev frameAt := Lower.frameAt initial (firstCfg nativeFirstCfg) language
def nativeCfgAt : (n : Nat) → A.Programme (PhysicalValue:=Value W n) (PhysicalVar:=X) (sort:=s)
 | 0 => nativeFirstCfg
 | n+1 => R.nativeProgramme (Lower.tailData initial (firstCfg nativeFirstCfg) language n).2
abbrev cfgAt (n : Nat) := F.configuration (nativeCfgAt initial nativeFirstCfg language n)

theorem cfg_source_faces (n : Nat) : Lower.cfgAt initial (firstCfg nativeFirstCfg) language n=cfgAt initial nativeFirstCfg language n := by
 cases n <;> rfl

def faceAt (n : Nat) : SourceNativeRootSemanticFaceAt
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation.root
  (frameAt initial nativeFirstCfg language n) (cfgAt initial nativeFirstCfg language n))
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation.visit
  (frameAt initial nativeFirstCfg language n) (cfgAt initial nativeFirstCfg language n)) := {
  projection:=(F.installation (frameAt initial nativeFirstCfg language n) (nativeCfgAt initial nativeFirstCfg language n)).embed PUnit.unit
  active:=PUnit.unit
  classifier_eq:=rfl }

theorem actual_material (n : Nat) : (faceAt initial nativeFirstCfg language n).rootRead=
 F.material (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt initial nativeFirstCfg language n))
 (nativeCfgAt initial nativeFirstCfg language n) (Q.actualOccurrence (frameAt initial nativeFirstCfg language n)) := rfl

def facesAt (n : Nat) := F.E.fourFaces
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt initial nativeFirstCfg language n))
 (nativeCfgAt initial nativeFirstCfg language n) (Q.actualOccurrence (frameAt initial nativeFirstCfg language n))
 ((faceAt initial nativeFirstCfg language n).rootRead)

def actualFaceAt (n : Nat) := FaceTransport.move (frameAt initial nativeFirstCfg language n)
 (cfgAt initial nativeFirstCfg language n) (Lower.cfgAt initial (firstCfg nativeFirstCfg) language n)
 (cfg_source_faces initial nativeFirstCfg language n).symm (faceAt initial nativeFirstCfg language n)

theorem actual_source_read (n : Nat) : HEq (actualFaceAt initial nativeFirstCfg language n).rootRead
 (F.material (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt initial nativeFirstCfg language n))
 (nativeCfgAt initial nativeFirstCfg language n) (Q.actualOccurrence (frameAt initial nativeFirstCfg language n))) :=
 (FaceTransport.read_heq _ _ _ _ _).trans (heq_of_eq (actual_material initial nativeFirstCfg language n))

theorem installed_dual (n : Nat) : type_of% (F.E.dual_readback
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt initial nativeFirstCfg language n))
 (nativeCfgAt initial nativeFirstCfg language n) (Q.actualOccurrence (frameAt initial nativeFirstCfg language n))
 ((faceAt initial nativeFirstCfg language n).rootRead)) := F.E.dual_readback _ _ _ _

theorem installed_boundary (n : Nat) :
 (SaturationMonoid.SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=s)
  (SaturationMonoid.SourceOperationEffects.mixedEnvironment (faceAt initial nativeFirstCfg language n).rootRead.2.1.raw.environment
   ((faceAt initial nativeFirstCfg language n).rootRead.2.1.nextRaw.environment-(faceAt initial nativeFirstCfg language n).rootRead.2.1.raw.environment))).comp
 (faceAt initial nativeFirstCfg language n).rootRead.2.2.2.2.2.2.2=0 :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.installed_boundary_equation
 (frameAt initial nativeFirstCfg language n) (nativeCfgAt initial nativeFirstCfg language n)

theorem packet_algebra (n : Nat) : (facesAt initial nativeFirstCfg language n).algebraFace.root.1=
 (faceAt initial nativeFirstCfg language n).rootRead := rfl
theorem packet_combinatorics (n : Nat) : (facesAt initial nativeFirstCfg language n).combinatorialFace.root.1=
 (faceAt initial nativeFirstCfg language n).rootRead := rfl
theorem packet_topology (n : Nat) : (facesAt initial nativeFirstCfg language n).topologicalFace.root.1=
 (faceAt initial nativeFirstCfg language n).rootRead := rfl
theorem packet_logic (n : Nat) : (facesAt initial nativeFirstCfg language n).logicalFace.root.1=
 (faceAt initial nativeFirstCfg language n).rootRead := rfl
end Lower.Facets
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
