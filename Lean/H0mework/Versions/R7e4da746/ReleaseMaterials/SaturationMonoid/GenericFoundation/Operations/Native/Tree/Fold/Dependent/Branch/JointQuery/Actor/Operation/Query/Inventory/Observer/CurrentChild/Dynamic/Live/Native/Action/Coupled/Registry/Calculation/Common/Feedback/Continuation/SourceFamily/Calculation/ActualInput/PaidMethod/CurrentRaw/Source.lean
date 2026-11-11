import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.Recovery
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Source
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyCurrentPaidRawInstallation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace H
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
 (factory methodBase completePairOutput actual_native_faces after_native_value after_native_whole_action actual_complete_query_written)
end H
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed Packet cfg runtime actual_receipt actual_whole actual_next)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch optionalSourceRoot)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw actualOccurrence)
end S
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence materialAt residualAt)
end C
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression updated_value residual_value relations)
end N
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (component stockLaw)
end I
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg nextBase nextSeed nextCfg)
end AS
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower (component combined configuration)
end Faces

section Frame
variable {Sorts : Type u} {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)] {s : Sorts}
variable (frame : M.Frame (Value := U) (Var := Y) (sort := s))

def currentRaw {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : C.Occurrence frame (current := current)) :
 SourceOperationInquiry.Context.Raw (PhysicalValue := U) (PhysicalVar := Y) (sort := s) :=
 let paid := (C.materialAt frame supplied).paid
 let request := N.input paid
 ⟨request.environment, request.expression⟩

theorem current_raw_source {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : C.Occurrence frame (current := current)) :
 (currentRaw frame supplied).environment = (N.input (C.materialAt frame supplied).paid).environment ∧
 (currentRaw frame supplied).expression = N.expression (C.materialAt frame supplied).paid := ⟨rfl,rfl⟩

abbrev Reader :=
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} →
 C.Occurrence frame (current := current) →
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue U) (Var := Y) (sort := s)

def component : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => SourceOperationInquiry.Context.Raw
  (PhysicalValue := U) (PhysicalVar := Y) (sort := s)
 project := fun _ {_current} supplied _ => currentRaw frame supplied

variable (base : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s))
def combined := ((A.optionalSourceRoot (S.base frame).root (base.datum frame).component).source.base.withProjectionCoface
 (component frame)).projectionLaw

def configuration : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s) :=
 { base with datum := fun sourceFrame => { base.datum sourceFrame with component := some (combined sourceFrame base) } }

-- The raw coordinate is installed before the original Faces and inventory query are emitted.
def installation :=
 ((SourceNativeProjectionLaw.InstallationAt.componentCoface
  (A.optionalSourceRoot (S.base (A.epoch frame)).root (base.datum (A.epoch frame)).component).source.base
  (component (A.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
   (S.base (A.epoch frame)).root.source.base (combined (A.epoch frame) base))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (A.optionalSourceRoot (S.base (A.epoch frame)).root ((configuration base).datum (A.epoch frame)).component).source.base
   (Faces.component (A.epoch frame) (configuration base))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   { (S.base (A.epoch frame)).root.source.base with projectionLaw := Faces.combined (A.epoch frame) (configuration base) }
   (I.stockLaw (A.epoch frame) (Faces.configuration (configuration base)))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
   (I.component (A.epoch frame) (Faces.configuration (configuration base)))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.baseRoot frame (AS.stockCfg (Faces.configuration (configuration base)))).source.base
   (S.queryLaw (A.epoch frame) (AS.stockCfg (Faces.configuration (configuration base))))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.queryRoot frame (AS.stockCfg (Faces.configuration (configuration base)))).source.base
   (S.resultLaw (A.epoch frame) (AS.stockCfg (Faces.configuration (configuration base))))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.resultRoot frame (AS.stockCfg (Faces.configuration (configuration base)))).source.base
   (S.consumerLaw (A.epoch frame) (AS.stockCfg (Faces.configuration (configuration base))))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.consumerRoot frame (AS.stockCfg (Faces.configuration (configuration base)))).source.base
   (S.compilationLaw (A.epoch frame) (AS.stockCfg (Faces.configuration (configuration base)))))

def rawFace : SourceNativeRootSemanticFaceAt
 (S.root frame (AS.stockCfg (Faces.configuration (configuration base))))
 (S.visit frame (AS.stockCfg (Faces.configuration (configuration base)))) where
 projection := (installation frame base).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

def rawRestriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue := U) (PhysicalVar := Y) (sort := s)
 (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered,
   ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt,
    (S.root frame (AS.stockCfg (Faces.configuration (configuration base)))).toAuthoritativeRoot,
    S.visit frame (AS.stockCfg (Faces.configuration (configuration base)))⟩⟩ : AnyAuthoritativeRootCurrent) where
 projection := (rawFace frame base).projection
 active := (rawFace frame base).active
 classifier_eq := (rawFace frame base).classifier_eq
 payload_eq := rfl

theorem installed_current_raw : SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.readRaw _
 (rawRestriction frame base) = currentRaw (A.epoch frame) (S.actualOccurrence frame) := rfl
end Frame

section Factory
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance familyGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (original : SF.Factory W X s)
def enrich : SF.Factory W X s :=
 { original with datum := fun n seed frame => (configuration (SF.cfg original n seed)).datum frame }

theorem preserves_source (n : Nat) (seed : SF.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 @Eq (Reader frame) ((enrich original).datum n seed frame).reader (original.datum n seed frame).reader ∧
 @Eq (Option (Reader frame)) ((enrich original).datum n seed frame).calculationReader (original.datum n seed frame).calculationReader ∧
 (enrich original).nextInventory = original.nextInventory ∧
 (enrich original).nextPairInventory = original.nextPairInventory ∧
 (enrich original).extraScalar = original.extraScalar ∧ (enrich original).extraPair = original.extraPair :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end Factory
end SourceFamilyCurrentPaidRawInstallation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
