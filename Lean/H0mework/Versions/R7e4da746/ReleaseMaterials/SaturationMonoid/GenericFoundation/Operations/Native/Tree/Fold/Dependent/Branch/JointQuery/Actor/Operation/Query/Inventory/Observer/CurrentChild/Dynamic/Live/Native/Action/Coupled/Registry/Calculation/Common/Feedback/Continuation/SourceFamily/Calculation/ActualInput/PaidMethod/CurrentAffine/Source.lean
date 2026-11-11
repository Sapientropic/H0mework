import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.CurrentRaw.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyCurrentAffineWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace K
export SourceFamilyCurrentPaidRawInstallation (currentRaw)
export SourceFamilyCurrentPaidRawInstallation.SF (Factory Seed cfg)
end K
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch optionalSourceRoot)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end S
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace C
export SourceOperationInquiry.Context.Installation (materialAt Occurrence)
end C
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input relations updated_value residual_value)
end N
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (boundary sourceOccurrence actualRelation history effectFaces paidCoordinate complex differential_effect actual_inverse native_zero_iff)
end F
namespace P
export SourceOperationPaidRelations (exposure prefixHistory)
end P
namespace Feed
export SourceInventoryExecutionFeed (written relationSpace relation_span_affine_written history_relation_space original_preserved complete_source_cost)
end Feed
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace L
export SourceFamilyCurrentPaidRawInstallation.L (Value groups)
end L

section Frame
variable {Sorts : Type u} {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)] {s : Sorts}
variable (frame : M.Frame (Value := U) (Var := Y) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : C.Occurrence frame (current := current))

abbrev paid := (C.materialAt frame supplied).paid
abbrev updatedEnvironment := (N.input (paid frame supplied)).environment
abbrev beta := F.boundary (paid frame supplied)
abbrev nu : U s →₀ ℤ := valueMap (R := ℤ) (updatedEnvironment frame supplied) (beta frame supplied)
def gamma := beta frame supplied - constantMap (R := ℤ) (nu frame supplied)
def certificate := normalizationCertificate (R := ℤ) (updatedEnvironment frame supplied) (beta frame supplied)
def sourceTrace := (paid frame supplied).state.2
def sourceInventory := P.exposure (sourceTrace frame supplied)
def written := Feed.written (updatedEnvironment frame supplied) (sourceInventory frame supplied)

theorem affine_certificate : relationMap (R := ℤ) (updatedEnvironment frame supplied)
 (certificate frame supplied) = gamma frame supplied :=
 source_reduction (updatedEnvironment frame supplied) (beta frame supplied)

theorem free_value_read : ScalarRelationPresentation.freeEvaluation (R := ℤ) (U s) (nu frame supplied) =
 (K.currentRaw frame supplied).expression.eval (K.currentRaw frame supplied).environment :=
 (LinearMap.congr_fun (valueMap_evaluation (R := ℤ) (updatedEnvironment frame supplied)) (beta frame supplied)).trans
 (N.residual_value (R := ℤ) (paid frame supplied))

theorem differential_read : (F.effectFaces (paid frame supplied)).embedding
 ((F.effectFaces (paid frame supplied)).canonical
  (((F.complex (paid frame supplied)).d 0 1).hom (F.actualRelation (paid frame supplied))).val) =
 (K.currentRaw frame supplied).expression.eval (K.currentRaw frame supplied).environment :=
 (F.differential_effect (paid frame supplied)).trans (N.updated_value (R := ℤ) (paid frame supplied)).symm

theorem gamma_written : gamma frame supplied ∈ Feed.relationSpace (written frame supplied) := by
 have original := (F.actualRelation (paid frame supplied)).property
 change beta frame supplied ∈ (P.prefixHistory (F.sourceOccurrence (paid frame supplied))
  (sourceInventory frame supplied)).relationClosure at original
 rw [Feed.history_relation_space] at original
 exact Feed.relation_span_affine_written (updatedEnvironment frame supplied) (sourceInventory frame supplied)
  (beta frame supplied) original

-- The free value word and every paid/source execution remain separate retained coordinates.
def material := (paid frame supplied,updatedEnvironment frame supplied,beta frame supplied,nu frame supplied,
 gamma frame supplied,certificate frame supplied,sourceTrace frame supplied,written frame supplied)

def component : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} actual _ => type_of% (material frame actual)
 project := fun _ {_current} actual _ => material frame actual

variable (base : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s))
def combined := ((A.optionalSourceRoot (S.base frame).root (base.datum frame).component).source.base.withProjectionCoface
 (component frame)).projectionLaw

def configuration : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s) :=
 { base with datum := fun sourceFrame => { base.datum sourceFrame with component := some (combined sourceFrame base) } }
end Frame

section Factory
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance familyGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (original : K.Factory W X s)

def callback (n : Nat) (seed : K.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :=
 Stock.preserve (original.nextInventory n seed frame)
  (written (A.epoch frame) (S.actualOccurrence frame))

def enrich : K.Factory W X s :=
 { original with
   datum := fun n seed frame => (configuration (K.cfg original n seed)).datum frame
   nextInventory := fun n seed frame => some (callback original n seed frame) }

theorem callback_keeps_trace (n : Nat) (seed : K.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 ∀ event ∈ (written (A.epoch frame) (S.actualOccurrence frame)).trace,
 event ∈ (callback original n seed frame).trace := by
 unfold callback Stock.preserve
 cases original.nextInventory n seed frame with
 | none => exact fun _ present => present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1
end Factory
end SourceFamilyCurrentAffineWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
