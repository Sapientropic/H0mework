import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (atReceipt receipt)
end Complete
end Shared
namespace Past
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
 (stage exposure result written every_stage_born)
end Past
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace QS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock (nativeAdmissionEvent native_seed_query_receipt)
end QS
namespace Acted
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted (programme)
end Acted

section Prefix
variable {V X : Unit→Type} [∀ target,AddCommGroup (V target)]
variable (sourceSeed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X ())))
variable (sourceFrame : A.M.Frame (Value:=V) (Var:=X) (sort:=()))
variable (cfg : A.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=()))

private theorem receipt_epoch :
 A.epoch (Shared.Complete.atReceipt cfg sourceFrame 0)=A.epoch sourceFrame := by
 apply NativeSigma.Prefix.receipt_read cfg sourceFrame (fun stage=>A.epoch (Shared.frames sourceFrame cfg stage))
 intro stage paid actual
 have advance : Shared.frames sourceFrame cfg (stage+1)=(Shared.frames sourceFrame cfg stage).mathNext := by
  change Shared.next _ _ = _
  unfold Shared.next
  rw [actual]
 exact (congrArg A.epoch advance).trans rfl

/-- The full initial query history survives the actual calculation prefix up to its writer receipt. -/
theorem initial_query_receipt
 (event : PresentedRelationEventAt (Expr (PairValue V) X ()))
 (present : event∈(SourceOperationPaidRelations.exposure
  (J.queryResult sourceSeed (A.epoch sourceFrame) (S.actualOccurrence (A.epoch sourceFrame))).2.1.2).trace) :
 event∈(Past.written sourceSeed (Shared.Complete.atReceipt cfg sourceFrame 0)).trace := by
 apply Past.every_stage_born sourceSeed (Shared.Complete.atReceipt cfg sourceFrame 0) 0 (Nat.zero_le _)
 have identified : Past.stage (Shared.Complete.atReceipt cfg sourceFrame 0) 0=A.epoch sourceFrame :=
  receipt_epoch sourceFrame cfg
 unfold Past.exposure Past.result
 rw [identified]
 exact present
end Prefix

section InstalledCallback
local instance callbackGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (code : Expr (PairValue (PairValue C.Value)) C.Var ())
variable (packet : NativeSigma.NativePacket)
private abbrev callbackFactory := NativeSigma.Writeback.Input.withActualInput code
 (SF.defaultFactory (PairValue C.Value) C.Var ())

private theorem initial_query_born :
 let native:=AS.nativeAfterAdmission (callbackFactory code) packet
 let initial:=native.2.1.1
 let firstTrace:=SourceOperationPaidRelations.exposure
  (J.queryResult native.2.1.2 (A.epoch initial) (S.actualOccurrence (A.epoch initial))).2.1.2
 ∃ stock,(AS.bornAfterNative native).2.1.1.pairInventory=some stock ∧
  ∀ event∈firstTrace.trace,event∈stock.trace := by
 dsimp only
 let native:=AS.nativeAfterAdmission (callbackFactory code) packet
 let selected:=Shared.Complete.atReceipt (AS.stockCfg native.2.2.1) native.2.1.1 0
 obtain ⟨stock,writes,preserved⟩:=stock_installed native.1 native.2.2.1 native.2.1.2
  (native_after_admission_installed code packet) selected
 refine ⟨stock,writes,?_⟩
 intro event belongs
 exact preserved event
  (initial_query_receipt native.2.1.2 native.2.1.1 (AS.stockCfg native.2.2.1) event belongs)

private theorem born_pair_next_seed (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (stock : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value (PairValue C.Value) native.1)) C.Var ())))
 (written : (AS.bornAfterNative native).2.1.1.pairInventory=some stock) (event) (belongs : event∈stock.trace) :
 QS.nativeAdmissionEvent factory (AS.bornAfterNative native) event∈
 (AS.nativeAfterAdmission factory (AS.bornAfterNative native)).2.1.2.trace := by
 let born:=AS.bornAfterNative native
 let carried:=Stock.preserve born.2.1.1.pairInventory
  (Stock.preserve (native.2.2.1.nextPairInventory born.2.1.1) (AS.generatedPairStock born.2.1.1))
 apply QS.native_seed_query_receipt factory born carried rfl event
 change event∈(Stock.preserve (AS.bornAfterNative native).2.1.1.pairInventory _).trace
 rw [written]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event belongs

/-- The original initial query's entire paid trace crosses its real writer and next admission. -/
theorem initial_query_next_seed :
 let native:=AS.nativeAfterAdmission (callbackFactory code) packet
 let initial:=native.2.1.1
 ∀ event∈(SourceOperationPaidRelations.exposure
  (J.queryResult native.2.1.2 (A.epoch initial) (S.actualOccurrence (A.epoch initial))).2.1.2).trace,
 QS.nativeAdmissionEvent (callbackFactory code) (AS.bornAfterNative native) event∈
 (AS.nativeAfterAdmission (callbackFactory code) (AS.bornAfterNative native)).2.1.2.trace := by
 dsimp only
 obtain ⟨stock,written,all⟩:=initial_query_born code packet
 intro event belongs
 exact born_pair_next_seed (callbackFactory code) (AS.nativeAfterAdmission (callbackFactory code) packet)
  stock written event (all event belongs)
/-- The source constructor identifies the exact initial occurrence, before transporting its trace. -/
def QueryNextSeedAt : Prop :=
 let native:=AS.nativeAfterAdmission (callbackFactory code) packet
 ∀ event∈(SourceOperationPaidRelations.exposure
  (J.queryResult native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1)).2.1.2).trace,
 QS.nativeAdmissionEvent (callbackFactory code) (AS.bornAfterNative native) event∈
 (AS.nativeAfterAdmission (callbackFactory code) (AS.bornAfterNative native)).2.1.2.trace

theorem actual_query_next_seed : QueryNextSeedAt code packet := by
 unfold QueryNextSeedAt
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  exact initial_query_next_seed code ⟨grade,data,⟨C.Var,datum,inventory,pairInventory⟩,⟨rfl⟩⟩
end InstalledCallback

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- All paid events of the exact generated residual enter the actual following native seed. -/
theorem original_residual_next_seed : QueryNextSeedAt
 (FR.jointCode (RSource.code observation nontrivial half))
 (Next.bornPacket observation nontrivial half depth (ordinal+1)) :=
 actual_query_next_seed (FR.jointCode (RSource.code observation nontrivial half))
  (Next.bornPacket observation nontrivial half depth (ordinal+1))


end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
