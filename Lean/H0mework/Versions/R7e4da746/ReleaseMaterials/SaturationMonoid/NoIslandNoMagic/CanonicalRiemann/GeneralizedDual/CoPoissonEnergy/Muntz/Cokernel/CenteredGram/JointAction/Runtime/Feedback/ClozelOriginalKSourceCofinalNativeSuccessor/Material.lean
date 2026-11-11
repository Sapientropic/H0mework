import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Installed
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Outgoing.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
 (raw withCalculation action_reader source_callbacks reader_source)
end CF
namespace CM
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory reader query_factory_transport)
end CM
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (nextCfg stockCfg stock_action_reader next_action_reader template)
end AS
namespace Native
export ActualCofinalSourceAction (nativePacket selected receipt sourceBorn packetTransport born_transport)
end Native
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance materialFamilyGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

private theorem calculation_language {Y Z : Unit→Type} (same : Y=Z)
 (mother : SF.Factory W Z ()) (code : Expr (PairValue W) Z ()) :
 (same.symm ▸ CF.withCalculation mother code : SF.Factory W Y ())=
 CF.withCalculation (same.symm ▸ mother) (same.symm ▸ code) := by cases same; rfl

/-- The literal code replaces only expression; the original common-material environment remains the same actual source. -/
theorem source_next_material_environment
 (frame : M.Frame (Value:=L.Value W (packet.1+1)) (Var:=packet.2.2.1.LowVar) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 (R.actionReader frame (AS.stockCfg (Native.nativePacket (Prior.sourceCofinalFactory literalCode factory) packet).2.2.1) supplied).environment=
 (CM.reader (A.epoch frame) supplied).environment := by
 refine (congrArg (fun raw=>raw.environment)
  (AS.next_action_reader (Prior.sourceCofinalFactory literalCode factory) packet.1 packet.2.1
    packet.2.2.1 packet.2.2.2.down frame supplied)).trans ?_
 unfold AS.template Prior.sourceCofinalFactory
 rw [calculation_language packet.2.2.2.down,CM.query_factory_transport packet.2.2.2.down]
 rfl

/-- The real source native cfg carries the complete before/action environment; no old raw-state identity is assumed. -/
theorem source_native_full_material
 (frame : M.Frame (Value:=L.Value W (packet.1+1)) (Var:=packet.2.2.1.LowVar) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 (R.actionReader frame (AS.stockCfg (Native.nativePacket (Prior.sourceCofinalFactory literalCode factory) packet).2.2.1) supplied).environment=
 pairEnvironment (I.rawAt (A.epoch frame) supplied).environment
 ((I.nextRawAt (A.epoch frame) supplied).environment-(I.rawAt (A.epoch frame) supplied).environment) :=
 source_next_material_environment _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
