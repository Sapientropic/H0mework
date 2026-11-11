import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Material
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (HasSourceCode native_after_admission_code born_after_native_code)
end CF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (AdmissionPacket bornAfterNative stockCfg)
end AS
namespace D
export ActualCofinalSourceAction.D (packetAt packetAt_successor)
end D
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance cofinalGroups (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
variable (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
variable (language : cfg.LowVar=X)

/-- A reader-environment invariant on the original programme, without replacing its cfg. -/
def HasFullCurrentEnvironment (grade : Nat)
 (programme : A.Programme (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()))
 (sameVar : programme.LowVar=X) : Prop :=
 ∀ (frame : M.Frame (Value:=L.Value W grade) (Var:=X) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)),
 (R.actionReader frame (AS.stockCfg programme) supplied).environment=
 (sameVar.symm ▸ (CM.reader (A.epoch frame) supplied).environment : Env (PairValue (L.Value W grade)) programme.LowVar)

/-- The actual native template generates the full current-material reader on the receiver language. -/
theorem source_native_current_environment
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 HasFullCurrentEnvironment
  (W:=W) (X:=packet.2.2.1.LowVar) (packet.1+1)
  (Native.nativePacket (Prior.sourceCofinalFactory literalCode factory) packet).2.2.1 rfl := by
 intro frame current supplied
 exact source_next_material_environment literalCode factory packet frame supplied

/-- The original born stock cfg consumes that same environment invariant. -/
theorem source_born_current_environment
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (generated : HasFullCurrentEnvironment (W:=W) packet.1 packet.2.2.1 packet.2.2.2.down) :
 HasFullCurrentEnvironment (W:=W) (AS.bornAfterNative packet).1
 (AS.bornAfterNative packet).2.2.1 (AS.bornAfterNative packet).2.2.2.down := by
 intro frame current supplied
 exact (congrArg (fun raw=>raw.environment) (AS.stock_action_reader frame
  (AS.stockCfg packet.2.2.1) supplied)).trans (generated frame supplied)

/-- Each original runtime admission inherits the actual native reader; no cfg is covered over by a new source packet. -/
theorem source_cofinal_current_environment (ordinal : Nat) :
 let packet:=D.packetAt (Prior.sourceCofinalFactory literalCode factory) initial cfg language (ordinal+1)
 HasFullCurrentEnvironment (W:=W) packet.1 packet.2.2.1 packet.2.2.2.down := by
 dsimp only
 rw [D.packetAt_successor]
 generalize previousEq : D.packetAt (Prior.sourceCofinalFactory literalCode factory) initial cfg language ordinal=previous
 rcases previous with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  exact source_born_current_environment
   (Native.nativePacket (Prior.sourceCofinalFactory literalCode factory)
    ⟨grade,data,⟨X,datum,inventory,pairInventory⟩,⟨rfl⟩⟩)
   (source_native_current_environment literalCode factory _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
