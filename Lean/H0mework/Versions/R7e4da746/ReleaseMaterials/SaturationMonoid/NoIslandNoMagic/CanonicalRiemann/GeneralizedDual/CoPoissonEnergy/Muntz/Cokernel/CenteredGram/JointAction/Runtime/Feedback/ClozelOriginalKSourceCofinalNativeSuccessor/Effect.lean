import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Receipt
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (cofinal_source_code HasSourceCode)
end CF
namespace Native
export ActualCofinalSourceAction (environmentTransport)
end Native
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance effectFamilyGroups (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
variable (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
variable (language : cfg.LowVar=X)

/-- This is the original admission in the existing runtime. Its cfg is retained intact. -/
def cofinalSourcePacket (ordinal : Nat) := D.packetAt (Prior.sourceCofinalFactory literalCode factory)
 initial cfg language (ordinal+1)

def cofinalSourceNativeTotal (ordinal : Nat) :=
 let packet:=cofinalSourcePacket literalCode factory initial cfg language ordinal
 WB.oldPaid packet.2.1.1 packet.2.2.1+
 Native.nativeValue (Prior.sourceCofinalFactory literalCode factory) packet

def cofinalSourceInput (ordinal : Nat) :=
 let packet:=cofinalSourcePacket literalCode factory initial cfg language ordinal
 Native.environmentTransport packet.2.2.2.down
  (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment

/-- Real code lineage, material and receipt generate this actual update; no target code equation enters a constructor. -/
theorem cofinal_source_native_total_code (ordinal : Nat) :
 let packet:=cofinalSourcePacket literalCode factory initial cfg language ordinal
 cofinalSourceNativeTotal literalCode factory initial cfg language ordinal=
 (packet.2.2.2.down.symm ▸ CF.codeAt literalCode packet.1 : Expr (PairValue (L.Value W packet.1)) packet.2.2.1.LowVar ()).eval
  (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment := by
 dsimp only [cofinalSourceNativeTotal]
 have generated:=CF.cofinal_source_code (CM.queryFactory factory) literalCode initial cfg language ordinal
 have code:=(generated (cofinalSourcePacket literalCode factory initial cfg language ordinal).2.1.1
   (S.actualOccurrence (cofinalSourcePacket literalCode factory initial cfg language ordinal).2.1.1))
 exact (source_actual_native_total (Prior.sourceCofinalFactory literalCode factory) _).trans
  (congrArg (fun expression=>expression.eval
   (N.input (R.actualMaterial (cofinalSourcePacket literalCode factory initial cfg language ordinal).2.1.1
    (cofinalSourcePacket literalCode factory initial cfg language ordinal).2.2.1)).environment) code)

private theorem code_language_value {Y Z : Unit→Type} (same : Y=Z)
 (code : Expr (PairValue W) Z ()) (n : Nat)
 (environment : Env (PairValue (L.Value W n)) Y) :
 CF.collapseValue n ((same.symm ▸ CF.codeAt code n : Expr (PairValue (L.Value W n)) Y ()).eval environment)=
 code.eval (fun target name=>CF.collapseValue n (Native.environmentTransport same environment target name)) := by
 cases same
 exact CF.code_base_value code n environment

/-- Collapse is taken through the same actual graded carrier and receiver language. -/
theorem cofinal_source_native_total_base (ordinal : Nat) :
 let packet:=cofinalSourcePacket literalCode factory initial cfg language ordinal
 CF.collapseValue packet.1 (cofinalSourceNativeTotal literalCode factory initial cfg language ordinal)=
 literalCode.eval (fun target name=>CF.collapseValue packet.1
  (cofinalSourceInput literalCode factory initial cfg language ordinal target name)) := by
 dsimp only
 rw [cofinal_source_native_total_code]
 exact code_language_value _ _ _ _

/-- Each source write is fed by this real packet's complete source total. -/
theorem cofinal_source_born_write (ordinal : Nat) :
 let packet:=cofinalSourcePacket literalCode factory initial cfg language ordinal
 (Native.sourceBorn (Prior.sourceCofinalFactory literalCode factory) packet).2.1.1.activeEnvironment=
 AS.write (Prior.sourceCofinalFactory literalCode factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
 (cofinalSourceNativeTotal literalCode factory initial cfg language ordinal) :=
 Native.born_environment _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
