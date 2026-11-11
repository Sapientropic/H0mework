import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMaterial.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMaterial
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid old_paid_value)
end WB
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
 (nativeValue native_value updated_total)
end Dyn
local instance originalNativeGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem actual_material_input :
 let packet:=D.packet observation nontrivial half depth ordinal
 let material:=R.actualMaterial packet.2.1.1 packet.2.2.1
 (N.input material).environment=material.environment := by
 dsimp only
 change (R.actualMaterial _ _).environment+(R.actualMaterial _ _).increment=(R.actualMaterial _ _).environment
 rw [actual_material_increment,add_zero]

theorem actual_native_value :
 let packet:=D.packet observation nontrivial half depth ordinal
 Dyn.nativeValue (D.factory observation nontrivial half) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down=0 := by
 let packet:=D.packet observation nontrivial half depth ordinal
 let material:=R.actualMaterial packet.2.1.1 packet.2.2.1
 have updated:=Dyn.updated_total (D.factory observation nontrivial half)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
 have sourceInput:=actual_material_input observation nontrivial half depth ordinal
 have value : material.raw.eval (N.input material).environment=WB.oldPaid packet.2.1.1 packet.2.2.1 :=
  (congrArg material.raw.eval sourceInput).trans (WB.old_paid_value packet.2.1.1 packet.2.2.1).symm
 exact add_left_cancel ((updated.trans value).trans (add_zero (WB.oldPaid packet.2.1.1 packet.2.2.1)).symm)

theorem actual_native_expression :
 let packet:=D.packet observation nontrivial half depth ordinal
 let material:=R.actualMaterial packet.2.1.1 packet.2.2.1
 (N.expression material).eval (N.input material).environment=0 :=
 (Dyn.native_value (D.factory observation nontrivial half)
  (D.packet observation nontrivial half depth ordinal).1
  (D.packet observation nontrivial half depth ordinal).2.1
  (D.packet observation nontrivial half depth ordinal).2.2.1
  (D.packet observation nontrivial half depth ordinal).2.2.2.down).symm.trans
   (actual_native_value observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMaterial
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
